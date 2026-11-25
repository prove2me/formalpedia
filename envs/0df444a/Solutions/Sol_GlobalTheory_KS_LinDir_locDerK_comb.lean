-- Prove2me | solution 1 for GlobalTheory.KS.LinDir.locDerK_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:35.369516+00:00
-- url     : https://prove2.me/submissions/7bb2de88-a0ac-4d2f-92a7-364c539b427a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KsCocLinear
import Theorems.Thm_GlobalTheory_KS_LinDir_constFn_lin
import Theorems.Thm_GlobalTheory_KS_IsCob_add
import Theorems.Thm_GlobalTheory_KS_rsT_constFn
import Theorems.Thm_GlobalTheory_KS_rsT_mul
import Theorems.Thm_GlobalTheory_KS_rsT_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.LinDir
namespace GlobalTheory.KS.LinDir
theorem _root_.solution {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W hW, h'.add W hW, h''.add W hW]; ring
  mul W hW f f' := by
    rw [h.mul W hW, h'.mul W hW, h''.mul W hW]; ring
  res W W' l hW f := by
    rw [h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul,
      rsT_constFn q (m.preimage_mono l)]
  base W hW r := by
    rw [h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]
end GlobalTheory.KS.LinDir
