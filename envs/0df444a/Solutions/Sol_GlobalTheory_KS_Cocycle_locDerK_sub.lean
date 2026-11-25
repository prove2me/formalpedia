-- Prove2me | solution 1 for GlobalTheory.KS.Cocycle.locDerK_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:25.787651+00:00
-- url     : https://prove2.me/submissions/d6d97b21-1a20-463f-b181-18d89d783815

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnZero
import Theorems.Thm_GlobalTheory_KS_Cocycle_rsT_sub
import Theorems.Thm_P2M_GlobalTheory_KS_Cocycle_constFn_zero__d707fc2ffe6e
import Theorems.Thm_GlobalTheory_KS_IsCob_add
import Theorems.Thm_GlobalTheory_KS_rsT_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Cocycle
namespace GlobalTheory.KS.Cocycle
theorem _root_.solution {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) where
  add W hW f f' := by
    rw [h₁.add W (hW.trans l₁), h₂.add W (hW.trans l₂)]; ring
  mul W hW f f' := by
    rw [h₁.mul W (hW.trans l₁), h₂.mul W (hW.trans l₂)]; ring
  res W W' h hW f := by
    rw [h₁.res W W' h (hW.trans l₁), h₂.res W W' h (hW.trans l₂), rsT_sub (m.preimage_mono h)]
  base W hW r := by
    rw [h₁.base W (hW.trans l₁), h₂.base W (hW.trans l₂), sub_self, constFn_zero']
end GlobalTheory.KS.Cocycle
