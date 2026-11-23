-- Prove2me | solution 1 for GlobalTheory.LocDerExtK.locDerK_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:02.47178+00:00
-- url     : https://prove2.me/submissions/50407a70-e19e-4b9e-9b45-f6dda55c3ea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
import Theorems.Thm_GlobalTheory_LocDerExtK_rsT_eq
import Theorems.Thm_GlobalTheory_LocDerExt_der_unique
import Theorems.Thm_GlobalTheory_LocDerExt_sep


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
open GlobalTheory GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt
namespace GlobalTheory.LocDerExtK
theorem _root_.solution {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ : X.Opens} (hW : IsAffineOpen W₀)
    (d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (h : LocDerK q p m D W₀ d)
    (h' : LocDerK q p m D W₀ d') (e : d W₀ = d' W₀) (W : X.Opens) (hle : W ≤ W₀) : d W = d' W := by
  funext s
  refine sep m hW hle _ _ (fun f k => ?_)
  rw [← rsT_eq (pre_le m k), ← rsT_eq (pre_le m k), ← h.res W _ k hle, ← h'.res W _ k hle]
  haveI := hW.isLocalization_basicOpen f
  refine der_unique f (m.app (X.basicOpen f)).hom (d _) (d' _) (h.mul _ (X.basicOpen_le f))
    (h'.mul _ (X.basicOpen_le f)) (fun a => ?_) _
  change d _ (resG X (X.basicOpen_le f) a) = d' _ (resG X (X.basicOpen_le f) a)
  rw [h.res W₀ _ _ le_rfl, h'.res W₀ _ _ le_rfl, e]
end GlobalTheory.LocDerExtK
