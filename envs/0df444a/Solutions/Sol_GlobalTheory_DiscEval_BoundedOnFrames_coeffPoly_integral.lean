-- Prove2me | solution 1 for GlobalTheory.DiscEval.BoundedOnFrames.coeffPoly_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:18.029379+00:00
-- url     : https://prove2.me/submissions/ec56459d-7955-40fb-b493-27ace303e360

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_norm_coeff_detProdPoly_le
import Theorems.Thm_GlobalTheory_DiscEval_exists_norm_coeff_detProdPoly
import Theorems.Thm_GlobalTheory_DiscEval_coeffPoly_integral_of_admissible
import Theorems.Thm_GlobalTheory_DiscEval_residueFieldInfiniteOn_algField
import Theorems.Thm_GlobalTheory_DiscEval_algDisc_dense
import Theorems.Thm_GlobalTheory_DiscEval_mul_mem_algDisc
import Theorems.Thm_GlobalTheory_DiscEval_isUnit_algInt_iff
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_eval_detProdPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}
namespace GlobalTheory.DiscEval
namespace BoundedOnFrames
theorem _root_.solution (hF : BoundedOnFrames i hi hπ F) (m : ℤ) :
    (∀ μ, ‖coeff μ (coeffPoly m (map (laurent π A i hπ) F))‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by
  refine coeffPoly_integral_of_admissible (algField p) (residueFieldInfiniteOn_algField p)
    (algDisc p) (fun _ ht => ht.2) (algDisc_dense p) (mul_mem_algDisc p) i hi hπ
    (detProdPoly ℂ_[p] n) (norm_coeff_detProdPoly_le n) (exists_norm_coeff_detProdPoly n) F
    (fun t htS ht0 ht x hx hxδ => ?_) m
  let y : EntryIndex n n → algInt p := fun k => ⟨x k, hx k⟩
  have h1 : IsUnit (∏ s, (ofEntries y s).det) := by
    rw [isUnit_algInt_iff, ← hxδ, eval_detProdPoly, ← Subring.coe_subtype, map_prod]
    simp only [RingHom.map_det]
    rfl
  rw [IsUnit.prod_univ_iff] at h1
  exact hF t htS.1 ht0 ht fun s => ((Matrix.isUnit_iff_isUnit_det _).2 (h1 s)).unit
end BoundedOnFrames
end GlobalTheory.DiscEval
