-- Prove2me | solution 1 for GlobalTheory.SatakeBound.exists_hermMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:05.51303+00:00
-- url     : https://prove2.me/submissions/a9fd8239-8ca1-4ea9-918b-24166435d21c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_hermMat_lt
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_hermite_reduction_unipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {R : Type} [CommRing R] {n : ℕ}
variable {p : R} {a a' : Fin n → ℕ}
variable [IsDomain R]
namespace GlobalTheory.SatakeBound
theorem _root_.solution [IsDiscreteValuationRing R] (hp : Irreducible p) (b : Matrix (Fin n) (Fin n) R)
    (hb : ∀ i j, j < i → b i j = 0) (h0 : ∀ i, b i i ≠ 0) :
    ∃ (a : Fin n → ℕ) (c : HermIdx p a) (W : GL (Fin n) R), hermMat p a c = b * W := by
  choose a u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (h0 i) hp
  let b' := b * Matrix.diagonal fun i => (((u i)⁻¹ : Rˣ) : R)
  have h1 : ∀ i j, j < i → b' i j = 0 := fun i j h => by simp [b', hb i j h]
  have h2 : ∀ i, b' i i = p ^ a i := fun i => by
    simp only [b', Matrix.mul_diagonal]
    rw [hu i, mul_comm, Units.inv_mul_cancel_left]
  obtain ⟨U, hU, hU1, hr⟩ := GlobalTheory.hermite_reduction_unipotent R n b' (fun i y => (Ideal.Quotient.mk (Ideal.span {p ^ a i}) y).out) h1
    fun i y => by
      rw [h2, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      simp
  have hunit : IsUnit ((Matrix.diagonal fun i => (((u i)⁻¹ : Rˣ) : R)) * U) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_of_isUpperTriangular (M := U) fun _ _ h => hU _ _ h,
      Matrix.det_diagonal]
    simp [hU1, IsUnit.prod_iff]
  refine ⟨a, fun i j => Ideal.Quotient.mk _ ((b' * U) i j), hunit.unit, ?_⟩
  rw [hunit.unit_spec, ← mul_assoc]
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · obtain ⟨y, hy⟩ := hr i j h
    rw [hermMat_lt _ h]
    show (Ideal.Quotient.mk _ ((b' * U) i j)).out = (b' * U) i j
    rw [hy]
    simp
  · rw [hermMat_diag, Matrix.mul_apply, Finset.sum_eq_single i (fun s _ hs => ?_) (by simp), hU1, mul_one, ← h2]
    rcases lt_or_gt_of_ne hs with h | h
    · exact mul_eq_zero_of_left (h1 _ _ h) _
    · rw [hU _ _ h, mul_zero]
  · rw [hermMat_gt _ h]
    exact (Matrix.BlockTriangular.mul (b := id) (fun _ _ h => h1 _ _ h) (fun _ _ h => hU _ _ h) h).symm
end GlobalTheory.SatakeBound
