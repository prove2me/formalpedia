-- Prove2me | solution 1 for GlobalTheory.DetClass.mat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:24.397776+00:00
-- url     : https://prove2.me/submissions/77eb4883-6760-4268-a60f-a0fae4502790

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DetClass
theorem _root_.solution {I J : ι → Ideal R} (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩) * mat φ.toLinearMap (fun i => ⟨c, hI i⟩)
      = Matrix.diagonal fun _ => c * c := by
  ext j k
  simp only [Matrix.mul_apply, mat, Matrix.diagonal_apply, LinearEquiv.coe_coe]
  set v := φ (Pi.single k ⟨c, hI k⟩) with hv
  have hsw : ∀ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l)
      = c • (Pi.single i (v i) : (l : ι) → J l) := by
    intro i
    funext l
    by_cases hl : l = i
    · subst hl
      apply Subtype.ext
      simp [mul_comm]
    · simp [Pi.single_eq_of_ne hl]
  have hsum : ∑ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l) = c • v := by
    simp_rw [hsw, ← Finset.smul_sum, Finset.univ_sum_single]
  have h := congrArg (fun x => ((φ.symm x) j : R)) hsum
  simp only [map_sum, map_smul, hv, LinearEquiv.symm_apply_apply, Finset.sum_apply,
    Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] at h
  simp_rw [mul_comm _ ((v _ : J _) : R)]
  rw [h]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk]
end GlobalTheory.DetClass
