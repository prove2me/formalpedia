-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.span_hq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:37.363454+00:00
-- url     : https://prove2.me/submissions/e632d4cc-f314-422c-9074-7420452a995d

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_add
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_pr_val
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_pr_pr
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_hq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_mask_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_mask_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_mask
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_swap
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_scalar
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_up_pr
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_blk_pr
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuSpan
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuSpan
theorem _root_.solution (hk : 1 ≤ k) {Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hY : Lie (Hq k r) Y) :
    ∃ B A C : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Lie (Hq k r) B ∧ Lie (Hq k r) A ∧ Lie (Hq k r) C ∧ (∀ i j, ¬ blk k r i j → B i j = 0) ∧
      (∀ i, B i (wI k r 0) = B i (wI k r (Fin.last k))) ∧
      (∀ i j, ¬ (up k r i j ∧ ¬ blk k r i j) → A i j = 0) ∧ (∀ i j, up k r i j → C i j = 0) ∧ Y = B + A + C := by
  have p0 : pr k r (wI k r 0) = wI k r (Fin.last k) := by
    apply Fin.ext; simp [pr_val, wI]; omega
  have p1 : pr k r (wI k r (Fin.last k)) = wI k r 0 := by rw [← p0, pr_pr]
  set a := Y (wI k r 0) (wI k r (Fin.last k)) with ha
  have ha' : star a + a = 0 := by
    have := (lie_hq_iff Y).1 hY (wI k r (Fin.last k)) (wI k r (Fin.last k))
    rwa [p1] at this
  set U := mask (up k r) Y with hU
  have lU : Lie (Hq k r) U := lie_mask up_pr hY
  set B := mask (blk k r) (U + U.submatrix (pr k r) (pr k r) + a • 1) with hB
  have lB : Lie (Hq k r) B :=
    lie_mask (fun i j => (blk_pr i j).1) (lie_add (lie_add lU (lie_swap lU)) (lie_scalar ha'))
  set A := mask (fun i j => up k r i j ∧ ¬ blk k r i j) Y with hA
  have lA : Lie (Hq k r) A :=
    lie_mask (fun i j h => ⟨up_pr i j h.1, fun h' => h.2 ((blk_pr i j).2 h')⟩) hY
  refine ⟨B, A, Y - B - A, lB, lA, lie_sub (lie_sub hY lB) lA, fun i j h => mask_neg h, fun i => ?_,
    fun i j h => mask_neg h, fun i j h => ?_, by abel⟩
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have b0 : blk k r i (wI k r 0) := ⟨hi, by simp [wI]⟩
      have b1 : blk k r i (wI k r (Fin.last k)) := ⟨hi, by simp [wI]⟩
      have u0 : ∀ l : Fin (2 * r + k + 1), r ≤ l.val → U l (wI k r 0) = 0 := fun l hl =>
        mask_neg (by simp only [up, wI, Fin.lt_def, Fin.val_zero]; omega)
      have hpi : r ≤ (pr k r i).val := by rw [pr_val]; split_ifs <;> omega
      have ud : U (wI k r (Fin.last k)) (wI k r (Fin.last k)) = 0 := mask_neg (by simp [up])
      have ua : U (wI k r 0) (wI k r (Fin.last k)) = a :=
        mask_pos (by simp only [up, outer, wI, Fin.lt_def, Fin.val_zero, Fin.val_last]; omega)
      have hne : wI k r 0 ≠ wI k r (Fin.last k) := by
        simp only [wI, Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
      rw [hB, mask_pos b0, mask_pos b1]
      simp only [Matrix.add_apply, submatrix_apply, p0, p1, u0 i hi.1, u0 _ hpi, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      by_cases h0 : i = wI k r 0
      · rw [h0, p0, ud, ua]; simp [hne]
      · by_cases h1 : i = wI k r (Fin.last k)
        · rw [h1, p1, ud, ua]; simp [hne.symm]
        · have : pr k r i = i := by
            apply Fin.ext
            simp only [wI, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h0 h1
            rw [pr_val, if_neg (by omega)]
          rw [this]; simp [h0, h1]
    · rw [hB, mask_neg (fun h => hi h.1), mask_neg (fun h => hi h.1)]
  · rw [Matrix.sub_apply, Matrix.sub_apply]
    by_cases hb : blk k r i j
    · have h2 : ¬ up k r (pr k r i) (pr k r j) := by
        simp only [up, blk, outer, Fin.lt_def, pr_val] at *
        split_ifs at * <;> omega
      rw [hA, mask_neg (fun h' => h'.2 hb), hB, mask_pos hb]
      simp only [Matrix.add_apply, submatrix_apply, Matrix.smul_apply, hU, mask_pos h, mask_neg h2,
        Matrix.one_apply_ne (ne_of_lt h.1)]
      simp
    · rw [hA, mask_pos ⟨h, hb⟩, hB, mask_neg hb]; simp
end GlobalTheory.CompanionTheory.BmuSpan
