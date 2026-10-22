-- Prove2me | solution 1 for HolisticService.Effort.proposition_3_own
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:45:43.831847+00:00
-- url     : https://prove2.me/submissions/2559061d-e108-46ac-ab52-77dfc9fa8af5

import Mathlib
import Definitions.Def_HolisticService_Effort_Model
import Theorems.Thm_HolisticService_Effort_partials_own
import Theorems.Thm_HolisticService_Effort_proposition_1

open HolisticService.Effort

theorem solution {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i : Fin n) :
    deriv (fun t => optEffort (withC M i t) i) (M.c i) < 0 ∧
      0 < deriv (fun t => optEffort (withVH M i t) i) (M.VH i) ∧
      (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) i) (M.sH i)) ∧
      (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) i) (M.sH i) < 0) := by
  have hS' := hS
  obtain ⟨hV, -, -, -, hcS, -, hr, -, hne, -, -, -, hP⟩ := hS'
  have hd : ∀ k, M.sH k - M.sL k ≠ 0 := fun k => sub_ne_zero.mpr (hne k)
  obtain ⟨hc, hcneg, hv, hvpos, hA, hδeq, hsh⟩ := partials_own M hS hβ hI i
  have hex : ∃ δ, IsOptimalEffort M δ := ⟨δhat M, _, (proposition_1 M hS hI).1⟩
  have hδ0 : 0 ≤ optEffort M i := by
    unfold optEffort
    rw [dif_pos hex]
    obtain ⟨π, hπ⟩ := Classical.choose_spec hex
    exact (hπ.1.1 i).1
  have hdi := hd i
  refine ⟨by rw [hc.deriv]; exact hcneg, by rw [hv.deriv]; exact hvpos, ?_, ?_⟩
  · intro hneg
    rw [hsh.deriv]
    generalize M.sH i - M.sL i = d at *
    have hX : 2 * ((1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i)
        + (∑ j ∈ Finset.univ.erase i,
            (1 - M.c j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ j i - M.sL i) * d
        = (1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i + d ^ 2 * optEffort M i := by
      rw [hδeq]; field_simp; ring
    rw [hX]
    have h3 : d ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) h3
  · intro hpos
    rw [hsh.deriv]
    generalize M.sH i - M.sL i = d at *
    have hX : 2 * ((1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i)
        + (∑ j ∈ Finset.univ.erase i,
            (1 - M.c j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ j i - M.sL i) * d
        = (1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i + d ^ 2 * optEffort M i := by
      rw [hδeq]; field_simp; ring
    rw [hX]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)
