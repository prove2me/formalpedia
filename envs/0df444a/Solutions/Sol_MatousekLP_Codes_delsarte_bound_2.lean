-- Prove2me | solution 2 for MatousekLP.Codes.delsarte_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:04.832931+00:00
-- url     : https://prove2.me/submissions/961634c5-95bc-4cd3-af7b-ffdaf68b2c55

import Mathlib
import Definitions.Def_MatousekLP_Codes_DelsarteLP
import Theorems.Thm_MatousekLP_Codes_xtilde_feasible

-- carved verbatim out of submission b0e8d01b-14cb-4b17-9a88-431770787709, lines 178-206

section
open Finset Polynomial MatousekLP.Codes

open Finset MatousekLP.Codes in
theorem solution (n d : ℕ) (v : ℝ)
    (hv : ∀ x : Fin (n + 1) → ℝ, IsDelsarteFeasible n d x → delsarteObjective x ≤ v) :
    (A n d : ℝ) ≤ v := by
  classical
  -- the point e₀ is feasible with objective 1, so v ≥ 1
  set e0 : Fin (n + 1) → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0
  have hK0 : ∀ t, K n t 0 = (n.choose t : ℤ) := by intro t; simp [K]
  have he0 : IsDelsarteFeasible n d e0 := by
    refine ⟨by simp [e0], fun i hi1 _ => by simp only [e0]; rw [if_neg (by omega)], fun t _ _ => ?_, fun i => by
      simp only [e0]; split_ifs <;> norm_num⟩
    rw [Finset.sum_eq_single (0 : Fin (n + 1)) (fun i _ hi => by
      simp [e0, Fin.val_eq_zero_iff, hi]) (by simp)]
    simp [e0, hK0]
  have hv1 : 1 ≤ v := by
    have := hv e0 he0
    simp only [delsarteObjective] at this
    rwa [Finset.sum_eq_single (0 : Fin (n + 1)) (fun i _ hi => by simp [e0, Fin.val_eq_zero_iff, hi])
      (by simp), show e0 0 = 1 by simp [e0]] at this
  -- an optimal code
  set F := (Finset.univ : Finset (Finset (Word n))).filter (fun C => HasDistance C d)
  have hF : F.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw => absurd hw (Finset.notMem_empty w)⟩⟩
  obtain ⟨C, hCF, hCmax⟩ := Finset.exists_mem_eq_sup F hF Finset.card
  have hA : A n d = C.card := by unfold A; exact hCmax
  rw [hA]
  rcases C.eq_empty_or_nonempty with h | h
  · simp [h]; linarith
  · obtain ⟨hobj, hfeas⟩ := MatousekLP.Codes.xtilde_feasible C h (Finset.mem_filter.mp hCF).2
    rw [← hobj]; exact hv _ hfeas

end
