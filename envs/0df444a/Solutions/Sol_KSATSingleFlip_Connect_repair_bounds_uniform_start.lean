-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_bounds_uniform_start
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:50:14.82248+00:00
-- url     : https://prove2.me/submissions/228958a7-01e1-4ec5-96da-588daed5035b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KSATSingleFlip_Connect_lemma_7_11
import Theorems.Thm_KSATSingleFlip_Connect_repair_planted_transport

open scoped Classical BigOperators
open OAI.FixedClauseThreshold KSATSingleFlip.Connect

theorem solution :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ t : ℕ,
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          uexp (fun z : Fin n → Bool => poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φ := ofList l
              let I0 := satIdx Φ z
              let X := glauberState (subF Φ I0) z s
              RepairBounds k Φ I0 X)) := by
  obtain ⟨k0, hk⟩ := lemma_7_11
  refine ⟨max k0 1, ?_⟩
  intro k hk0
  have hkpos : 1 ≤ k := le_trans (le_max_right _ _) hk0
  obtain ⟨n0, hn⟩ := hk k (le_trans (le_max_left _ _) hk0)
  refine ⟨max n0 k, ?_⟩
  intro n hn0 m hm hupper t
  have hkn : k ≤ n := le_trans (le_max_right _ _) hn0
  have hbase := hn n (le_trans (le_max_left _ _) hn0) m hm hupper
  let P : (Fin n → Bool) → ℝ := fun x =>
    poisExp (clausesSatBy (k := k) (fun _ : Fin 1 => x)) (m * (1 - 1 / (2 : ℝ) ^ k))
      (fun l0 => poisProb (allClauses n k) m (fun g =>
        ∀ I : Finset (Fin (ofList g).length),
          RepairBounds k (ofList l0 ++ subF (ofList g) I)
            (Finset.univ.filter fun c => c.val < (ofList l0).length) x))
  have hpoint : ∀ x, 1 - Real.exp (-(rho k ^ 8) * n) ≤ P x := hbase
  have hmean : 1 - Real.exp (-(rho k ^ 8) * n) ≤ uexp P := by
    have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (Fin n → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
      exact_mod_cast ne_of_gt this
    have hc : uexp (fun _ : Fin n → Bool => 1 - Real.exp (-(rho k ^ 8) * n)) =
        1 - Real.exp (-(rho k ^ 8) * n) := by
      unfold uexp
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [← hc]
    unfold uexp
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x))
      (show (0 : ℝ) ≤ Fintype.card (Fin n → Bool) by positivity)
  exact hmean.trans (repair_planted_transport hkpos hkn m hm t)



#print axioms solution
