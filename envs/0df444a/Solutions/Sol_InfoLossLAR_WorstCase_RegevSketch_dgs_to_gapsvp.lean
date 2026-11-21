-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dgs_to_gapsvp
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:49:06.492106+00:00
-- url     : https://prove2.me/submissions/dde2f381-1846-4696-a8a0-06bcb20303e9

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_far_mass
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_circuit_union

set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms.Complexity
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

private theorem event_transfer {observed ideal slack loss : ℝ}
    (hg : 1 - slack ≤ ideal) (ht : -loss ≤ observed - ideal) :
    1-observed ≤ slack + loss := by linarith

theorem solution :
  ∃ C k : ℕ,1 ≤ C ∧ ∀ G : MFamily,IsMQPT G →
    ∀ error : ℕ → ℝ,Negligible error →
      ∃ A : Family,IsQPT A ∧ ∃ cutoff : ℕ,∀ n ≥ cutoff,1 ≤ n →
        DGSAt G n (error n) →
          SolvesGapSVP A (famN n) ((C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k) := by
  obtain ⟨C, k, n₀, hC, hgeo⟩ := dual_parity_pool_far_mass
  refine ⟨C, k, hC, ?_⟩
  intro G hG error herr
  obtain ⟨A, hA, hcirc⟩ := dual_parity_pool_circuit_union G hG
  obtain ⟨n₁, hn₁⟩ := herr.2 6 (by norm_num)
  refine ⟨A, hA, max 64 (max n₀ n₁), ?_⟩
  intro n hn hpos hdgs
  change SolvesGapSVP A n _
  intro B hB δ hδ
  have h64 : 64 ≤ n := le_trans (le_max_left ..) hn
  have hn' : max n₀ n₁ ≤ n := le_trans (le_max_right ..) hn
  have hnr : (64 : ℝ) ≤ n := by exact_mod_cast h64
  have hnr' : (0 : ℝ) < n := by linarith
  have he := hn₁ n ((le_max_right ..).trans hn')
  rw [Real.rpow_neg (by positivity)] at he
  norm_num at he
  have hct : ((n : ℝ)+1)^3 * error n ≤ 1/(16*((n : ℝ)+1)) := by
    calc
      _ ≤ ((n : ℝ)+1)^3 * ((n : ℝ)^6)⁻¹ := by gcongr
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        calc
          _ ≤ (2*(n:ℝ))^3 * (16*(2*(n:ℝ))) := by gcongr <;> linarith
          _ = 256 * (n:ℝ)^4 := by ring
          _ ≤ (n:ℝ)^2 * (n:ℝ)^4 := by gcongr; nlinarith
          _ = _ := by ring
  have hc := hcirc n hpos B hB δ hδ
  constructor
  · intro hy
    rw [hc.1 hy]; norm_num
  · intro hfar
    have hg := hgeo n ((le_max_left ..).trans hn') hpos B hB δ hδ hfar
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    have hp (i : Fin n) : 1-outputProb G (dgsInput (D i) (r i) m (16*(n+1)))
        (decodedPoolEvent (E i)) ≤ 3/(16*((n : ℝ)+1)) := by
      obtain ⟨hdet, hr, ht, hmass⟩ := hg i
      have hev := hdgs (D i) hdet (r i) hr ht m (16*(n+1)) (E i)
      have hleft := (abs_le.mp hev).1
      change 1 - 1/(16*((n:ℝ)+1)) ≤ ∑' p : Fin m → Fin n → ℤ,
        (∏ j, coefficientMass (D i) (r i) (p j)) * (@ite ℝ (E i p) (Classical.propDecidable _) 1 0) at hmass
      have hbudget : 1/((16*(n+1) : ℕ) + 1 : ℝ) ≤ 1/(16*((n:ℝ)+1)) := by
        push_cast; gcongr; linarith
      have hm : (m : ℝ) * error n ≤ 1/(16*((n:ℝ)+1)) := by simpa [m] using hct
      calc
        _ ≤ 1/(16*((n:ℝ)+1)) + ((m:ℝ)*error n + 1/((16*(n+1) : ℕ) + 1 : ℝ)) := event_transfer hmass hleft
        _ ≤ 1/(16*((n:ℝ)+1)) + (1/(16*((n:ℝ)+1)) + 1/(16*((n:ℝ)+1))) := add_le_add le_rfl (add_le_add hm hbudget)
        _ = 3/(16*((n:ℝ)+1)) := by ring
    calc
      _ ≤ _ := hc.2
      _ ≤ ∑ _i : Fin n, 3/(16*((n:ℝ)+1)) := Finset.sum_le_sum (fun i _ => hp i)
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        linarith
