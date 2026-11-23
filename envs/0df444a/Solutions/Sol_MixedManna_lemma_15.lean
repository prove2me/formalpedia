-- Prove2me | solution 1 for MixedManna.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:20:16.757598+00:00
-- url     : https://prove2.me/submissions/132f0c7f-61ca-4311-8e6c-8c271f2f3646

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_lcpSolutions

set_option autoImplicit false

open Classical MixedManna

theorem solution {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P R : ℝ) (hP : 0 < P) (δ : M → ℝ)
    (hδ : IsAdmissibleDelta I δ) (ε : ℝ) (hε : 0 < ε) (x : LCPVar I)
    (hx : x ∈ lcpSolutions I P R δ ε) :
    (∀ j, pv x j ≤ P) ∧ ((∃ j, ¬ IsGood I j ∧ pv x j < P) → ∀ i, rv x i ≤ R) ∧
      (∀ i, rv x i = R → ∀ j, ¬ IsGood I j → pv x j = P) := by
  simp only [lcpSolutions, lcpPolyhedron, Set.mem_ofPred_eq] at hx
  obtain ⟨⟨hp0, hf0, hr0, hs0, hz0, hagent, hprice, hspend, hseg⟩, -, -, -, hsc⟩ := hx
  have hlcp_pos : ∀ σ : Seg I, 0 < lcpLength I ε σ := by
    intro σ
    unfold lcpLength
    split_ifs with hlast
    · linarith
    · unfold IsLastSeg at hlast
      have hk : segIdx σ < I.K (segAgent σ) (segItem σ) := σ.1.2.isLt
      exact hI.L_pos _ _ _ (by omega)
  have hp_le_P : ∀ j : M, pv x j ≤ P := by
    intro j
    by_cases hj : IsGood I j
    · obtain ⟨i, hi0⟩ := hj
      have hK : 0 < I.K i j := hI.K_pos i j
      let σ₀ : Seg I := ⟨⟨(i, j), ⟨0, hK⟩⟩, fun _ => hi0⟩
      have hs_ge := hseg σ₀
      have hL0 := hlcp_pos σ₀
      have hf_ge := hf0 σ₀
      have hmul : lcpLength I ε σ₀ * pv x j ≤ lcpLength I ε σ₀ * P := by
        unfold segSlack at hs_ge
        have hitem : segItem σ₀ = j := rfl
        rw [hitem] at hs_ge
        linarith
      exact (mul_le_mul_iff_of_pos_left hL0).mp hmul
    · have hp_sl := hprice j
      simp only [priceSlack, if_neg hj] at hp_sl
      have hsum_nn : 0 ≤ ∑ σ : Seg I, if segItem σ = j then fv x σ else 0 :=
        Finset.sum_nonneg fun σ _ => by split_ifs; exact hf0 σ; exact le_rfl
      linarith
  have hr_lt_R : ∀ j : M, ¬ IsGood I j → pv x j < P → ∀ i : N, rv x i < R := by
    intro j hbad hp_lt i
    have hK : 1 ≤ I.K i j := hI.K_pos i j
    let σ : Seg I := ⟨⟨(i, j), ⟨I.K i j - 1, Nat.sub_lt hK zero_lt_one⟩⟩, fun hg => absurd hg hbad⟩
    have hitem : segItem σ = j := rfl
    have hagent_σ : segAgent σ = i := rfl
    have hlast : IsLastSeg σ := by
      unfold IsLastSeg segIdx segAgent segItem
      dsimp only [σ]
      omega
    have hfle : fv x σ ≤ ∑ σ' : Seg I, if segItem σ' = j then fv x σ' else 0 := by
      have := Finset.single_le_sum
        (f := fun σ' : Seg I => if segItem σ' = j then fv x σ' else 0)
        (fun σ' _ => by split_ifs; exact hf0 σ'; exact le_rfl)
        (Finset.mem_univ σ)
      simpa [hitem] using this
    have hp_sl := hprice j
    simp only [priceSlack, if_neg hbad] at hp_sl
    have hf_bound : fv x σ ≤ P - pv x j := by linarith
    have hseg_pos : 0 < segSlack I P ε x σ := by
      unfold segSlack
      rw [lcpLength, if_pos hlast, hitem]
      have := mul_pos hε (sub_pos.mpr hp_lt)
      nlinarith
    have hsv0 : sv x σ = 0 := (mul_eq_zero.mp (hsc σ)).resolve_right hseg_pos.ne'
    have hU0 : I.U i j 0 < 0 := hI.bad_slope_neg j hbad i
    have hUlast : I.U i j (I.K i j - 1) < 0 := by
      by_cases hk0 : 0 = I.K i j - 1
      · rw [← hk0]; exact hU0
      · exact (hI.U_strictAnti i j 0 (I.K i j - 1) (by omega) (by omega)).trans hU0
    have hD_pos : 0 < -segSlope σ := by
      unfold segSlope segAgent segItem segIdx
      dsimp only [σ]
      linarith
    have hsp := hspend σ
    unfold spendSlack at hsp
    rw [hitem, hagent_σ, if_neg hbad, hsv0] at hsp
    by_contra hge
    push Not at hge
    have hnn : 0 ≤ (-segSlope σ) * (rv x i - R) := mul_nonneg hD_pos.le (by linarith)
    linarith
  refine ⟨hp_le_P, ?_, ?_⟩
  · rintro ⟨j, hbad, hp_lt⟩ i
    exact (hr_lt_R j hbad hp_lt i).le
  · intro i hri j hbad
    by_contra hne
    have hp_lt : pv x j < P := lt_of_le_of_ne (hp_le_P j) hne
    have := hr_lt_R j hbad hp_lt i
    linarith
