-- Prove2me | solution 1 for JohnsonApprox.ExactCover.overlap_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:56:59.443294+00:00
-- url     : https://prove2.me/submissions/3b377e44-6907-4da8-bd91-c30c4b4fe2d9

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2



namespace JohnsonApprox.ExactCover

open Finset

variable {α : Type} [DecidableEq α]

/-- invariant of reachable states -/
def Inv (F : Input α) (σ : State F) : Prop :=
  σ.LEFT = univ \ σ.SUB ∧ σ.UNCOV = F.ground \ σ.SUB.biUnion F.S

lemma S_sub_ground (F : Input α) (i : Fin F.p) : F.S i ⊆ F.ground := by
  intro x hx; unfold Input.ground; exact mem_biUnion.2 ⟨i, mem_univ _, hx⟩

lemma inv_init (F : Input α) : Inv F (init F) := by
  unfold Inv init; simp

lemma inv_step (F : Input α) {σ σ' : State F} {i : Fin F.p} (h : Inv F σ)
    (hs : StepVia F σ i σ') : Inv F σ' := by
  obtain ⟨hL, hU⟩ := h
  obtain ⟨_, ⟨hiL, _, _⟩, rfl⟩ := hs
  refine ⟨?_, ?_⟩
  · simp only; rw [hL]; ext x; simp only [mem_erase, mem_sdiff, mem_univ, true_and, mem_insert]
    tauto
  · simp only; rw [hU]; ext x; simp only [mem_sdiff, biUnion_insert, mem_union]; tauto

lemma inv_of_reachable (F : Input α) {σ : State F} (h : Reachable F σ) : Inv F σ := by
  induction h with
  | refl => exact inv_init F
  | tail _ hst ih => obtain ⟨i, hi⟩ := hst; exact inv_step F ih hi

lemma reachable_of_runOV (F : Input α) {σ : State F} {ov : ℕ} (h : RunOV F σ ov) :
    Reachable F σ := by
  induction h with
  | init => exact Relation.ReflTransGen.refl
  | step _ hs ih => exact ih.tail ⟨_, hs⟩

lemma measure_aux (F : Input α) {σ : State F} {ov : ℕ} (hrun : RunOV F σ ov) :
    F.measure σ.SUB + σ.UNCOV.card = F.ground.card + ov ∧ σ.UNCOV ⊆ F.ground := by
  induction hrun with
  | init => simp [init, Input.measure]
  | @step σ ov i σ' hr hs ih =>
    have hinv := inv_of_reachable F (reachable_of_runOV F hr)
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨_, ⟨hiL, _, _⟩, rfl⟩ := hs
    have hiS : i ∉ σ.SUB := by rw [hinv.1] at hiL; simp at hiL; exact hiL
    refine ⟨?_, fun x hx => ih2 (mem_sdiff.1 hx).1⟩
    simp only [Input.measure] at ih1 ⊢
    rw [sum_insert hiS]
    have h1 := card_sdiff_add_card_inter σ.UNCOV (F.S i)
    have h2 := card_sdiff_add_card_inter (F.S i) σ.UNCOV
    rw [inter_comm] at h2
    omega

theorem measure_eq_card_add_overlap (F : Input α)
    {σ : State F} {ov : ℕ} (hrun : RunOV F σ ov) (hσ : Halts σ) :
    F.measure σ.SUB = F.ground.card + ov := by
  have := (measure_aux F hrun).1
  unfold Halts at hσ; rw [hσ] at this; simpa using this

lemma ground_le_measure (F : Input α) (M : Finset (Fin F.p)) (hM : F.IsSubcover M) :
    F.ground.card ≤ F.measure M := by
  unfold Input.IsSubcover at hM; rw [← hM]; exact card_biUnion_le

lemma ground_le_opt (F : Input α) : F.ground.card ≤ F.opt := by
  unfold Input.opt; apply le_inf'; intro M hM
  unfold Input.subcovers at hM; rw [mem_filter] at hM
  exact ground_le_measure F M hM.2

theorem uncov_card_bound_of_ratio_ge (F : Input α)
    {σ : State F} {i : Fin F.p} (hσ : Reachable F σ) (hi : MayChoose F σ i) (y : ℝ)
    (hy : y * ((F.S i ∩ σ.UNCOV).card : ℝ) ≤ ((F.S i \ σ.UNCOV).card : ℝ)) :
    (y + 1) * (σ.UNCOV.card : ℝ) ≤ (F.opt : ℝ) := by
  rcases lt_or_ge (y + 1) 0 with hy1 | hy1
  · have : (y + 1) * (σ.UNCOV.card : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hy1.le (by positivity)
    exact this.trans (by positivity)
  obtain ⟨hL, hU⟩ := inv_of_reachable F hσ
  obtain ⟨hiL, hne, hmin⟩ := hi
  obtain ⟨M, hM, hopt⟩ := exists_mem_eq_inf' F.subcovers_nonempty F.measure
  have hopt' : F.opt = F.measure M := hopt
  unfold Input.subcovers at hM; rw [mem_filter] at hM
  have hcov : σ.UNCOV ⊆ M.biUnion (fun j => F.S j ∩ σ.UNCOV) := by
    intro x hx
    have hx' : x ∈ F.ground := by rw [hU] at hx; exact (mem_sdiff.1 hx).1
    rw [← hM.2, mem_biUnion] at hx'
    obtain ⟨j, hj, hxj⟩ := hx'
    exact mem_biUnion.2 ⟨j, hj, mem_inter.2 ⟨hxj, hx⟩⟩
  have hc1 : (σ.UNCOV.card : ℝ) ≤ ∑ j ∈ M, ((F.S j ∩ σ.UNCOV).card : ℝ) := by
    exact_mod_cast (card_le_card hcov).trans card_biUnion_le
  have hpos : (0 : ℝ) < (F.S i ∩ σ.UNCOV).card := by exact_mod_cast card_pos.2 hne
  have hterm : ∀ j ∈ M, (y + 1) * ((F.S j ∩ σ.UNCOV).card : ℝ) ≤ (F.S j).card := by
    intro j _
    have hsplit : ((F.S j).card : ℝ) = (F.S j \ σ.UNCOV).card + (F.S j ∩ σ.UNCOV).card := by
      exact_mod_cast (card_sdiff_add_card_inter _ _).symm
    rcases (F.S j ∩ σ.UNCOV).eq_empty_or_nonempty with he | hne'
    · rw [he]; simp
    · have hjL : j ∈ σ.LEFT := by
        rw [hL, mem_sdiff]; refine ⟨mem_univ _, fun hjS => ?_⟩
        obtain ⟨x, hx⟩ := hne'
        rw [mem_inter, hU, mem_sdiff] at hx
        exact hx.2.2 (mem_biUnion.2 ⟨j, hjS, hx.1⟩)
      have hm := hmin j hjL hne'
      have hm' : ((F.S i \ σ.UNCOV).card : ℝ) * (F.S j ∩ σ.UNCOV).card ≤
          ((F.S j \ σ.UNCOV).card : ℝ) * (F.S i ∩ σ.UNCOV).card := by exact_mod_cast hm
      have : y * ((F.S j ∩ σ.UNCOV).card : ℝ) ≤ (F.S j \ σ.UNCOV).card := by
        have h3 : y * (F.S i ∩ σ.UNCOV).card * (F.S j ∩ σ.UNCOV).card ≤
            ((F.S j \ σ.UNCOV).card : ℝ) * (F.S i ∩ σ.UNCOV).card :=
          (mul_le_mul_of_nonneg_right hy (by positivity)).trans hm'
        nlinarith
      rw [hsplit]; linarith
  calc (y + 1) * (σ.UNCOV.card : ℝ) ≤ (y + 1) * ∑ j ∈ M, ((F.S j ∩ σ.UNCOV).card : ℝ) :=
        mul_le_mul_of_nonneg_left hc1 hy1
    _ = ∑ j ∈ M, (y + 1) * ((F.S j ∩ σ.UNCOV).card : ℝ) := by rw [mul_sum]
    _ ≤ ∑ j ∈ M, ((F.S j).card : ℝ) := sum_le_sum hterm
    _ = F.opt := by rw [hopt']; unfold Input.measure; push_cast; rfl

theorem ratio_le_of_covered_fraction (F : Input α)
    (hT : F.ground.Nonempty) {σ : State F} {i : Fin F.p} (hσ : Reachable F σ)
    (hi : MayChoose F σ i) :
    ((F.S i \ σ.UNCOV).card : ℝ) / ((F.S i ∩ σ.UNCOV).card : ℝ) ≤
      ((F.opt : ℝ) / (F.ground.card : ℝ)) /
        (1 - ((F.ground \ σ.UNCOV).card : ℝ) / (F.ground.card : ℝ)) - 1 := by
  have hpos : (0 : ℝ) < (F.S i ∩ σ.UNCOV).card := by exact_mod_cast card_pos.2 hi.2.1
  have hb := uncov_card_bound_of_ratio_ge F hσ hi
    (((F.S i \ σ.UNCOV).card : ℝ) / ((F.S i ∩ σ.UNCOV).card : ℝ)) (by
      rw [div_mul_cancel₀ _ hpos.ne'])
  have hUsub : σ.UNCOV ⊆ F.ground := by
    rw [(inv_of_reachable F hσ).2]; exact sdiff_subset
  have hUpos : (0 : ℝ) < σ.UNCOV.card := by
    obtain ⟨x, hx⟩ := hi.2.1; exact_mod_cast card_pos.2 ⟨x, (mem_inter.1 hx).2⟩
  have hTpos : (0 : ℝ) < F.ground.card := by exact_mod_cast card_pos.2 hT
  have hsd : ((F.ground \ σ.UNCOV).card : ℝ) = F.ground.card - σ.UNCOV.card := by
    rw [card_sdiff_of_subset hUsub]; push_cast [card_le_card hUsub]; ring
  have h1 : 1 - ((F.ground \ σ.UNCOV).card : ℝ) / (F.ground.card : ℝ) =
      σ.UNCOV.card / F.ground.card := by
    rw [hsd]; field_simp; ring
  rw [h1, div_div_div_cancel_right₀ hTpos.ne']
  rw [le_sub_iff_add_le, le_div_iff₀ hUpos]; linarith

section overlap
open Real

/-- integral of `min k (A/x)` from `0` to `x`, with `s = A/k` -/
noncomputable def Hc (k s x : ℝ) : ℝ := if x ≤ s then k * x else k * s + k * s * Real.log (x / s)

lemma Hc_step (k s x : ℝ) (hk : 0 < k) (hs : 0 < s) (hx : 1 ≤ x) :
    min k (k * s / x) ≤ Hc k s x - Hc k s (x - 1) := by
  have hx0 : 0 < x := by linarith
  unfold Hc
  by_cases h1 : x ≤ s
  · rw [if_pos h1, if_pos (by linarith)]; exact (min_le_left _ _).trans (by linarith)
  · rw [if_neg h1]
    push_neg at h1
    by_cases h2 : x - 1 ≤ s
    · rw [if_pos h2]
      have hl : 1 - s / x ≤ Real.log (x / s) := by
        have := Real.log_le_sub_one_of_pos (show 0 < s / x by positivity)
        rw [Real.log_div hs.ne' hx0.ne'] at this
        rw [Real.log_div hx0.ne' hs.ne']; linarith
      refine (min_le_right _ _).trans ?_
      have key : 0 ≤ 2 * s * x - s ^ 2 - x ^ 2 + x - s := by nlinarith
      have e : k * s + k * s * (1 - s / x) - k * (x - 1) - k * s / x =
          k * (2 * s * x - s ^ 2 - x ^ 2 + x - s) / x := by field_simp; ring
      have : 0 ≤ k * (2 * s * x - s ^ 2 - x ^ 2 + x - s) / x := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ k * s)]
    · rw [if_neg h2]
      push_neg at h2
      have hx1 : 0 < x - 1 := by linarith
      have hl : Real.log (x - 1) - Real.log x ≤ (x - 1) / x - 1 := by
        rw [← Real.log_div hx1.ne' hx0.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
      have e1 : Real.log (x / s) - Real.log ((x - 1) / s) = Real.log x - Real.log (x - 1) := by
        rw [Real.log_div hx0.ne' hs.ne', Real.log_div hx1.ne' hs.ne']; ring
      have e2 : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
      refine (min_le_right _ _).trans ?_
      have : k * s / x ≤ k * s * (Real.log (x / s) - Real.log ((x - 1) / s)) := by
        rw [e1]; rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      linarith

lemma Hc_sum (k s : ℝ) (hk : 0 < k) (hs : 0 < s) (N : ℕ) :
    ∑ ρ ∈ range N, min k (k * s / ((ρ : ℝ) + 1)) ≤ Hc k s N := by
  have h0 : Hc k s 0 = 0 := by unfold Hc; rw [if_pos hs.le]; ring
  have : Hc k s N = ∑ ρ ∈ range N, (Hc k s ((ρ : ℝ) + 1) - Hc k s ρ) := by
    have e := sum_range_sub (fun ρ : ℕ => Hc k s ρ) N
    push_cast at e; rw [e, h0, sub_zero]
  rw [this]
  apply sum_le_sum; intro ρ _
  have := Hc_step k s ((ρ : ℝ) + 1) hk hs (by linarith [(Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)])
  simpa using this

lemma Hc_le (k s : ℝ) (hk : 1 ≤ k) (hs : 0 < s) (N : ℝ) (hN0 : 0 < N) (hN : N ≤ k * s) :
    Hc k s N ≤ k * s * (Real.log k + 1) := by
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  unfold Hc
  split_ifs with h
  · have : k * N ≤ k * s := mul_le_mul_of_nonneg_left h (by linarith)
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ k * s) hlk]
  · have : Real.log (N / s) ≤ Real.log k := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hs]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ k * s)]

end overlap

theorem overlap_le (k : ℕ) (hk : 1 ≤ k) (F : Input α)
    (hF : InEC k F) (hT : F.ground.Nonempty) {σ : State F} {ov : ℕ}
    (hrun : RunOV F σ ov) (hσ : Halts σ) :
    (ov : ℝ) ≤ (F.ground.card : ℝ) *
      (((F.opt : ℝ) / (F.ground.card : ℝ)) * (Real.log k + 1) - 1) := by
  set A : ℝ := (F.opt : ℝ) with hAdef
  set N : ℝ := (F.ground.card : ℝ) with hNdef
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast card_pos.2 hT
  have hNA : N ≤ A := by rw [hNdef, hAdef]; exact_mod_cast ground_le_opt F
  have hApos : 0 < A := by linarith
  set s : ℝ := A / k with hsdef
  have hs : 0 < s := by positivity
  have hks : k * s = A := by rw [hsdef]; field_simp
  let g : ℕ → ℝ := fun ρ => min (k : ℝ) (A / ((ρ : ℝ) + 1)) - 1
  let Φ : ℕ → ℝ := fun u => ∑ ρ ∈ range u, g ρ
  have hinv : ∀ {σ : State F} {ov : ℕ}, RunOV F σ ov →
      (ov : ℝ) + Φ σ.UNCOV.card ≤ Φ F.ground.card ∧ σ.UNCOV ⊆ F.ground := by
    intro σ ov hr
    induction hr with
    | init => simp [init]
    | @step σ ov i σ' hr hs ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hreach := reachable_of_runOV F hr
      obtain ⟨_, hmc, rfl⟩ := hs
      refine ⟨?_, fun x hx => ih2 (mem_sdiff.1 hx).1⟩
      simp only
      set u := σ.UNCOV.card
      set n := (F.S i ∩ σ.UNCOV).card
      set o := (F.S i \ σ.UNCOV).card
      have hnpos : 0 < n := card_pos.2 hmc.2.1
      have hU' : (σ.UNCOV \ F.S i).card = u - n := by
        have := card_sdiff_add_card_inter σ.UNCOV (F.S i)
        rw [inter_comm] at this; simp only [u, n]; omega
      have hnu : n ≤ u := by
        simp only [n, u]; exact card_le_card inter_subset_right
      rw [hU']
      have hsplit : Φ u = Φ (u - n) + ∑ ρ ∈ Ico (u - n) u, g ρ := by
        simp only [Φ]; rw [sum_range_add_sum_Ico _ (Nat.sub_le u n)]
      have hmono : ∀ ρ ∈ Ico (u - n) u, g (u - 1) ≤ g ρ := by
        intro ρ hρ
        rw [mem_Ico] at hρ
        simp only [g]
        apply sub_le_sub_right
        apply min_le_min le_rfl
        apply div_le_div_of_nonneg_left hApos.le (by positivity)
        have : ρ + 1 ≤ u := by omega
        have : ((ρ + 1 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast this
        push_cast at this
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      have hsum : (n : ℝ) * g (u - 1) ≤ ∑ ρ ∈ Ico (u - n) u, g ρ := by
        have := sum_le_sum hmono
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
        rw [show u - (u - n) = n by omega] at this; exact this
      -- the overlap bound
      have hupos : (0 : ℝ) < u := by
        have : 0 < u := lt_of_lt_of_le hnpos hnu
        exact_mod_cast this
      have hgu : g (u - 1) = min (k : ℝ) (A / u) - 1 := by
        simp only [g]; rw [Nat.cast_sub (by omega)]; push_cast; ring_nf
      have hb := uncov_card_bound_of_ratio_ge F hreach hmc ((o : ℝ) / n) (by
        rw [div_mul_cancel₀ _ (by positivity)])
      have hSk : (o : ℝ) + n ≤ k := by
        have := card_sdiff_add_card_inter (F.S i) σ.UNCOV
        have h2 := hF i
        have : o + n ≤ k := by simp only [o, n]; omega
        exact_mod_cast this
      have hover : (o : ℝ) ≤ n * g (u - 1) := by
        rw [hgu]
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have h1 : (o : ℝ) + n ≤ n * k := by
          nlinarith [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ n by exact_mod_cast hnpos)
            (show (0:ℝ) ≤ k by positivity)]
        have h2 : (o : ℝ) + n ≤ n * (A / u) := by
          rw [mul_div_assoc', le_div_iff₀ hupos]
          have hb' : ((o : ℝ) / n + 1) * u ≤ A := hb
          have : ((o : ℝ) / n + 1) * u * n = (o + n) * u := by field_simp
          nlinarith
        rcases min_cases (k : ℝ) (A / u) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;> linarith
      push_cast
      linarith
  obtain ⟨h1, _⟩ := hinv hrun
  unfold Halts at hσ
  rw [hσ, card_empty] at h1
  simp only [Φ, range_zero, sum_empty, add_zero] at h1
  have hΦ : Φ F.ground.card ≤ A * (Real.log k + 1) - N := by
    simp only [Φ, g]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have := Hc_sum k s (by linarith) hs F.ground.card
    rw [hks] at this
    have h2 := Hc_le k s hk' hs N hNpos (by rw [hks]; exact hNA)
    rw [hks] at h2
    rw [hNdef] at h2 ⊢
    linarith
  have : N * (A / N * (Real.log k + 1) - 1) = A * (Real.log k + 1) - N := by
    field_simp
  rw [this]; linarith

end JohnsonApprox.ExactCover

open JohnsonApprox.ExactCover

theorem solution {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (F : Input α)
    (hF : InEC k F) (hT : F.ground.Nonempty) {σ : State F} {ov : ℕ}
    (hrun : RunOV F σ ov) (hσ : Halts σ) :
    (ov : ℝ) ≤ (F.ground.card : ℝ) *
      (((F.opt : ℝ) / (F.ground.card : ℝ)) * (Real.log k + 1) - 1) := by
  exact overlap_le k hk F hF hT hrun hσ
