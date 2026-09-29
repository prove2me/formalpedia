-- Prove2me | solution 1 for JohnsonApprox.ExactCover.measure_eq_card_add_overlap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:53:19.96863+00:00
-- url     : https://prove2.me/submissions/2d3abbae-b347-4fa6-85ca-c17fe122b792

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

end JohnsonApprox.ExactCover

open JohnsonApprox.ExactCover

theorem solution {α : Type} [DecidableEq α] (F : Input α)
    {σ : State F} {ov : ℕ} (hrun : RunOV F σ ov) (hσ : Halts σ) :
    F.measure σ.SUB = F.ground.card + ov := by
  exact measure_eq_card_add_overlap F hrun hσ
