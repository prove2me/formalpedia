-- Prove2me | solution 1 for HiringLP.ProbeTopK.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:51:41.975886+00:00
-- url     : https://prove2.me/submissions/e74a8ed6-9ab9-490b-b195-5694fa0e0f38

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_WeightedBernoulli

set_option autoImplicit false
open Finset HiringLP.ProbeTopK

theorem PTK5_exists_opt {n : ℕ} (I : WBInstance n) (hI : I.Valid) :
    ∃ x y : Fin n → ℝ, WBIsOpt I x y := by
  set K : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {z | WBFeasible I z.1 z.2} with hK
  have hsub : K ⊆ Set.Icc (0, 0) (1, 1) := by
    rintro ⟨x, y⟩ ⟨h1, -, -, h4, h5⟩
    refine ⟨⟨fun i => h4 i, fun i => (h5 i).1⟩, ⟨fun i => ?_, fun i => (h5 i).2⟩⟩
    have := h1 i
    have hq := hI.2.2.2.2 i
    have := mul_le_one₀ (h5 i).2 hq.1 hq.2
    show x i ≤ 1
    linarith
  have hclosed : IsClosed K := by
    have e : K = (⋂ i, {z : (Fin n → ℝ) × (Fin n → ℝ) | z.1 i ≤ z.2 i * I.q i}) ∩
        {z | ∑ i, z.2 i ≤ (I.T : ℝ)} ∩ {z | ∑ i, z.1 i ≤ (I.k : ℝ)} ∩
        (⋂ i, {z : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ z.1 i}) ∩
        (⋂ i, {z : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ z.2 i ∧ z.2 i ≤ 1}) := by
      ext z
      simp only [hK, WBFeasible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [e]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
    · exact isClosed_iInter (fun i => isClosed_le (by fun_prop) (by fun_prop))
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · exact isClosed_iInter (fun i => isClosed_le (by fun_prop) (by fun_prop))
    · exact isClosed_iInter (fun i =>
        (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).inter
          (isClosed_le ((continuous_apply i).comp continuous_snd) continuous_const))
  have hcomp : IsCompact K := (isCompact_Icc).of_isClosed_subset hclosed hsub
  have hne : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    refine ⟨fun i => by simp, by simp, by simp, fun i => le_rfl, fun i => ⟨le_rfl, by simp⟩⟩
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn hne
    (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) => WBobj I z.1) (by unfold WBobj; fun_prop)
  refine ⟨z.1, z.2, hz, fun x' y' h' => ?_⟩
  exact hmax (show (x', y') ∈ K from h')

theorem solution {n : ℕ} (I : WBInstance n) (hI : I.Valid) :
    ∃ x y : Fin n → ℝ, WBIsOpt I x y ∧ ∀ i, x i = y i * I.q i := by
  obtain ⟨x, y, ⟨h1, h2, h3, h4, h5⟩, hopt⟩ := PTK5_exists_opt I hI
  set y' : Fin n → ℝ := fun i => if I.q i = 0 then 0 else x i / I.q i with hy'
  have hyy : ∀ i, 0 ≤ y' i ∧ y' i ≤ y i := by
    intro i
    simp only [hy']
    split_ifs with hq
    · exact ⟨le_rfl, (h5 i).1⟩
    · have hqp : 0 < I.q i := lt_of_le_of_ne (hI.2.2.2.2 i).1 (Ne.symm hq)
      exact ⟨div_nonneg (h4 i) hqp.le, (div_le_iff₀ hqp).2 (h1 i)⟩
  have hxy : ∀ i, x i = y' i * I.q i := by
    intro i
    simp only [hy']
    split_ifs with hq
    · have := h1 i; rw [hq, mul_zero] at this; linarith [h4 i]
    · field_simp
  refine ⟨x, y', ⟨⟨fun i => (hxy i).le, ?_, h3, h4, fun i => ⟨(hyy i).1, (hyy i).2.trans (h5 i).2⟩⟩,
    fun x'' y'' h'' => hopt x'' y'' h''⟩, hxy⟩
  exact (sum_le_sum (fun i _ => (hyy i).2)).trans h2
