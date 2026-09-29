-- Prove2me | solution 1 for GoldbergTarjan.Generic.max_flow_iff_no_augmenting_path
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:58:23.698502+00:00
-- url     : https://prove2.me/submissions/944c2f4c-8059-43df-8bd6-c89e7dcc5cbf

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow



namespace GoldbergTarjan.Generic

open Classical

set_option linter.unusedSectionVars false
section MF
variable {V : Type} [Fintype V]

/-- unit flow on a pair -/
noncomputable def unitF (a b : V) : V → V → ℝ :=
  fun x y => (if x = a ∧ y = b then 1 else 0) - (if x = b ∧ y = a then 1 else 0)

lemma excess_unitF (a b u : V) :
    excess (unitF a b) u = (if u = b then 1 else 0) - (if u = a then 1 else 0) := by
  unfold excess unitF
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : u = b
    · simp [h]
    · simp [h]
  · by_cases h : u = a
    · simp [h]
    · simp [h]

lemma unitF_antisymm (a b x y : V) : unitF a b x y = - unitF a b y x := by
  unfold unitF
  have e1 : (if y = a ∧ x = b then (1:ℝ) else 0) = if x = b ∧ y = a then 1 else 0 :=
    if_congr and_comm rfl rfl
  have e2 : (if y = b ∧ x = a then (1:ℝ) else 0) = if x = a ∧ y = b then 1 else 0 :=
    if_congr and_comm rfl rfl
  rw [e1, e2]; ring

lemma excess_add (f g : V → V → ℝ) (u : V) : excess (fun x y => f x y + g x y) u = excess f u + excess g u := by
  unfold excess; rw [Finset.sum_add_distrib]

lemma excess_smul (f : V → V → ℝ) (r : ℝ) (u : V) : excess (fun x y => r * f x y) u = r * excess f u := by
  unfold excess; rw [Finset.mul_sum]

lemma path_flow (N : Network V) (f : V → V → ℝ) (a b : V) (hab : ResidualReachable N f a b) :
    ∃ h : V → V → ℝ, (∀ x y, h x y = - h y x) ∧ (∀ x y, 0 < h x y → IsResidualEdge N f x y) ∧
      ∀ u, excess h u = (if u = b then 1 else 0) - (if u = a then 1 else 0) := by
  induction hab with
  | refl => exact ⟨fun _ _ => 0, by simp, by simp, by intro u; simp [excess]⟩
  | tail _ hbc ih =>
    rename_i b c _
    obtain ⟨h, h1, h2, h3⟩ := ih
    refine ⟨fun x y => h x y + unitF b c x y, ?_, ?_, ?_⟩
    · intro x y; beta_reduce; rw [h1 x y, unitF_antisymm]; ring
    · intro x y hxy
      by_cases hp : x = b ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp; exact hbc
      · have : unitF b c x y ≤ 0 := by unfold unitF; rw [if_neg hp]; split_ifs <;> norm_num
        exact h2 x y (by linarith)
    · intro u; rw [excess_add, h3, excess_unitF]; ring

lemma sum_antisymm_zero (g : V → V → ℝ) (hg : ∀ x y, g x y = - g y x) (T : Finset V) :
    ∑ x ∈ T, ∑ y ∈ T, g x y = 0 := by
  have : ∑ x ∈ T, ∑ y ∈ T, g x y = - ∑ x ∈ T, ∑ y ∈ T, g x y := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; congr 1; ext x; rw [← Finset.sum_neg_distrib]
    congr 1; ext y; rw [hg]
  linarith

/-- value of a flow equals the net flow across a cut containing s but not t -/
lemma value_eq_cut (N : Network V) (g : V → V → ℝ) (hg : IsFlow N g) (S : Finset V)
    (hs : N.s ∈ S) (ht : N.t ∉ S) :
    value N g = ∑ x ∈ S, ∑ u ∈ Sᶜ, g x u := by
  obtain ⟨_, ha, hc⟩ := hg
  have h1 : ∑ u ∈ Sᶜ, excess g u = value N g := by
    rw [Finset.sum_eq_single N.t]
    · rfl
    · intro u hu hut; apply hc u _ hut; intro h; subst h; simp at hu; exact hu hs
    · intro h; simp at h; exact absurd h ht
  rw [← h1]
  unfold excess
  have h2 : ∀ u, ∑ x, g x u = ∑ x ∈ S, g x u + ∑ x ∈ Sᶜ, g x u := by
    intro u; rw [Finset.sum_add_sum_compl]
  simp_rw [h2]
  rw [Finset.sum_add_distrib]
  have h3 : ∑ u ∈ Sᶜ, ∑ x ∈ Sᶜ, g x u = 0 := by
    rw [Finset.sum_comm]; exact sum_antisymm_zero g ha _
  rw [h3, add_zero, Finset.sum_comm]

theorem mf_core (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ResidualReachable N f N.s N.t := by
  constructor
  · rintro ⟨_, hmax⟩ hr
    obtain ⟨h, h1, h2, h3⟩ := path_flow N f _ _ hr
    -- choose ε
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ x y, f x y + ε * h x y ≤ N.c x y := by
      rw [Filter.eventually_all]; intro x; rw [Filter.eventually_all]; intro y
      by_cases hp : 0 < h x y
      · have hr' := h2 x y hp
        unfold IsResidualEdge residualCap at hr'
        have ht : Filter.Tendsto (fun ε : ℝ => f x y + ε * h x y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x y + 0 * h x y)) := by
          apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
          exact ((continuous_id.mul continuous_const).const_add _).tendsto 0 |>.congr (fun _ => rfl)
        rw [zero_mul, add_zero] at ht
        exact ht.eventually (ge_mem_nhds (by linarith))
      · push_neg at hp
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have : ε * h x y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε) hp
        linarith [hf.1 x y]
    obtain ⟨ε, hε1, hε2⟩ := (hev.and self_mem_nhdsWithin).exists
    have hflow : IsFlow N (fun x y => f x y + ε * h x y) := by
      refine ⟨hε1, ?_, ?_⟩
      · intro x y; beta_reduce; rw [hf.2.1 x y, h1 x y]; ring
      · intro u hus hut
        rw [excess_add, excess_smul (f := h), h3, hf.2.2 u hus hut]; simp [hus, hut]
    have hv := hmax _ hflow
    have : value N (fun x y => f x y + ε * h x y) = value N f + ε := by
      have e1 : value N (fun x y => f x y + ε * h x y) = excess (fun x y => f x y + ε * h x y) N.t := rfl
      rw [e1, excess_add, excess_smul (f := h), h3]
      simp [N.source_ne_sink.symm]; rfl
    rw [this] at hv
    have : (0:ℝ) < ε := hε2
    linarith
  · intro hnr
    refine ⟨hf, ?_⟩
    intro g hg
    set S : Finset V := Finset.univ.filter (fun u => ResidualReachable N f N.s u) with hS
    have hs : N.s ∈ S := by simp [hS]; exact Relation.ReflTransGen.refl
    have ht : N.t ∉ S := by simp [hS]; exact hnr
    rw [value_eq_cut N g hg S hs ht, value_eq_cut N f hf S hs ht]
    apply Finset.sum_le_sum; intro x hx; apply Finset.sum_le_sum; intro u hu
    have hfx : f x u = N.c x u := by
      by_contra hne
      have hlt : f x u < N.c x u := lt_of_le_of_ne (hf.1 x u) hne
      have : ResidualReachable N f N.s u := by
        simp [hS] at hx
        exact hx.tail (show IsResidualEdge N f x u by unfold IsResidualEdge residualCap; linarith)
      simp [hS] at hu; exact hu this
    rw [hfx]; exact hg.1 x u

end MF
end GoldbergTarjan.Generic

open GoldbergTarjan.Generic


theorem solution {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ResidualReachable N f N.s N.t := by
  exact mf_core N f hf
