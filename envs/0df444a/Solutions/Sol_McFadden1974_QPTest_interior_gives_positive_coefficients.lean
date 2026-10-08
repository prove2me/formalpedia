-- Prove2me | solution 1 for McFadden1974.QPTest.interior_gives_positive_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:25:12.460563+00:00
-- url     : https://prove2.me/submissions/27c38c1a-3ff2-4d1b-92ba-95082f54e1b4

import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false


namespace McFadden1974.QPTest

theorem zmin_core {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) (h0 : (0 : EuclideanSpace ℝ (Fin K)) ∈ d.qpFeasible) :
    d.Axiom6 := by
  obtain ⟨α, hα, hsum⟩ := h0
  intro γ hγ
  have hall : ∀ n i j, inner ℝ (d.w n i j) γ = 0 := by
    have h1 : inner ℝ (∑ n, ∑ i, ∑ j, α n i j • d.w n i j) γ = 0 := by
      rw [← hsum]; simp
    simp only [sum_inner, inner_smul_left] at h1
    simp only [RCLike.conj_to_real] at h1
    have hle : ∀ n i j, α n i j * inner ℝ (d.w n i j) γ ≤ 0 := fun n i j =>
      mul_nonpos_of_nonneg_of_nonpos (le_trans zero_le_one (hα n i j)) (hγ n i j)
    have e1 := (Finset.sum_eq_zero_iff_of_nonpos (fun n _ => Finset.sum_nonpos
      (fun i _ => Finset.sum_nonpos (fun j _ => hle n i j)))).1 h1
    intro n i j
    have e2 := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ =>
      Finset.sum_nonpos (fun j _ => hle n i j))).1 (e1 n (Finset.mem_univ _))
    have e3 := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hle n i j)).1
      (e2 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    rcases mul_eq_zero.1 e3 with h | h
    · linarith [hα n i j]
    · exact h
  apply h5
  intro n i j
  obtain ⟨i0, hi0⟩ : ∃ i0, 0 < d.S n i0 := by
    by_contra hc
    push_neg at hc
    have := d.positive_repetitions n
    have : ∑ i, d.S n i = 0 := Finset.sum_eq_zero (fun i _ => by have := hc i; omega)
    omega
  have key : ∀ k, inner ℝ (d.z n k - d.z n i0) γ = 0 := by
    intro k
    have := hall n i0 k
    simp only [ChoiceData.w, inner_smul_left, RCLike.conj_to_real] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by exact_mod_cast hi0.ne')
    · exact h
  have : d.z n j - d.z n i = (d.z n j - d.z n i0) - (d.z n i - d.z n i0) := by abel
  rw [this, inner_sub_left, key, key, sub_zero]

theorem interior_core {N K : ℕ} (d : ChoiceData N K)
    (h : (0 : EuclideanSpace ℝ (Fin K)) ∈ interior d.coneSet) :
    (∃ α : (n : Fin N) → Fin (d.J n) → Fin (d.J n) → ℝ,
      (∀ n i j, 0 < α n i j) ∧
        (∑ n, ∑ i, ∑ j, α n i j • d.w n i j) = 0) ∧
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  set v : EuclideanSpace ℝ (Fin K) := ∑ n, ∑ i, ∑ j, d.w n i j with hv
  set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  have htpos : 0 < t := by rw [ht]; positivity
  have hmem : (-t) • v ∈ d.coneSet := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos htpos, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨β, hβ, hβs⟩ := hmem
  have hsum : (∑ n, ∑ i, ∑ j, (β n i j + t) • d.w n i j) = 0 := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hβs, hv]
    simp only [Finset.smul_sum, neg_smul, Finset.sum_neg_distrib, neg_add_cancel]
  refine ⟨⟨fun n i j => β n i j + t, fun n i j => by linarith [hβ n i j], hsum⟩, ?_, ?_⟩
  · refine ⟨0, ⟨fun n i j => (β n i j + t) / t, fun n i j => ?_, ?_⟩, by simp⟩
    · rw [le_div_iff₀ htpos]; linarith [hβ n i j]
    · have : (∑ n, ∑ i, ∑ j, ((β n i j + t) / t) • d.w n i j) =
          t⁻¹ • ∑ n, ∑ i, ∑ j, (β n i j + t) • d.w n i j := by
        simp only [Finset.smul_sum, smul_smul, div_eq_inv_mul]
      rw [this, hsum, smul_zero]
  · rintro _ ⟨y, _, rfl⟩
    positivity

theorem nonint_core {N K : ℕ} (d : ChoiceData N K)
    (h : (0 : EuclideanSpace ℝ (Fin K)) ∉ interior d.coneSet) :
    (∃ γ : EuclideanSpace ℝ (Fin K), γ ≠ 0 ∧
      ∀ n i j, inner ℝ (d.w n i j) γ ≤ 0) ∧ ¬ d.Axiom6 := by
  have hconv : Convex ℝ d.coneSet := by
    intro x hx y hy a b ha hb _
    obtain ⟨α, hα, rfl⟩ := hx
    obtain ⟨β, hβ, rfl⟩ := hy
    refine ⟨fun n i j => a * α n i j + b * β n i j, fun n i j => by
      have := hα n i j; have := hβ n i j; positivity, ?_⟩
    simp only [Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
  have h0 : (0 : EuclideanSpace ℝ (Fin K)) ∈ d.coneSet :=
    ⟨fun _ _ _ => 0, fun _ _ _ => le_rfl, by simp⟩
  have hw : ∀ n i j, d.w n i j ∈ d.coneSet := by
    intro n i j
    classical
    refine ⟨fun n' i' j' => if (⟨n', i', j'⟩ : (n : Fin N) × Fin (d.J n) × Fin (d.J n)) =
      ⟨n, i, j⟩ then 1 else 0, fun _ _ _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
    rw [Finset.sum_eq_single n (fun b _ hb => Finset.sum_eq_zero fun i' _ =>
      Finset.sum_eq_zero fun j' _ => by
        dsimp only; rw [if_neg (by intro e; exact hb (congrArg Sigma.fst e)), zero_smul]) (by simp)]
    rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun j' _ => by
        dsimp only; rw [if_neg (by intro e; simp only [Sigma.mk.inj_iff, heq_eq_eq] at e; exact hb (congrArg Prod.fst e.2)), zero_smul]) (by simp)]
    rw [Finset.sum_eq_single j (fun b _ hb => by
        dsimp only; rw [if_neg (by intro e; simp only [Sigma.mk.inj_iff, heq_eq_eq] at e; exact hb (congrArg Prod.snd e.2)), zero_smul]) (by simp)]
    simp
  have hsep : ∃ γ : EuclideanSpace ℝ (Fin K), γ ≠ 0 ∧
      ∀ n i j, inner ℝ (d.w n i j) γ ≤ 0 := by
    by_cases hne : (interior d.coneSet).Nonempty
    · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior h
      obtain ⟨x, hx⟩ := hne
      refine ⟨(InnerProductSpace.toDual ℝ _).symm f, ?_, ?_⟩
      · intro hz
        have := hf x hx
        have hf0 : f = 0 := by
          have := congrArg (InnerProductSpace.toDual ℝ _) hz
          simpa using this
        simp [hf0] at this
      · intro n i j
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
        have hcl : d.coneSet ⊆ closure (interior d.coneSet) := by
          rw [hconv.closure_interior_eq_closure_of_nonempty_interior ⟨x, hx⟩]
          exact subset_closure
        have : closure (interior d.coneSet) ⊆ {y | f y ≤ 0} := by
          apply closure_minimal
          · intro y hy; have := hf y hy; simp at this ⊢; linarith
          · exact isClosed_le f.continuous continuous_const
        have := this (hcl (hw n i j))
        simpa using this
    · rw [hconv.interior_nonempty_iff_affineSpan_eq_top,
        ← AffineSubspace.direction_eq_top_iff_of_nonempty
          ((affineSpan_nonempty ℝ).2 ⟨0, h0⟩), ← Submodule.orthogonal_eq_bot_iff,
        ← ne_eq, Submodule.ne_bot_iff] at hne
      obtain ⟨γ, hγ, hγ0⟩ := hne
      refine ⟨γ, hγ0, fun n i j => le_of_eq ?_⟩
      have hd : d.w n i j -ᵥ (0 : EuclideanSpace ℝ (Fin K)) ∈
          (affineSpan ℝ d.coneSet).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ (hw n i j))
          (subset_affineSpan ℝ _ h0)
      rw [vsub_eq_sub, sub_zero] at hd
      rw [real_inner_comm]
      exact Submodule.inner_left_of_mem_orthogonal hd hγ
  obtain ⟨γ, hγ, hγw⟩ := hsep
  exact ⟨⟨γ, hγ, hγw⟩, fun h6 => hγ (h6 γ hγw)⟩

theorem goal_core {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) :
    d.Axiom6 ↔
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by
  constructor
  · intro h6
    by_cases hi : (0 : EuclideanSpace ℝ (Fin K)) ∈ interior d.coneSet
    · exact (interior_core d hi).2
    · exact absurd h6 (nonint_core d hi).2
  · rintro ⟨⟨y, hy, hy0⟩, _⟩
    have : y = 0 := by simpa using hy0
    subst this
    exact zmin_core d h5 hy

end McFadden1974.QPTest

open McFadden1974.QPTest


theorem solution {N K : ℕ} (d : ChoiceData N K)
    (h : (0 : EuclideanSpace ℝ (Fin K)) ∈ interior d.coneSet) :
    (∃ α : (n : Fin N) → Fin (d.J n) → Fin (d.J n) → ℝ,
      (∀ n i j, 0 < α n i j) ∧
        (∑ n, ∑ i, ∑ j, α n i j • d.w n i j) = 0) ∧
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by
  exact interior_core d h
