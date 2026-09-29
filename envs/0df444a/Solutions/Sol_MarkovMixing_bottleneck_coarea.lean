-- Prove2me | solution 1 for MarkovMixing.bottleneck_coarea
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:53:02.416069+00:00
-- url     : https://prove2.me/submissions/7bd5171f-08e4-4d85-9fc5-898b4a59e836

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace Coarea

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end Coarea

open Coarea

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π)
    (ψ : V → ℝ) (hψ : ∀ x : V, 0 ≤ ψ x)
    (hsupp : ∑ x ∈ Finset.univ.filter (fun x : V => 0 < ψ x), π x ≤ 2⁻¹) :
    MarkovMixing.bottleneckStar P π * MarkovMixing.distExp π ψ ≤
      ∑ x, ∑ y, max (ψ x - ψ y) 0 * MarkovMixing.edgeMeasure P π x y := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hQnn : ∀ x y : V, 0 ≤ MarkovMixing.edgeMeasure P π x y := fun x y =>
    mul_nonneg (hpos x).le (hP.1 x y)
  -- Φ⋆ is bounded above by the ratio of any admissible set
  have hbdd : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
      MarkovMixing.bottleneckRatio P π S.1) := by
    refine ⟨0, ?_⟩
    rintro b ⟨S, rfl⟩
    refine div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y) ?_
    exact Finset.sum_nonneg fun x _ => (hpos x).le
  have hcut : ∀ S : Finset V, S.Nonempty → (∑ x ∈ S, π x) ≤ 2⁻¹ →
      MarkovMixing.bottleneckStar P π * (∑ x ∈ S, π x)
        ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
    intro S hSne hShalf
    have hppos : 0 < ∑ x ∈ S, π x := by
      obtain ⟨x, hx⟩ := hSne
      have h1 : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    have h1 : MarkovMixing.bottleneckStar P π ≤ MarkovMixing.bottleneckRatio P π S :=
      ciInf_le hbdd ⟨S, hSne, hShalf⟩
    rw [MarkovMixing.bottleneckRatio, div_eq_mul_inv] at h1
    calc MarkovMixing.bottleneckStar P π * (∑ x ∈ S, π x)
        ≤ ((∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y) * (∑ x ∈ S, π x)⁻¹)
            * (∑ x ∈ S, π x) := by
          exact mul_le_mul_of_nonneg_right h1 hppos.le
      _ = ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
          field_simp
  -- strong induction on the size of the support
  suffices H : ∀ n : ℕ, ∀ φ : V → ℝ, (∀ x, 0 ≤ φ x) →
      (Finset.univ.filter (fun x : V => 0 < φ x)).card ≤ n →
      (∑ x ∈ Finset.univ.filter (fun x : V => 0 < φ x), π x) ≤ 2⁻¹ →
      MarkovMixing.bottleneckStar P π * MarkovMixing.distExp π φ ≤
        ∑ x, ∑ y, max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y by
    exact H _ ψ hψ le_rfl hsupp
  intro n
  induction n with
  | zero =>
    intro φ hφ hcard _
    have hzero : ∀ x : V, φ x = 0 := by
      intro x
      by_contra hx
      have : x ∈ Finset.univ.filter (fun x : V => 0 < φ x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne (hφ x) (Ne.symm hx)
      have := Finset.card_pos.mpr ⟨x, this⟩
      omega
    have hL : MarkovMixing.distExp π φ = 0 := by
      show ∑ x, φ x * π x = 0
      exact Finset.sum_eq_zero fun x _ => by rw [hzero x]; ring
    rw [hL, mul_zero]
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    exact mul_nonneg (le_max_right _ _) (hQnn x y)
  | succ n ih =>
    intro φ hφ hcard hsupp'
    set S : Finset V := Finset.univ.filter (fun x : V => 0 < φ x) with hS_def
    by_cases hSne : S.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := S.exists_min_image φ hSne
      set a : ℝ := φ x0 with ha_def
      have hapos : 0 < a := by
        have := Finset.mem_filter.mp hx0
        exact this.2
      set φ' : V → ℝ := fun x => max (φ x - a) 0 with hφ'_def
      have hφ'nn : ∀ x, 0 ≤ φ' x := fun x => le_max_right _ _
      have hmem : ∀ x : V, x ∈ S ↔ 0 < φ x := by
        intro x; rw [hS_def]; simp
      have hzero : ∀ x : V, x ∉ S → φ x = 0 := by
        intro x hx
        rcases lt_or_eq_of_le (hφ x) with h | h
        · exact absurd ((hmem x).mpr h) hx
        · exact h.symm
      have hge : ∀ x ∈ S, a ≤ φ x := fun x hx => hmin x hx
      have hφ'S : ∀ x ∈ S, φ' x = φ x - a := by
        intro x hx
        rw [hφ'_def]
        exact max_eq_left (by linarith [hge x hx])
      have hφ'out : ∀ x : V, x ∉ S → φ' x = 0 := by
        intro x hx
        have hd : φ' x = max (φ x - a) 0 := rfl
        rw [hd, hzero x hx]
        exact max_eq_right (by linarith)
      -- support of φ' shrinks
      have hsub : Finset.univ.filter (fun x : V => 0 < φ' x) ⊆ S.erase x0 := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hxS : x ∈ S := by
          by_contra hc
          rw [hφ'out x hc] at hx
          exact lt_irrefl 0 hx
        rw [hφ'S x hxS] at hx
        refine Finset.mem_erase.mpr ⟨?_, hxS⟩
        intro hc
        rw [hc] at hx
        simp [ha_def] at hx
      have hcard' : (Finset.univ.filter (fun x : V => 0 < φ' x)).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hx0] at h1
        have h2 : 1 ≤ S.card := Finset.card_pos.mpr hSne
        omega
      have hsupp'' : (∑ x ∈ Finset.univ.filter (fun x : V => 0 < φ' x), π x) ≤ 2⁻¹ := by
        refine le_trans ?_ hsupp'
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (hpos i).le)
        exact hsub.trans (Finset.erase_subset _ _)
      have IH := ih φ' hφ'nn hcard' hsupp''
      -- decomposition of the mean
      have hexp : MarkovMixing.distExp π φ = MarkovMixing.distExp π φ' + a * ∑ x ∈ S, π x := by
        have hA : ∑ x, φ x * π x = (∑ x ∈ S, φ x * π x) + ∑ x ∈ Sᶜ, φ x * π x :=
          (Finset.sum_add_sum_compl S _).symm
        have hB : ∑ x, φ' x * π x = (∑ x ∈ S, φ' x * π x) + ∑ x ∈ Sᶜ, φ' x * π x :=
          (Finset.sum_add_sum_compl S _).symm
        have e1 : ∑ x ∈ S, φ x * π x = (∑ x ∈ S, φ' x * π x) + a * ∑ x ∈ S, π x := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x hx => by rw [hφ'S x hx]; ring
        have e2 : ∑ x ∈ Sᶜ, φ x * π x = ∑ x ∈ Sᶜ, φ' x * π x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.mem_compl] at hx
          rw [hzero x hx, hφ'out x hx]
        show ∑ x, φ x * π x = (∑ x, φ' x * π x) + a * ∑ x ∈ S, π x
        rw [hA, hB, e1, e2]
        ring
      -- pointwise comparison of the edge terms
      have hpair : ∀ x y : V,
          max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
            + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
          ≤ max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y := by
        intro x y
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'S x hx, hφ'S y hy]
          have e : φ x - a - (φ y - a) = φ x - φ y := by ring
          rw [e]
        · rw [if_pos ⟨hx, hy⟩, hφ'S x hx, hφ'out y hy, hzero y hy]
          have h1 : max (φ x - a - 0) 0 = φ x - a := by
            rw [sub_zero]; exact max_eq_left (by linarith [hge x hx])
          have h2 : max (φ x - 0) 0 = φ x := by
            rw [sub_zero]; exact max_eq_left (hφ x)
          rw [h1, h2]
          have e : (φ x - a) * MarkovMixing.edgeMeasure P π x y
              + a * MarkovMixing.edgeMeasure P π x y
              = φ x * MarkovMixing.edgeMeasure P π x y := by ring
          rw [e]
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'out x hx, hzero x hx, hφ'S y hy]
          have h1 : max (0 - (φ y - a)) 0 = 0 := max_eq_right (by linarith [hge y hy])
          have h2 : max (0 - φ y) 0 = 0 := max_eq_right (by linarith [(hmem y).mp hy])
          rw [h1, h2]
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'out x hx, hφ'out y hy, hzero x hx,
            hzero y hy]
      -- the indicator sum is the cut
      have hind : ∑ x, ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
          = ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have h1 : ∀ x : V, ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
            = if x ∈ S then ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y else 0 := by
          intro x
          by_cases hx : x ∈ S
          · simp only [hx, true_and, if_true]
            rw [← Finset.sum_filter]
            congr 1
            ext y
            simp [Finset.mem_compl]
          · simp [hx]
        rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.sum_filter]
        congr 1
        ext x
        simp
      have hsum : ∑ x, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
          + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
          ≤ ∑ x, ∑ y, max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
      have hsplit : ∑ x, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
          + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
          = (∑ x, ∑ y, max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y)
            + a * ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have e : ∀ x : V, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
            + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
            = (∑ y, max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y)
              + a * ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0) := by
          intro x
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, ← Finset.mul_sum, hind]
      have hcutS := hcut S hSne hsupp'
      rw [hexp, mul_add]
      have hstar : MarkovMixing.bottleneckStar P π * (a * ∑ x ∈ S, π x)
          ≤ a * ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have : MarkovMixing.bottleneckStar P π * (a * ∑ x ∈ S, π x)
            = a * (MarkovMixing.bottleneckStar P π * ∑ x ∈ S, π x) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hcutS hapos.le
      rw [hsplit] at hsum
      linarith
    · -- empty support
      have hzero : ∀ x : V, φ x = 0 := by
        intro x
        rcases lt_or_eq_of_le (hφ x) with h | h
        · exact absurd ⟨x, by rw [hS_def]; simp [h]⟩ hSne
        · exact h.symm
      have hL : MarkovMixing.distExp π φ = 0 := by
        show ∑ x, φ x * π x = 0
        exact Finset.sum_eq_zero fun x _ => by rw [hzero x]; ring
      rw [hL, mul_zero]
      refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
      exact mul_nonneg (le_max_right _ _) (hQnn x y)
