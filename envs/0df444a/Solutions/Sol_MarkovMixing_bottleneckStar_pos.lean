-- Prove2me | solution 1 for MarkovMixing.bottleneckStar_pos
-- status  : ACCEPTED   (prove)
-- author  : @steven
-- created : 2026-08-22T22:25:38.296796+00:00
-- url     : https://prove2.me/submissions/af567f5b-4114-4ade-bdc3-a5d5453c6d36

import Definitions.Def_mm_martingale
import Mathlib.Tactic

open scoped BigOperators
open MarkovMixing

namespace MarkovMixingX

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
      intro x y
      by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

private lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

private lemma stationary_pos {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ x : V, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    linarith [hπ.1.2]
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have hsingle : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  nlinarith [mul_pos hy ht]

private lemma cut_flow_pos (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (S : Finset V) (hSne : S.Nonempty) (hScne : Sᶜ.Nonempty) :
    0 < ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y := by
  classical
  have hpos := stationary_pos hP hirr hπ
  have hedge0 : ∀ x y : V, 0 ≤ edgeMeasure P π x y :=
    fun x y => mul_nonneg (hpos x).le (hP.1 x y)
  let Q : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hedge0 x y
  by_contra hnpos
  have hQ : Q = 0 := le_antisymm (not_lt.mp hnpos) hQ0
  have hcross : ∀ x ∈ S, ∀ y ∈ Sᶜ, P x y = 0 := by
    intro x hx y hy
    have hxy_le_inner : edgeMeasure P π x y ≤ ∑ z ∈ Sᶜ, edgeMeasure P π x z :=
      Finset.single_le_sum (fun z _ => hedge0 x z) hy
    have hinner0 : 0 ≤ ∑ z ∈ Sᶜ, edgeMeasure P π x z :=
      Finset.sum_nonneg fun z _ => hedge0 x z
    have hinner_le : (∑ z ∈ Sᶜ, edgeMeasure P π x z) ≤ Q := by
      exact Finset.single_le_sum
        (fun z _ => Finset.sum_nonneg fun w _ => hedge0 z w) hx
    have hedge : edgeMeasure P π x y = 0 := by
      have : edgeMeasure P π x y ≤ 0 := by simpa [hQ] using hxy_le_inner.trans hinner_le
      exact le_antisymm this (hedge0 x y)
    simp only [edgeMeasure] at hedge
    exact (mul_eq_zero.mp hedge).resolve_left (ne_of_gt (hpos x))
  obtain ⟨a, ha⟩ := hSne
  obtain ⟨b, hb⟩ := hScne
  have hpzero : ∀ t : ℕ, ∀ x ∈ S, ∀ y ∈ Sᶜ, (P ^ t) x y = 0 := by
    intro t
    induction t with
    | zero =>
        intro x hx y hy
        have hxy : x ≠ y := by
          intro h
          subst y
          exact (Finset.mem_compl.mp hy) hx
        simp [Matrix.one_apply, hxy]
    | succ t ih =>
        intro x hx y hy
        rw [pow_succ, Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro z _
        by_cases hz : z ∈ S
        · rw [hcross z hz y hy, mul_zero]
        · have hzc : z ∈ Sᶜ := Finset.mem_compl.mpr hz
          rw [ih x hx z hzc, zero_mul]
  obtain ⟨t, ht⟩ := hirr a b
  rw [hpzero t a ha b hb] at ht
  exact (lt_irrefl 0 ht)

end MarkovMixingX

/-- A finite irreducible chain on at least two states has strictly positive
bottleneck constant. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    0 < bottleneckStar P π := by
  classical
  have hpos := MarkovMixingX.stationary_pos hP hirr hπ
  let I := {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ (2 : ℝ)⁻¹}
  have hI : Nonempty I := by
    obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ (2 : ℝ)⁻¹ := by
      by_contra hcon
      push_neg at hcon
      have hcard : 1 < Fintype.card V := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have hpairsum : π x + π y ≤ ∑ z, π z := by
        calc
          π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := (Finset.sum_pair hxy).symm
          _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun i _ _ => (hpos i).le)
      linarith [hcon x, hcon y, hπ.1.2]
    exact ⟨⟨{x}, Finset.singleton_nonempty x, by simpa using hx⟩⟩
  let ratio : I → ℝ := fun S => bottleneckRatio P π S.1
  have hratio : ∀ S : I, 0 < ratio S := by
    intro S
    obtain ⟨T, hTne, hThalf⟩ := S
    have hTcne : Tᶜ.Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      have hTuniv : T = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        by_contra hx
        have hxc : x ∈ Tᶜ := Finset.mem_compl.mpr hx
        rw [hc] at hxc
        simpa using hxc
      rw [hTuniv] at hThalf
      have : ∑ x : V, π x = 1 := hπ.1.2
      norm_num [this] at hThalf
    have hnum := MarkovMixingX.cut_flow_pos P hP hirr π hπ T hTne hTcne
    have hden : 0 < ∑ x ∈ T, π x := by
      obtain ⟨x, hx⟩ := hTne
      have hle := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith [hpos x]
    exact div_pos hnum hden
  let vals : Finset ℝ := Finset.univ.image ratio
  have hvals : vals.Nonempty := by
    let S : I := Classical.choice hI
    exact ⟨ratio S, Finset.mem_image.mpr ⟨S, Finset.mem_univ S, rfl⟩⟩
  let m : ℝ := vals.min' hvals
  have hm_mem : m ∈ vals := Finset.min'_mem vals hvals
  obtain ⟨Smin, -, hSmin⟩ := Finset.mem_image.mp hm_mem
  have hmpos : 0 < m := by simpa [hSmin] using hratio Smin
  have hmle : ∀ S : I, m ≤ ratio S := by
    intro S
    exact Finset.min'_le vals (ratio S) (Finset.mem_image.mpr ⟨S, Finset.mem_univ S, rfl⟩)
  have hbdd : BddBelow (Set.range ratio) := ⟨0, by rintro _ ⟨S, rfl⟩; exact (hratio S).le⟩
  have hinf : (⨅ S : I, ratio S) = m := by
    apply le_antisymm
    · have hle := ciInf_le hbdd Smin
      linarith [hSmin]
    · exact le_ciInf hmle
  change 0 < ⨅ S : I, ratio S
  rw [hinf]
  exact hmpos
