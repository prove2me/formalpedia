-- Prove2me | solution 1 for MonotoneCompStatics.Monotonicity.corollary1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:30:14.037232+00:00
-- url     : https://prove2.me/submissions/25c0feee-92e3-4aa2-a16b-d967e1f71ef3

import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
import Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing

open MonotoneCompStatics.Monotonicity Supermodularity.Lattices

private lemma pair_max {X : Type*} (g : X → ℝ) (a b : X) (h : g b ≤ g a) :
    a ∈ argmaxOn g ({a, b} : Set X) := by
  refine ⟨by simp, ?_⟩
  intro z hz
  rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
  · exact le_rfl
  · exact h

private lemma pair_order {X : Type*} [Lattice X] (x y : X) :
    InducedSetOrder ({x ⊓ y, x} : Set X) {y, x ⊔ y} := by
  intro a ha b hb
  have ha' : a = x ⊓ y ∨ a = x := by simpa using ha
  have hb' : b = y ∨ b = x ⊔ y := by simpa using hb
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    simp [inf_assoc, inf_left_comm, inf_comm, sup_assoc, sup_left_comm, sup_comm]

private lemma qsm_necessary {X : Type*} [Lattice X] (g : X → ℝ)
    (hm : ∀ ⦃A B : Set X⦄, InducedSetOrder A B →
      InducedSetOrder (argmaxOn g A) (argmaxOn g B)) :
    QuasiSupermodularOn g Set.univ := by
  intro x hx y hy
  constructor
  · intro h
    by_contra hn
    have hb := pair_max g y (x ⊔ y) (le_of_lt (lt_of_not_ge hn))
    have ha : x ∈ argmaxOn g ({x ⊓ y, x} : Set X) := by
      simpa [Set.pair_comm] using pair_max g x (x ⊓ y) h
    have hj := (hm (pair_order x y) ha hb).2
    have hh := hj.2 y (by simp)
    exact hn hh
  · intro h
    by_contra hn
    have hb := pair_max g y (x ⊔ y) (le_of_not_gt hn)
    have ha : x ∈ argmaxOn g ({x ⊓ y, x} : Set X) := by
      simpa [Set.pair_comm] using pair_max g x (x ⊓ y) (le_of_lt h)
    have hh := (hm (pair_order x y) ha hb).1
    have hh' := hh.2 x (by simp)
    exact (not_le_of_gt h) hh'

private lemma sc_weak {X T : Type*} [PartialOrder X] [PartialOrder T]
    {f : X → T → ℝ} (h : SingleCrossing f)
    {x y : X} {t u : T} (hxy : x ≤ y) (htu : t ≤ u)
    (hf : f x t ≤ f y t) : f x u ≤ f y u := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  rcases eq_or_lt_of_le htu with rfl | htu
  · exact hf
  exact (h hxy htu).2 hf

private lemma sc_strict {X T : Type*} [PartialOrder X] [PartialOrder T]
    {f : X → T → ℝ} (h : SingleCrossing f)
    {x y : X} {t u : T} (hxy : x ≤ y) (htu : t ≤ u)
    (hf : f x t < f y t) : f x u < f y u := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact (lt_irrefl _ hf).elim
  rcases eq_or_lt_of_le htu with rfl | htu
  · exact hf
  exact (h hxy htu).1 hf

private lemma sufficient {X T : Type*} [Lattice X] [PartialOrder T]
    (f : X → T → ℝ)
    (hq : ∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ)
    (hsc : SingleCrossing f) : ArgmaxMonotone f := by
  intro t u A B htu hAB a ha b hb
  have hm := (hAB ha.1 hb.1).1
  have hj := (hAB ha.1 hb.1).2
  have hma := ha.2 (a ⊓ b) hm
  have hbj := (hq t (Set.mem_univ a) (Set.mem_univ b)).1 hma
  have hbj' := sc_weak hsc le_sup_right htu hbj
  have hjb := hb.2 (a ⊔ b) hj
  have ham : f a t ≤ f (a ⊓ b) t := by
    by_contra hn
    have hlt := (hq t (Set.mem_univ a) (Set.mem_univ b)).2 (lt_of_not_ge hn)
    have hlt' := sc_strict hsc le_sup_right htu hlt
    exact (not_lt_of_ge hjb) hlt'
  exact ⟨⟨hm, fun z hz => (ha.2 z hz).trans ham⟩,
    ⟨hj, fun z hz => (hb.2 z hz).trans hbj'⟩⟩

private lemma sc_necessary {X T : Type*} [Lattice X] [PartialOrder T]
    (f : X → T → ℝ) (hm : ArgmaxMonotone f) : SingleCrossing f := by
  intro y x hxy u t htu
  have hS : InducedSetOrder ({x, y} : Set X) {x, y} := by
    intro a ha b hb
    have ha' : a = x ∨ a = y := by simpa using ha
    have hb' : b = x ∨ b = y := by simpa using hb
    rcases ha' with rfl | rfl <;>
      rcases hb' with rfl | rfl <;>
      simp [inf_eq_left.mpr hxy.le, inf_eq_right.mpr hxy.le,
        sup_eq_left.mpr hxy.le, sup_eq_right.mpr hxy.le]
  constructor
  · intro hf
    by_contra hn
    have ha : y ∈ argmaxOn (fun z => f z t) ({x, y} : Set X) := by
      simpa [Set.pair_comm] using pair_max (fun z => f z t) y x hf.le
    have hb := pair_max (fun z => f z u) x y (le_of_not_gt hn)
    have hh := (hm htu.le hS ha hb).1
    have hh' : f y t ≤ f x t := by
      simpa [inf_eq_right.mpr hxy.le] using hh.2 y (by simp)
    exact (not_le_of_gt hf) hh'
  · intro hf
    by_contra hn
    have ha : y ∈ argmaxOn (fun z => f z t) ({x, y} : Set X) := by
      simpa [Set.pair_comm] using pair_max (fun z => f z t) y x hf
    have hb := pair_max (fun z => f z u) x y (le_of_lt (lt_of_not_ge hn))
    have hh := (hm htu.le hS ha hb).2
    have hh' : f x u ≤ f y u := by
      simpa [sup_eq_left.mpr hxy.le] using hh.2 x (by simp)
    exact hn hh'

theorem solution {X : Type*} [Lattice X] (g : X → ℝ) :
    QuasiSupermodularOn g Set.univ ↔
      ∀ ⦃S S' : Set X⦄, Supermodularity.Lattices.InducedSetOrder S S' →
        Supermodularity.Lattices.InducedSetOrder (argmaxOn g S) (argmaxOn g S') := by
  constructor
  · intro hq
    have hm := sufficient (fun x (_ : Unit) => g x) (fun _ => hq) (by
      intro y x hxy u t htu
      exact (lt_irrefl t (by simpa using htu)).elim)
    exact fun A B h => hm (t := ()) (t' := ()) le_rfl h
  · exact qsm_necessary g

#print axioms solution
