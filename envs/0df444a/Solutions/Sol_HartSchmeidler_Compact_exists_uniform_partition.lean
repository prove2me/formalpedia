-- Prove2me | solution 1 for HartSchmeidler.Compact.exists_uniform_partition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:30:02.345381+00:00
-- url     : https://prove2.me/submissions/932919cf-0b20-43f7-9c01-f4a4c3ce63c5

import Definitions.Def_HartSchmeidler_Compact_Game



namespace HartSchmeidler.Compact

open MeasureTheory

theorem eup_core {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (A : Fin K → Set (S i)),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, (A k).Nonempty) ∧ Pairwise (Function.onFun Disjoint A) ∧
        (⋃ k, A k) = Set.univ ∧
        ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, ∀ s : Profile S,
          |h i (Function.update s i a) - h i (Function.update s i b)| < ε := by
  classical
  -- the curried map
  have hΦ : Continuous (fun q : S i × Profile S => h i (Function.update q.2 i q.1)) := by
    apply (hcont i).comp
    show Continuous (fun q : S i × (∀ j, S j) => Function.update q.2 i q.1)
    exact Continuous.update continuous_snd i continuous_fst
  let g : C(S i, C(Profile S, ℝ)) := ContinuousMap.curry ⟨_, hΦ⟩
  have hK : IsCompact (Set.range g) := isCompact_range g.continuous
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := ε / 2) (by linarith)
  have : Fintype t := htf.fintype
  let n := Fintype.card t
  let x : Fin n → C(Profile S, ℝ) := fun k => ((Fintype.equivFin t).symm k).1
  let U : Fin n → Set (S i) := fun k => g ⁻¹' Metric.ball (x k) (ε / 2)
  have hUo : ∀ k, IsOpen (U k) := fun k => Metric.isOpen_ball.preimage g.continuous
  have hUcov : (⋃ k, U k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    have := hcov ⟨a, rfl⟩
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hay⟩ := this
    refine Set.mem_iUnion.2 ⟨Fintype.equivFin t ⟨y, hy⟩, ?_⟩
    simpa [U, x] using hay
  let V : Fin n → Set (S i) := disjointed U
  have hVm : ∀ k, MeasurableSet (V k) := fun k => by
    show MeasurableSet (disjointed U k)
    rw [disjointed_apply]
    refine (hUo k).measurableSet.diff ?_
    rw [Finset.sup_set_eq_biUnion]
    exact Finset.measurableSet_biUnion _ fun j _ => (hUo j).measurableSet
  have hVd : Pairwise (Function.onFun Disjoint V) := disjoint_disjointed U
  have hVu : (⋃ k, V k) = Set.univ := by rw [iUnion_disjointed, hUcov]
  have hVU : ∀ k, V k ⊆ U k := disjointed_subset U
  let P : Set (Fin n) := {k | (V k).Nonempty}
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  refine ⟨Fintype.card P, fun j => V (e.symm j).1, fun j => hVm _, fun j => (e.symm j).2, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply hVd
    intro heq
    apply hjj'
    have : e.symm j = e.symm j' := Subtype.ext heq
    exact e.symm.injective this
  · apply Set.eq_univ_of_forall
    intro a
    have : a ∈ ⋃ k, V k := by rw [hVu]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    refine Set.mem_iUnion.2 ⟨e ⟨k, ⟨a, hk⟩⟩, ?_⟩
    simpa using hk
  · intro j a ha b hb s
    have ha' := hVU _ ha
    have hb' := hVU _ hb
    have hd : dist (g a) (g b) < ε := by
      calc dist (g a) (g b) ≤ dist (g a) (x (e.symm j).1) + dist (g b) (x (e.symm j).1) := by
            rw [dist_comm (g b)]; exact dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add ha' hb'
        _ = ε := by ring
    have := ContinuousMap.dist_apply_le_dist (f := g a) (g := g b) s
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this hd

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (A : Fin K → Set (S i)),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, (A k).Nonempty) ∧ Pairwise (Function.onFun Disjoint A) ∧
        (⋃ k, A k) = Set.univ ∧
        ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, ∀ s : Profile S,
          |h i (Function.update s i a) - h i (Function.update s i b)| < ε := by
  exact eup_core h hcont i ε hε
