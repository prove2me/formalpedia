-- Prove2me | solution 1 for HyperKCut.Structure.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:19:04.202799+00:00
-- url     : https://prove2.me/submissions/cef33d75-f291-49d0-b052-ceddd37468e2

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Theorems.Thm_HyperKCut_Structure_lemma_3_2
import Theorems.Thm_HyperKCut_Structure_lemma_3_3

open HyperKCut.Structure
namespace HKYWZAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem snoc2_cases {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (q : Finset V → Prop) (i : Fin (p + 2))
    (hY : ∀ j, q (Y j)) (hW : q W) (hZ : q Z) :
    q (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) := by
  induction i using Fin.lastCases with
  | last => simpa using hZ
  | cast i =>
    rw [Fin.snoc_castSucc]
    induction i using Fin.lastCases with
    | last => simpa using hW
    | cast i => rw [Fin.snoc_castSucc]; exact hY i

/-- Basic facts about a partition `(Y₁,…,Yₚ,W,Z)`. -/
theorem ywz_facts {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (h : IsPartitionYWZ Y W Z) :
    (∀ i, (Y i).Nonempty) ∧ W.Nonempty ∧ Z.Nonempty ∧
    (∀ i j, i ≠ j → Disjoint (Y i) (Y j)) ∧
    (∀ i, Disjoint (Y i) W) ∧ (∀ i, Disjoint (Y i) Z) ∧ Disjoint W Z ∧
    (∀ v, (∃ i, v ∈ Y i) ∨ v ∈ W ∨ v ∈ Z) := by
  obtain ⟨hne, hdis, hcov⟩ := h
  have eY : ∀ i, Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.castSucc i)) = Y i := by intro i; simp
  have eW : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.last p)) = W := by simp
  have eZ : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.last (p + 1)) = Z := by simp
  refine ⟨fun i => ?_, ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_, ?_, fun v => ?_⟩
  · have := hne (Fin.castSucc (Fin.castSucc i)); rwa [eY] at this
  · have := hne (Fin.castSucc (Fin.last p)); rwa [eW] at this
  · have := hne (Fin.last (p + 1)); rwa [eZ] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc j))
      (fun h => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ h)))
    rwa [eY, eY] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.last p))
      (fun h => (Fin.castSucc_lt_last i).ne (Fin.castSucc_injective _ h))
    rwa [eY, eW] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.last (p + 1))
      (Fin.castSucc_lt_last _).ne
    rwa [eY, eZ] at this
  · have := hdis (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)) (Fin.castSucc_lt_last _).ne
    rwa [eW, eZ] at this
  · obtain ⟨i, hi⟩ := hcov v
    revert hi
    induction i using Fin.lastCases with
    | last => intro hi; right; right; simpa using hi
    | cast i =>
      rw [Fin.snoc_castSucc]
      induction i using Fin.lastCases with
      | last => intro hi; right; left; simpa using hi
      | cast i => rw [Fin.snoc_castSucc]; intro hi; left; exact ⟨i, hi⟩

end HKYWZAux

namespace HKT31Aux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cost_reindex (H : HyperKCut.Structure.Hypergraph V) {a b : ℕ} (e : Fin a ≃ Fin b)
    (P : Fin b → Finset V) : cost H (P ∘ e) = cost H P := by
  unfold cost
  congr 1
  apply Multiset.filter_congr
  intro x _
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨e i, e j, fun h => hij (e.injective h), hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨e.symm i, e.symm j, fun h => hij (e.symm.injective h), ?_, ?_⟩
    · simpa using hi
    · simpa using hj

theorem partition_reindex {a b : ℕ} (e : Fin a ≃ Fin b) (P : Fin b → Finset V)
    (h : IsPartition P) : IsPartition (P ∘ e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => h1 (e i), fun i j hij => h2 (e i) (e j) (fun h => hij (e.injective h)), ?_⟩
  intro v
  obtain ⟨i, hi⟩ := h3 v
  exact ⟨e.symm i, by simpa using hi⟩

end HKT31Aux

open HKYWZAux HKT31Aux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hUV : U ⊂ (Finset.univ : Finset V))
    (u : Fin p → V) (huinj : Function.Injective u)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j) :
    ∃ P : Fin k → Finset V, IsPartition P ∧
      Uᶜ ⊂ P ⟨k - 1, by omega⟩ ∧
      ∀ i j : Fin p, i ≠ j → 2 * cost H P ≤ d H (A i) + d H (A j) := by
  classical
  have hp2 : 2 ≤ p := by omega
  obtain ⟨hpart, hsig⟩ := lemma_3_2 H p hp2 R U hR hRU hUV u huinj hu A hA hui huj
  set Z : Finset V := Finset.univ.filter (fun v => ∀ i, v ∉ A i) with hZ
  set W : Finset V := Finset.univ.filter
      (fun v => ∃ i j : Fin p, i ≠ j ∧ v ∈ A i ∧ v ∈ A j) with hW
  set Y : Fin p → Finset V := fun i => A i \ W with hY
  obtain ⟨f, hfinj, hf⟩ := lemma_3_3 H k p hk hp Y W Z hpart
  obtain ⟨hYne, hWne, hZne, hYY, hYW, hYZ, hWZ, hcov⟩ := ywz_facts Y W Z hpart
  set Rest : Finset V := (Finset.univ : Finset V) \
    Finset.univ.biUnion (fun j : Fin (k - 1) => Y (f j)) with hRest
  set Pf : Fin (k - 1 + 1) → Finset V :=
    Fin.snoc (α := fun _ => Finset V) (fun j => Y (f j)) Rest with hPf
  have hkk : k = k - 1 + 1 := by omega
  let e : Fin k ≃ Fin (k - 1 + 1) := finCongr hkk
  refine ⟨Pf ∘ e, ?_, ?_, ?_⟩
  · apply partition_reindex
    have hRestZ : Z ⊆ Rest := by
      intro v hv
      rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨j, -, hj⟩
      exact Finset.disjoint_left.mp (hYZ (f j)) hj hv
    refine ⟨?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [hPf, Fin.snoc_last]
        obtain ⟨z, hz⟩ := hZne
        exact ⟨z, hRestZ hz⟩
      | cast i => rw [hPf, Fin.snoc_castSucc]; exact hYne (f i)
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          rw [hPf, Fin.snoc_last, Fin.snoc_castSucc]
          rw [Finset.disjoint_left]
          intro v hv hv'
          rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion] at hv
          exact hv.2 ⟨j, Finset.mem_univ _, hv'⟩
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [hPf, Fin.snoc_last, Fin.snoc_castSucc]
          rw [Finset.disjoint_left]
          intro v hv' hv
          rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion] at hv
          exact hv.2 ⟨i, Finset.mem_univ _, hv'⟩
        | cast j =>
          rw [hPf, Fin.snoc_castSucc, Fin.snoc_castSucc]
          have : i ≠ j := fun h => hij (by rw [h])
          exact hYY (f i) (f j) (fun h => this (hfinj h))
    · intro v
      by_cases hv : v ∈ Finset.univ.biUnion (fun j : Fin (k - 1) => Y (f j))
      · rw [Finset.mem_biUnion] at hv
        obtain ⟨j, -, hj⟩ := hv
        exact ⟨Fin.castSucc j, by rw [hPf, Fin.snoc_castSucc]; exact hj⟩
      · exact ⟨Fin.last _, by
          rw [hPf, Fin.snoc_last, hRest, Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩⟩
  · have hlast : (Pf ∘ e) ⟨k - 1, by omega⟩ = Rest := by
      have : e ⟨k - 1, by omega⟩ = Fin.last (k - 1) := by
        apply Fin.ext
        simp [e]
      simp only [Function.comp, this, hPf, Fin.snoc_last]
    rw [hlast]
    -- Uᶜ ⊆ W ⊆ Rest
    have i0 : Fin p := ⟨0, by omega⟩
    have hUW : Uᶜ ⊆ W := by
      intro v hv
      rw [hW, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_⟩⟩
      · intro h; have := congrArg Fin.val h; simp at this
      · by_contra hn
        exact Finset.disjoint_left.mp (hA ⟨0, by omega⟩).1.2 (Finset.mem_compl.mpr hn) hv
      · by_contra hn
        exact Finset.disjoint_left.mp (hA ⟨1, by omega⟩).1.2 (Finset.mem_compl.mpr hn) hv
    have hWRest : W ⊆ Rest := by
      intro v hv
      rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨j, -, hj⟩
      exact Finset.disjoint_left.mp (hYW (f j)) hj hv
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hUW.trans hWRest, ?_⟩
    obtain ⟨r, hr⟩ := hR
    have hrU : r ∈ U := hRU.1 hr
    have hrZ : r ∈ Z := by
      rw [hZ, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i hri => ?_⟩
      have hsrc : r ∈ ((Finset.univ.image u) ∪ R).erase (u i) := by
        rw [Finset.mem_erase]
        refine ⟨fun h => ?_, Finset.mem_union_right _ hr⟩
        have := (Finset.mem_sdiff.mp (hu i)).2
        rw [← h] at this
        exact this hr
      exact (Finset.mem_compl.mp ((hA i).1.1 hsrc)) hri
    intro heq
    have hrR : r ∈ Rest := by
      rw [hRest, Finset.mem_sdiff, Finset.mem_biUnion]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨j, -, hj⟩
      exact Finset.disjoint_left.mp (hYZ (f j)) hj hrZ
    rw [← heq] at hrR
    exact (Finset.mem_compl.mp hrR) hrU
  · intro i j hij
    rw [cost_reindex]
    have h1 := hsig i j hij
    unfold sigma at h1
    have h2 : 2 * cost H Pf ≤ costYWZ H Y W Z + alpha H Y W Z + beta H Y Z := hf
    omega
