-- Prove2me | solution 1 for HallReps.CDR.lemma_cdrMeet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:55.012155+00:00
-- url     : https://prove2.me/submissions/dae23355-5f25-439d-9766-6eb0c7e0e871

import Mathlib
import Definitions.Def_HallReps_CDR_System
import Theorems.Thm_HallReps_CDR_theorem1_hall

set_option autoImplicit false

open HallReps.CDR

namespace HallPkMeet

/-- If `a i` lies in every C.D.R., then every element of `T i` lies in every C.D.R. -/
theorem pk_key {ι α : Type*} [Finite ι] (T : ι → Set α) (a : ι → α) (ha : IsCDR T a)
    (i : ι) (hi : a i ∈ cdrMeet T) : T i ⊆ cdrMeet T := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- delete `a i` from every set
  let T' : ι → Set α := fun j => T j \ {a i}
  have hno : ¬ ∃ c : ι → α, IsCDR T' c := by
    rintro ⟨c, hcinj, hcmem⟩
    have hcdr : IsCDR T c := ⟨hcinj, fun j => (hcmem j).1⟩
    obtain ⟨j, hj⟩ := hi c hcdr
    exact (hcmem j).2 hj
  have hfail : ¬ HallCondition T' := fun h => hno (HallReps.CDR.theorem1_hall T' h)
  simp only [HallCondition, not_forall, not_le] at hfail
  obtain ⟨s, hs⟩ := hfail
  set U : Set α := ⋃ j ∈ s, T j with hUdef
  have hU' : (⋃ j ∈ s, T' j) = U \ {a i} := by
    ext x
    simp only [T', hUdef, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨j, hj, hxj, hx⟩
      exact ⟨⟨j, hj, hxj⟩, hx⟩
    · rintro ⟨⟨j, hj, hxj⟩, hx⟩
      exact ⟨j, hj, hxj, hx⟩
  rw [hU'] at hs
  -- the image of `s` under any C.D.R. is a subset of `U` with `s.card` elements
  have himg : ∀ c : ι → α, IsCDR T c → c '' (s : Set ι) ⊆ U ∧
      (c '' (s : Set ι)).encard = (s.card : ℕ∞) := by
    intro c hc
    refine ⟨?_, ?_⟩
    · rintro _ ⟨j, hj, rfl⟩
      exact Set.mem_biUnion hj (hc.2 j)
    · rw [hc.1.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard]
  obtain ⟨haU, hacard⟩ := himg a ha
  -- `a i ∈ U`
  have hiU : a i ∈ U := by
    by_contra hnot
    have : U \ {a i} = U := Set.sdiff_singleton_eq_self hnot
    rw [this] at hs
    exact absurd (hacard ▸ Set.encard_le_encard haU) (not_le.mpr hs)
  -- `U` has at most `s.card` elements
  have hUle : U.encard ≤ (s.card : ℕ∞) := by
    have h1 : U.encard ≤ (U \ {a i}).encard + 1 := by
      calc U.encard = (insert (a i) (U \ {a i})).encard := by rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hiU]
        _ ≤ (U \ {a i}).encard + 1 := Set.encard_insert_le _ _
    have h2 : (U \ {a i}).encard + 1 ≤ (s.card : ℕ∞) := Order.add_one_le_of_lt hs
    exact h1.trans h2
  have hUfin : U.Finite := Set.finite_of_encard_le_coe hUle
  -- every C.D.R. maps `s` onto `U`
  have honto : ∀ c : ι → α, IsCDR T c → c '' (s : Set ι) = U := by
    intro c hc
    obtain ⟨hcU, hccard⟩ := himg c hc
    exact Set.Finite.eq_of_subset_of_encard_le (s.finite_toSet.image c) hcU (by rw [hccard]; exact hUle)
  have hUR : U ⊆ cdrMeet T := by
    intro x hx c hc
    rw [← honto c hc] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact ⟨j, rfl⟩
  -- `i ∈ s`
  have his : i ∈ s := by
    have : a i ∈ a '' (s : Set ι) := by rw [honto a ha]; exact hiU
    obtain ⟨j, hj, hji⟩ := this
    have : j = i := ha.1 hji
    exact this ▸ hj
  exact (Set.subset_biUnion_of_mem (u := T) (by exact_mod_cast his : i ∈ (s : Set ι))).trans hUR

end HallPkMeet

theorem solution {ι α : Type*} [Finite ι] (T : ι → Set α) (a : ι → α)
    (ha : IsCDR T a) :
    (⋃ (i : ι) (_ : a i ∈ cdrMeet T), T i) = cdrMeet T ∧
      (cdrMeet T).encard = ENat.card {i : ι // a i ∈ cdrMeet T} := by
  have hRa : ∀ x ∈ cdrMeet T, x ∈ Set.range a := fun x hx => hx a ha
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro y hy
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨i, hi, hyi⟩ := hy
      exact HallPkMeet.pk_key T a ha i hi hyi
    · intro x hx
      obtain ⟨i, rfl⟩ := hRa x hx
      exact Set.mem_biUnion hx (ha.2 i)
  · -- `i ↦ a i` is a bijection `{i // a i ∈ R} → R`
    have hbij : Function.Bijective (fun i : {i : ι // a i ∈ cdrMeet T} => (⟨a i.1, i.2⟩ : cdrMeet T)) := by
      constructor
      · intro i j hij
        exact Subtype.ext (ha.1 (congrArg Subtype.val hij))
      · rintro ⟨x, hx⟩
        obtain ⟨i, rfl⟩ := hRa x hx
        exact ⟨⟨i, hx⟩, rfl⟩
    exact (ENat.card_congr (Equiv.ofBijective _ hbij)).symm

#print axioms solution
