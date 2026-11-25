-- Prove2me | solution 1 for IsCompact.convexHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:38.937297+00:00
-- url     : https://prove2.me/submissions/116bdf24-313e-4150-9cdd-7e0b407259d6

module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_BasicResults_CompactConvexHull
public import Theorems.Thm_isCompact_convexWeights

set_option autoImplicit true
@[expose] public section
public section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace IsCompact
theorem _root_.solution {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simp only [convexHull_empty]; exact isCompact_empty
  have hK : IsCompact ({w : Fin (Module.finrank ℝ E + 1) → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} ×ˢ
      Set.univ.pi fun _ : Fin (Module.finrank ℝ E + 1) => s) :=
    (isCompact_convexWeights _).prod (isCompact_univ_pi fun _ => hs)
  have hcont : Continuous
      (fun p : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E) =>
        ∑ i, p.1 i • p.2 i) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  refine (congrArg IsCompact ?_).mpr (hK.image hcont)
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, hfin, z, w, hzs, hai, hw0, hw1, hxeq⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let : Fintype ι := hfin
      -- Carathéodory: affinely independent families have at most `finrank + 1` members.
      have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
        le_trans hai.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      -- embed the index type into `Fin (finrank + 1)`
      set f : ι → Fin (Module.finrank ℝ E + 1) :=
        fun j => Fin.castLE hcard ((Fintype.equivFin ι) j) with hf
      have hfinj : Function.Injective f := by
        intro a b hab
        have h2 := congrArg Fin.val hab
        simp only [hf, Fin.val_castLE] at h2
        exact (Fintype.equivFin ι).injective (Fin.ext h2)
      -- pad the family by weight-0 copies of a fixed point of `s`
      set w' : Fin (Module.finrank ℝ E + 1) → ℝ :=
        fun i => if h : ∃ j, f j = i then w h.choose else 0 with hw'
      set z' : Fin (Module.finrank ℝ E + 1) → E :=
        fun i => if h : ∃ j, f j = i then z h.choose else x₀ with hz'
      have hchoose : ∀ (j : ι) (h : ∃ j', f j' = f j), h.choose = j :=
        fun j h => hfinj h.choose_spec
      have hw'f : ∀ j, w' (f j) = w j := fun j => by
        simp only [hw']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hz'f : ∀ j, z' (f j) = z j := fun j => by
        simp only [hz']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hw'zero : ∀ i, i ∉ Finset.univ.image f → w' i = 0 := fun i hi => by
        simp only [hw']
        exact dif_neg fun h =>
          hi (Finset.mem_image.mpr ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩)
      have hw'sum : ∑ i, w' i = 1 := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => hw'zero i hi]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => hw'f j]
        exact hw1
      have hsum : ∑ i, w' i • z' i = x := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => by rw [hw'zero i hi, zero_smul]]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => by rw [hw'f j, hz'f j]]
        exact hxeq
      refine ⟨(w', z'), ⟨⟨fun i => ?_, hw'sum⟩, Set.mem_univ_pi.mpr fun i => ?_⟩, hsum⟩
      · simp only [hw']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact (hw0 _).le
        · rw [dif_neg h]
      · simp only [hz']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact hzs (Set.mem_range_self _)
        · rw [dif_neg h]; exact hx₀
    · rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
        (fun i => hz i (Set.mem_univ i)) rfl
end IsCompact
