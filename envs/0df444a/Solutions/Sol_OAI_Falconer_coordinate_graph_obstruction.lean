-- Prove2me | solution 1 for OAI.Falconer.coordinate_graph_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:08:00.95453+00:00
-- url     : https://prove2.me/submissions/cf5747a5-7164-4292-ae74-a456f2e315ae

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_Regularization_scalar_dyadic_projection

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSumCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-cell comparison for scalar sumsets. These constant-factor
bridges allow the finite additive-combinatorial estimates to be applied
at the same scale as the parameter projections. -/
namespace Falconer
open scoped Pointwise

theorem floor_add_carry (u v : ℝ) :
    ⌊u+v⌋ = ⌊u⌋+⌊v⌋ ∨ ⌊u+v⌋ = ⌊u⌋+⌊v⌋+1 := by
  have h1 := Int.le_floor_add u v
  have h2 := Int.le_floor_add_floor u v
  omega

theorem scalarCells_add_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A+B) ⊆ (scalarCells δ A+scalarCells δ B) ∪
      ((scalarCells δ A+scalarCells δ B).image fun z => z+1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have hmem : ⌊a/δ⌋+⌊b/δ⌋ ∈ scalarCells δ A+scalarCells δ B :=
    Finset.add_mem_add (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [add_div]
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem add_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A+scalarCells δ B ⊆ scalarCells δ (A+B) ∪
      ((scalarCells δ (A+B)).image fun z => z-1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ+b/δ⌋ ∈ scalarCells δ (A+B) := by
    rw [← add_div]
    exact Finset.mem_image.mpr ⟨a+b,Finset.add_mem_add ha hb,rfl⟩
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

theorem scalarCells_add_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A+B)).card ≤ 2*(scalarCells δ A+scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_add_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A+scalarCells δ B)
    ((scalarCells δ A+scalarCells δ B).image fun z => z+1)
  have hi := Finset.card_image_le (s := scalarCells δ A+scalarCells δ B) (f := fun z => z+1)
  omega

theorem add_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A+scalarCells δ B).card ≤ 2*(scalarCells δ (A+B)).card := by
  have hb := Finset.card_le_card (add_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A+B))
    ((scalarCells δ (A+B)).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ (A+B)) (f := fun z => z-1)
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRuzsa
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar discretized Ruzsa triangle inequality, with the rounding
constant stated explicitly. -/
namespace Falconer
open scoped Pointwise

theorem floor_sub_carry (u v : ℝ) :
    ⌊u-v⌋ = ⌊u⌋-⌊v⌋ ∨ ⌊u-v⌋ = ⌊u⌋-⌊v⌋-1 := by
  have h1 := Int.le_floor_add (u-v) v
  have h2 := Int.le_floor_add_floor (u-v) v
  rw [sub_add_cancel] at h1 h2
  omega

theorem scalarCells_sub_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A-B) ⊆ (scalarCells δ A-scalarCells δ B) ∪
      ((scalarCells δ A-scalarCells δ B).image fun z => z-1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  have hmem : ⌊a/δ⌋-⌊b/δ⌋ ∈ scalarCells δ A-scalarCells δ B :=
    Finset.sub_mem_sub (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem scalarCells_sub_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A-B)).card ≤ 2*(scalarCells δ A-scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_sub_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A-scalarCells δ B)
    ((scalarCells δ A-scalarCells δ B).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ A-scalarCells δ B) (f := fun z => z-1)
  omega

theorem scalar_ruzsa_triangle (δ : ℝ) (A B C : Finset ℝ) :
    (scalarCells δ (A-C)).card*(scalarCells δ B).card ≤
      8*(scalarCells δ (A+B)).card*(scalarCells δ (C+B)).card := by
  have hR := Finset.ruzsa_triangle_inequality_sub_add_add
    (scalarCells δ A) (scalarCells δ B) (scalarCells δ C)
  calc
    _ ≤ (2*(scalarCells δ A-scalarCells δ C).card)*(scalarCells δ B).card :=
      Nat.mul_le_mul_right _ (scalarCells_sub_card δ A C)
    _ = 2*((scalarCells δ A-scalarCells δ C).card*(scalarCells δ B).card) := by ring
    _ ≤ 2*((scalarCells δ A+scalarCells δ B).card*(scalarCells δ C+scalarCells δ B).card) :=
      Nat.mul_le_mul_left 2 hR
    _ ≤ 2*((2*(scalarCells δ (A+B)).card)*(2*(scalarCells δ (C+B)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (add_scalarCells_card δ A B) (add_scalarCells_card δ C B))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinitePopularity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative popular-parameter selection in the finite incidence
argument. No asymptotic notation or hidden logarithmic losses are used. -/
namespace Falconer

/-- Deleting points below a fixed degree threshold loses at most the
threshold times the size of the whole set. -/
theorem finite_popular_mass {α : Type*} (S : Finset α) (w : α → ℝ)
    {I θ L : ℝ} (hθ : 0 ≤ θ) (htotal : I ≤ ∑ x ∈ S, w x)
    (hsmall : θ*(S.card : ℝ) ≤ I/2) (hupper : ∀ x ∈ S, w x ≤ L) :
    let G := S.filter fun x => θ ≤ w x
    I/2 ≤ ∑ x ∈ G, w x ∧ I/2 ≤ L*(G.card : ℝ) := by
  let G := S.filter fun x => θ ≤ w x
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => θ ≤ w x) w
  have hbad : (∑ x ∈ S.filter (fun x => ¬θ ≤ w x), w x) ≤ θ*(S.card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬θ ≤ w x), θ :=
        Finset.sum_le_sum fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = θ*((S.filter (fun x => ¬θ ≤ w x)).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hθ
  have hmass : I/2 ≤ ∑ x ∈ G, w x := by
    dsimp [G]
    linarith
  refine ⟨hmass,hmass.trans ?_⟩
  calc
    _ ≤ ∑ _x ∈ G, L := Finset.sum_le_sum fun x hx => hupper x (Finset.mem_filter.mp hx).1
    _ = _ := by simp [G,mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_BipartitePivot
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dense-neighborhood pivot used in the scalar additive-energy
argument. Integer vertices are sufficient for the quantized sumsets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem integer_bad_pairs_sum (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) :
    (∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) =
      ∑ p ∈ integerBadPairs A B e L, ((integerCommonNeighbors A e p.1 p.2).card : ℝ) := by
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := A) (t := integerBadPairs A B e L) (fun a p => e a p.1 ∧ e a p.2)
  exact_mod_cast he

theorem integer_bad_pairs_sum_le (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    {L : ℝ} (hL : 0 ≤ L) :
    (∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) ≤ L*(B.card : ℝ)^2 := by
  rw [integer_bad_pairs_sum]
  calc
    _ ≤ ∑ _p ∈ integerBadPairs A B e L, L := Finset.sum_le_sum fun p hp =>
      ((Finset.mem_filter.mp hp).2).le
    _ = L*((integerBadPairs A B e L).card : ℝ) := by simp [mul_comm]
    _ ≤ L*(B.card : ℝ)^2 := by
      apply mul_le_mul_of_nonneg_left _ hL
      have hc := Finset.card_le_card (show integerBadPairs A B e L ⊆ B ×ˢ B from Finset.filter_subset _ _)
      simpa only [Finset.card_product,Nat.cast_mul,pow_two] using (Nat.cast_le (α := ℝ)).mpr hc

theorem integer_dense_pivot (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ)) :
    ∃ a ∈ A, ρ*(B.card : ℝ)/2 ≤ ((integerNeighbors B e a).card : ℝ) ∧
      16*((integerBadPairsAt A B e L a).card : ℝ) ≤
        ρ*(B.card : ℝ)*((integerNeighbors B e a).card : ℝ) := by
  have ha : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hb : 0 < (B.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  let c : ℝ := 16/(ρ*(B.card : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbad := integer_bad_pairs_sum_le A B e hL
  have hloss : c*(∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) ≤
      ρ*(A.card : ℝ)*(B.card : ℝ)/2 := by
    calc
      _ ≤ c*(L*(B.card : ℝ)^2) := mul_le_mul_of_nonneg_left hbad hc
      _ ≤ c*((ρ^2*(A.card : ℝ)/32)*(B.card : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)) hc
      _ = _ := by dsimp [c]; field_simp; ring
  let score := fun a => ((integerNeighbors B e a).card : ℝ)-c*((integerBadPairsAt A B e L a).card : ℝ)
  have htotal : ∑ _a ∈ A, ρ*(B.card : ℝ)/2 ≤ ∑ a ∈ A, score a := by
    simp only [score,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    linarith
  obtain ⟨a,haA,hascore⟩ := Finset.exists_le_of_sum_le hA htotal
  have hscore : ρ*(B.card : ℝ)/2 ≤
      ((integerNeighbors B e a).card : ℝ)-c*((integerBadPairsAt A B e L a).card : ℝ) := hascore
  have hnonneg : 0 ≤ c*((integerBadPairsAt A B e L a).card : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
  refine ⟨a,haA,by linarith,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hscore (show 0 ≤ ρ*(B.card : ℝ) by positivity)
  have he : ρ*(B.card : ℝ)*(c*((integerBadPairsAt A B e L a).card : ℝ)) =
      16*((integerBadPairsAt A B e L a).card : ℝ) := by
    dsimp [c]
    field_simp
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DenseNeighborPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the few vertices with many bad partners leaves many common
good partners for every retained pair. This is the path-counting part of
the additive-energy refinement. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem dense_neighbor_pruning (N : Finset ℤ) (bad : ℤ → ℤ → Prop)
    {u : ℝ} (hu : 0 < u) (hN : u/2 ≤ (N.card : ℝ))
    (hsum : (∑ b ∈ N, ((N.filter fun c => bad b c).card : ℝ)) ≤ u*(N.card : ℝ)/16) :
    ∃ G ⊆ N, (N.card : ℝ)/2 ≤ (G.card : ℝ) ∧
      ∀ b ∈ G, ∀ c ∈ G,
        (N.card : ℝ)/2 ≤ ((N.filter fun v => ¬bad b v ∧ ¬bad c v).card : ℝ) := by
  let w := fun b => ((N.filter fun c => bad b c).card : ℝ)
  let G := N.filter fun b => w b ≤ u/8
  let D := N.filter fun b => ¬w b ≤ u/8
  have hD : (u/8)*(D.card : ℝ) ≤ ∑ b ∈ N, w b := by
    calc
      _ = ∑ _b ∈ D, u/8 := by simp [mul_comm]
      _ ≤ ∑ b ∈ D, w b := Finset.sum_le_sum fun b hb =>
        (lt_of_not_ge (Finset.mem_filter.mp hb).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
  have hsplit : (G.card : ℝ)+(D.card : ℝ) = N.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := N) (fun b => w b ≤ u/8)
  have hGcard : (N.card : ℝ)/2 ≤ G.card := by
    change (∑ b ∈ N, w b) ≤ _ at hsum
    nlinarith
  refine ⟨G,Finset.filter_subset _ _,hGcard,?_⟩
  intro b hb c hc
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  let H := N.filter fun v => ¬bad b v ∧ ¬bad c v
  let Db := N.filter fun v => bad b v
  let Dc := N.filter fun v => bad c v
  have hcover : N ⊆ H ∪ Db ∪ Dc := by
    intro v hv
    by_cases hbv : bad b v
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hbv⟩))
    · by_cases hcv : bad c v
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hcv⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,hbv,hcv⟩))
  have hcard : (N.card : ℝ) ≤ (H.card : ℝ)+(Db.card : ℝ)+(Dc.card : ℝ) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (H ∪ Db) Dc
    have h3 := Finset.card_union_le H Db
    exact_mod_cast (show N.card ≤ H.card+Db.card+Dc.card by omega)
  have hDb : (Db.card : ℝ) ≤ u/8 := hb'
  have hDc : (Dc.card : ℝ) ≤ u/8 := hc'
  change (N.card : ℝ)/2 ≤ H.card
  linarith

theorem integer_bad_pair_rows (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) (a : ℤ) :
    (∑ b ∈ integerNeighbors B e a,
      (((integerNeighbors B e a).filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card : ℝ)) =
      ((integerBadPairsAt A B e L a).card : ℝ) := by
  let N := integerNeighbors B e a
  have he : integerBadPairsAt A B e L a =
      (N ×ˢ N).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L := by
    ext ⟨b,c⟩
    simp only [integerBadPairsAt,integerBadPairs,integerNeighbors,N,Finset.mem_filter,Finset.mem_product]
    tauto
  rw [he]
  have hn : (∑ b ∈ N, (N.filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card) =
      ((N ×ˢ N).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  exact_mod_cast hn

theorem integer_dense_good_partners (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ)) :
    ∃ a ∈ A, ∃ G ⊆ integerNeighbors B e a,
      ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ∀ b ∈ G, ∀ c ∈ G,
        ρ*(B.card : ℝ)/4 ≤ (((integerNeighbors B e a).filter fun v =>
          L ≤ (integerCommonNeighbors A e b v).card ∧
          L ≤ (integerCommonNeighbors A e c v).card).card : ℝ) := by
  obtain ⟨a,ha,hN,hbad⟩ := integer_dense_pivot A B e hA hB hρ hL hsmall hdense
  have hsum : (∑ b ∈ integerNeighbors B e a,
      (((integerNeighbors B e a).filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card : ℝ)) ≤
      (ρ*(B.card : ℝ))*(integerNeighbors B e a).card/16 := by
    rw [integer_bad_pair_rows]
    linarith
  obtain ⟨G,hGN,hGcard,hpartners⟩ := dense_neighbor_pruning (integerNeighbors B e a)
    (fun b c => ((integerCommonNeighbors A e b c).card : ℝ) < L)
    (by have hb : (0 : ℝ) < B.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hB); positivity) hN hsum
  refine ⟨a,ha,G,hGN,by linarith,?_⟩
  intro b hb c hc
  have hp := hpartners b hb c hc
  simp only [not_lt] at hp
  exact (show ρ*(B.card : ℝ)/4 ≤ (integerNeighbors B e a).card/2 by linarith).trans hp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFourPaths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-edge paths and their sum labels. Injectivity of the labels is the
counting step converting dense neighborhoods into small difference sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem integerFourPaths_card (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (b c : ℤ) :
    ((integerFourPaths A B e b c).card : ℝ) =
      ∑ v ∈ B, ((integerCommonNeighbors A e b v).card : ℝ)*
        ((integerCommonNeighbors A e c v).card : ℝ) := by
  simp only [integerFourPaths,Finset.card_sigma,Finset.card_product,Nat.cast_sum,Nat.cast_mul]

theorem integerFourPaths_lower (A B V : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) (hV : V ⊆ B) {L : ℝ} (hL : 0 ≤ L)
    (hcommon : ∀ v ∈ V, L ≤ ((integerCommonNeighbors A e b v).card : ℝ) ∧
      L ≤ ((integerCommonNeighbors A e c v).card : ℝ)) :
    (V.card : ℝ)*L^2 ≤ (integerFourPaths A B e b c).card := by
  rw [integerFourPaths_card]
  calc
    _ = ∑ _v ∈ V, L*L := by simp [pow_two]
    _ ≤ ∑ v ∈ V, ((integerCommonNeighbors A e b v).card : ℝ)*
        ((integerCommonNeighbors A e c v).card : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul (hcommon v hv).1 (hcommon v hv).2 hL (Nat.cast_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hV (fun _ _ _ => by positivity)

theorem integerPathSums_injective (b c : ℤ) : Function.Injective (integerPathSums b c) := by
  rintro ⟨v,a₁,a₂⟩ ⟨w,d₁,d₂⟩ he
  have h1 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1.1) he
  have h2 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1.2) he
  have h3 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1) he
  dsimp [integerPathSums] at h1 h2 h3
  have ha : a₁ = d₁ := by omega
  have hv : v = w := by omega
  have hd : a₂ = d₂ := by omega
  subst d₁
  subst w
  subst d₂
  rfl

theorem integerPathSums_mem (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {b c : ℤ} (hb : b ∈ B) (hc : c ∈ B) {p : IntegerPath}
    (hp : p ∈ integerFourPaths A B e b c) :
    integerPathSums b c p ∈ (C ×ˢ C) ×ˢ (C ×ˢ C) := by
  obtain ⟨hv,hp⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨ha₁,ha₁b,ha₁v⟩ := Finset.mem_filter.mp hp1
  obtain ⟨ha₂,ha₂c,ha₂v⟩ := Finset.mem_filter.mp hp2
  exact Finset.mem_product.mpr ⟨
    Finset.mem_product.mpr ⟨hlabels _ ha₁ _ hb ha₁b,hlabels _ ha₁ _ hv ha₁v⟩,
    Finset.mem_product.mpr ⟨hlabels _ ha₂ _ hv ha₂v,hlabels _ ha₂ _ hc ha₂c⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarEnergyRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the integer additive-energy refinement to separated real
sets, preserving the original points and the quantized difference bound. -/
namespace Falconer
open scoped Pointwise

theorem same_scalar_cell_dist_lt {δ x y : ℝ} (hδ : 0 < δ) (hcell : ⌊x/δ⌋ = ⌊y/δ⌋) :
    |x-y| < δ := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  rw [hcell] at hx0 hx1
  have hh : |x/δ-y/δ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  exact (div_lt_one hδ).1 hh

theorem scalarCells_injective {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    Set.InjOn (fun x => ⌊x/δ⌋) (A : Set ℝ) := by
  intro x hx y hy he
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (same_scalar_cell_dist_lt hδ he)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarCoverCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting cells covered by finitely many translated scalar sets. -/
namespace Falconer
open scoped Pointwise

theorem floor_div_near_nat {δ u v : ℝ} (hδ : 0 < δ) (k : ℕ)
    (huv : |u-v| ≤ k*δ) : |⌊u/δ⌋-⌊v/δ⌋| ≤ (k : ℤ)+1 := by
  have hd : |u/δ-v/δ| ≤ (k : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ (k : ℝ)+1 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem scalarCells_near_card_nat {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (k : ℕ) (hcover : ∀ a ∈ A, ∃ b ∈ B, |a-b| ≤ k*δ) :
    (scalarCells δ A).card ≤ (2*k+3)*(scalarCells δ B).card := by
  classical
  let I := fun z : ℤ => Finset.Icc (z-((k : ℤ)+1)) (z+((k : ℤ)+1))
  have hsub : scalarCells δ A ⊆ (scalarCells δ B).biUnion I := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,hab⟩ := hcover a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊b/δ⌋,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
    have hh := floor_div_near_nat hδ k hab
    rw [abs_le] at hh
    apply Finset.mem_Icc.mpr
    omega
  have hI (z : ℤ) : (I z).card = 2*k+3 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((scalarCells δ B).biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ scalarCells δ B, (I z).card := Finset.card_biUnion_le
    _ = _ := by simp [hI,Nat.mul_comm]

theorem scalarCells_translate_cover {δ : ℝ} (hδ : 0 < δ)
    (P F Z : Finset ℝ) (k : ℕ)
    (hcover : ∀ p ∈ P, ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ k*δ) :
    (scalarCells δ P).card ≤ 2*(2*k+3)*F.card*(scalarCells δ Z).card := by
  classical
  have hn := scalarCells_near_card_nat hδ P (F+Z) k (by
    intro p hp
    obtain ⟨f,hf,z,hz,he⟩ := hcover p hp
    exact ⟨f+z,Finset.add_mem_add hf hz,he⟩)
  have hs := scalarCells_add_card δ F Z
  have hc : (scalarCells δ F+scalarCells δ Z).card ≤ F.card*(scalarCells δ Z).card :=
    Finset.card_add_le.trans (Nat.mul_le_mul_right _ (Finset.card_image_le (s := F)))
  calc
    _ ≤ (2*k+3)*(2*(F.card*(scalarCells δ Z).card)) :=
      hn.trans (Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_left _ hc)))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDilationBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar dilation changes a fixed-resolution covering number by at
most a linear factor in the dilation bound. -/
namespace Falconer
open scoped Pointwise

theorem scalar_dilation_cells {δ c : ℝ} (hδ : 0 < δ) (A : Finset ℝ)
    (M : ℕ) (hc : |c| ≤ M) :
    (scalarCells δ (A.image fun x => c*x)).card ≤ (2*M+3)*(scalarCells δ A).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  let F := (scalarCells δ A).image g
  have hF : F.card ≤ (scalarCells δ A).card := Finset.card_image_le
  have hcover : ∀ x ∈ A.image (fun x => c*x),
      ∃ y ∈ F.image (fun x => c*x), |x-y| ≤ (M : ℝ)*δ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hq := Function.invFunOn_pos (f := q) (s := (A : Set ℝ)) ⟨x,hx,rfl⟩
    have hxg : |x-g (q x)| ≤ δ := (same_scalar_cell_dist_lt hδ hq.2.symm).le
    have hgf : g (q x) ∈ F := Finset.mem_image.mpr
      ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩
    refine ⟨c*g (q x),Finset.mem_image.mpr ⟨g (q x),hgf,rfl⟩,?_⟩
    rw [← mul_sub,abs_mul]
    exact mul_le_mul hc hxg (abs_nonneg _) (Nat.cast_nonneg M)
  have hn := scalarCells_near_card_nat hδ (A.image fun x => c*x) (F.image fun x => c*x) M hcover
  have hsmall : (scalarCells δ (F.image fun x => c*x)).card ≤ (scalarCells δ A).card :=
    Finset.card_image_le.trans (Finset.card_image_le.trans hF)
  exact hn.trans (Nat.mul_le_mul_left _ hsmall)

theorem scalar_inverse_coefficient_cells {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (X : Finset ℝ) (M : ℕ) (hM : |a⁻¹| ≤ M) :
    (scalarCells δ (X+X.image (fun x => a⁻¹*x))).card ≤
      (2*M+3)*(scalarCells δ (X+X.image (fun x => a*x))).card := by
  classical
  have he : X+X.image (fun x => a⁻¹*x) =
      (X+X.image (fun x => a*x)).image (fun x => a⁻¹*x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨y+a*x,Finset.add_mem_add hy
        (Finset.mem_image.mpr ⟨x,hx,rfl⟩),?_⟩
      simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
    · intro hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x,hx,w,hw,rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have heq : a⁻¹*(x+a*y) = y+a⁻¹*x := by
        simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
      rw [heq]
      exact Finset.add_mem_add hy (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  rw [he]
  exact scalar_dilation_cells hδ _ M hM

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSignedRuzsa
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The other sign of the scalar Ruzsa triangle inequality, with the
same rounding loss. -/
namespace Falconer
open scoped Pointwise

 theorem sub_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A-scalarCells δ B ⊆ scalarCells δ (A-B) ∪
      ((scalarCells δ (A-B)).image fun z => z+1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ-b/δ⌋ ∈ scalarCells δ (A-B) := by
    rw [← sub_div]
    exact Finset.mem_image.mpr ⟨a-b,Finset.sub_mem_sub ha hb,rfl⟩
  rcases floor_sub_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

 theorem sub_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A-scalarCells δ B).card ≤ 2*(scalarCells δ (A-B)).card := by
  have hb := Finset.card_le_card (sub_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A-B))
    ((scalarCells δ (A-B)).image fun z => z+1)
  have hi := Finset.card_image_le (s := scalarCells δ (A-B)) (f := fun z => z+1)
  omega

 theorem scalar_ruzsa_sum_triangle (δ : ℝ) (A B C : Finset ℝ) :
    (scalarCells δ (A+C)).card*(scalarCells δ B).card ≤
      8*(scalarCells δ (B-A)).card*(scalarCells δ (B+C)).card := by
  have hR := Finset.ruzsa_triangle_inequality_add_sub_add
    (scalarCells δ A) (scalarCells δ B) (scalarCells δ C)
  calc
    _ ≤ (2*(scalarCells δ A+scalarCells δ C).card)*(scalarCells δ B).card :=
      Nat.mul_le_mul_right _ (scalarCells_add_card δ A C)
    _ = 2*((scalarCells δ B).card*(scalarCells δ A+scalarCells δ C).card) := by ring
    _ ≤ 2*((scalarCells δ B-scalarCells δ A).card*(scalarCells δ B+scalarCells δ C).card) :=
      Nat.mul_le_mul_left 2 hR
    _ ≤ 2*((2*(scalarCells δ (B-A)).card)*(2*(scalarCells δ (B+C)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (sub_scalarCells_card δ B A) (add_scalarCells_card δ B C))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSubsetTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transferring a small projection from an overlapping subset to its
reference set. Every denominator remains an actual covering number. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCells_mono (δ : ℝ) {A B : Finset ℝ} (hAB : A ⊆ B) :
    scalarCells δ A ⊆ scalarCells δ B := Finset.image_subset_image hAB

 theorem scalar_subset_sum_transfer (δ : ℝ) (A B C D : Finset ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hBA : B ⊆ A)
    (h0 : ((scalarCells δ (A+D)).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+C)).card : ℝ) ≤ L) :
    ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card*(scalarCells δ D).card ≤ 64*L^3 := by
  have hBD : ((scalarCells δ (B+D)).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add hBA (Finset.Subset.refl D))))).trans h0
  have hd : ((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card ≤ 8*L^2 := by
    have hh : ((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card ≤
        8*((scalarCells δ (B+D)).card : ℝ)*(scalarCells δ (A+D)).card := by
      exact_mod_cast scalar_ruzsa_triangle δ B D A
    have hprod := mul_le_mul hBD h0 (Nat.cast_nonneg _) hL
    nlinarith
  have hs : ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card ≤
      8*((scalarCells δ (B-A)).card : ℝ)*L := by
    have hh : ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card ≤
        8*((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ (B+C)).card := by
      exact_mod_cast scalar_ruzsa_sum_triangle δ A B C
    exact hh.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  calc
    _ ≤ (8*((scalarCells δ (B-A)).card : ℝ)*L)*(scalarCells δ D).card :=
      mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = (8*L)*(((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card) := by ring
    _ ≤ (8*L)*(8*L^2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

 theorem scalar_subset_difference_transfer (δ : ℝ) (A B C D R : Finset ℝ)
    {L F : ℝ} (hL : 0 ≤ L) (hF : 0 ≤ F) (hBA : B ⊆ A)
    (h0 : ((scalarCells δ (A+D)).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+C)).card : ℝ) ≤ L)
    (hscale : ((scalarCells δ (R+C)).card : ℝ) ≤ F*L) :
    ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ B).card*
      (scalarCells δ D).card*(scalarCells δ C).card ≤ 512*F*L^4 := by
  have hsum := scalar_subset_sum_transfer δ A B C D hL hBA h0 h1
  have hdiff : ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card ≤
      8*((scalarCells δ (A+C)).card : ℝ)*(F*L) := by
    have hh : ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card ≤
        8*((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ (R+C)).card := by
      exact_mod_cast scalar_ruzsa_triangle δ A C R
    exact hh.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  calc
    _ = (((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card)*
        ((scalarCells δ B).card*(scalarCells δ D).card) := by ring
    _ ≤ (8*((scalarCells δ (A+C)).card : ℝ)*(F*L))*
        ((scalarCells δ B).card*(scalarCells δ D).card) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = (8*F*L)*(((scalarCells δ (A+C)).card : ℝ)*
        (scalarCells δ B).card*(scalarCells δ D).card) := by ring
    _ ≤ (8*F*L)*(64*L^3) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRatioTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two overlapping small projections give a small difference projection
for the ratio of their coefficients. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_dilation_sum_image (A Y : Finset ℝ) {a b r : ℝ} (h : r*a = b) :
    A.image (fun x => r*x)+Y.image (fun y => b*y) =
      (A+Y.image (fun y => a*y)).image (fun x => r*x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨x+a*y,Finset.add_mem_add hx
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩),?_⟩
    rw [mul_add,← mul_assoc,h]
  · intro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    rw [mul_add,← mul_assoc,h]
    exact Finset.add_mem_add (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩)

 theorem scalar_ratio_transfer {δ a b r L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L) (A B Y : Finset ℝ) (hBA : B ⊆ A)
    (hr : r*a = b) (M : ℕ) (hM : |r| ≤ M)
    (h0 : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+Y.image (fun y => b*y))).card : ℝ) ≤ L) :
    ((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
      (scalarCells δ B).card*(scalarCells δ (Y.image (fun y => a*y))).card*
      (scalarCells δ (Y.image (fun y => b*y))).card ≤ 512*(2*M+3)*L^4 := by
  have hs : ((scalarCells δ (A.image (fun x => r*x)+Y.image (fun y => b*y))).card : ℝ) ≤
      (2*M+3)*L := by
    rw [scalar_dilation_sum_image A Y hr]
    have hh : ((scalarCells δ ((A+Y.image (fun y => a*y)).image (fun x => r*x))).card : ℝ) ≤
        (2*M+3)*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) := by
      exact_mod_cast scalar_dilation_cells hδ (A+Y.image (fun y => a*y)) M hM
    exact hh.trans (mul_le_mul_of_nonneg_left h0 (by positivity))
  exact scalar_subset_difference_transfer δ A B (Y.image fun y => b*y)
    (Y.image fun y => a*y) (A.image fun x => r*x) hL (by positivity) hBA h0 h1 hs

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarScaledCard
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower bounds for covering numbers of scalar dilates, using only
the inverse dilation required by the projection application. -/
namespace Falconer

 theorem scalarCells_dilate_inverse {a : ℝ} (ha : a ≠ 0) (Y : Finset ℝ) :
    (Y.image fun y => a*y).image (fun y => a⁻¹*y) = Y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hu
    simpa only [← mul_assoc,inv_mul_cancel₀ ha,one_mul] using hy
  · intro hz
    refine Finset.mem_image.mpr ⟨a*z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    rw [← mul_assoc,inv_mul_cancel₀ ha,one_mul]

 theorem scalar_scaled_cells_lower {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (Y : Finset ℝ) (M : ℕ) (hM : |a⁻¹| ≤ M)
    (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    (Y.card : ℝ) ≤ (2*M+3)*((scalarCells δ (Y.image (fun y => a*y))).card : ℝ) := by
  have hh := scalar_dilation_cells hδ (Y.image fun y => a*y) M hM
  rw [scalarCells_dilate_inverse ha Y] at hh
  have hcard : (scalarCells δ Y).card = Y.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  rw [hcard] at hh
  exact_mod_cast hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRatioCard
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ratio projection transfer expressed in cardinalities of the actual
separated overlap sets. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_ratio_card_bound {δ a b r L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L) (ha : a ≠ 0) (hb : b ≠ 0)
    (A B Y : Finset ℝ) (hBA : B ⊆ A)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hr : r*a = b) (M R : ℕ) (haM : |a⁻¹| ≤ M) (hbM : |b⁻¹| ≤ M) (hrR : |r| ≤ R)
    (h0 : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+Y.image (fun y => b*y))).card : ℝ) ≤ L) :
    ((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
      (B.card : ℝ)*(Y.card : ℝ)^2 ≤ 512*(2*R+3)*(2*M+3)^2*L^4 := by
  have hpre := scalar_ratio_transfer hδ hL A B Y hBA hr R hrR h0 h1
  have hBc : (scalarCells δ B).card = B.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hBsep)
  rw [hBc] at hpre
  have hYa := scalar_scaled_cells_lower hδ ha Y M haM hYsep
  have hYb := scalar_scaled_cells_lower hδ hb Y M hbM hYsep
  have hYs : (Y.card : ℝ)^2 ≤ ((2*M+3 : ℝ)^2)*
      (scalarCells δ (Y.image (fun y => a*y))).card*
      (scalarCells δ (Y.image (fun y => b*y))).card := by
    have hh := mul_le_mul hYa hYb (Nat.cast_nonneg _) (by positivity)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  calc
    _ ≤ (((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*(B.card : ℝ))*
        (((2*M+3 : ℝ)^2)*(scalarCells δ (Y.image (fun y => a*y))).card*
          (scalarCells δ (Y.image (fun y => b*y))).card) :=
      mul_le_mul_of_nonneg_left hYs (by positivity)
    _ = (2*M+3 : ℝ)^2*(((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
        (B.card : ℝ)*(scalarCells δ (Y.image (fun y => a*y))).card*
          (scalarCells δ (Y.image (fun y => b*y))).card) := by ring
    _ ≤ (2*M+3 : ℝ)^2*(512*(2*R+3)*L^4) :=
      mul_le_mul_of_nonneg_left hpre (by positivity)
    _ = _ := by ring

 theorem scalar_ratio_card_lower {D ρ N V B Y L : ℝ}
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hV : 0 ≤ V)
    (hB : ρ^4*N/2 ≤ B) (hY : ρ^4*V/2 ≤ Y)
    (hpre : D*B*Y^2 ≤ L) : D*ρ^12*N*V^2 ≤ 8*L := by
  have hYsq : (ρ^4*V/2)^2 ≤ Y^2 := pow_le_pow_left₀ (by positivity) hY 2
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ ρ^4*N/2).trans hB
  have hprod := mul_le_mul hB hYsq (by positivity) hB0
  have hd := mul_le_mul_of_nonneg_left hprod hD
  calc
    _ = 8*(D*((ρ^4*N/2)*(ρ^4*V/2)^2)) := by ring
    _ ≤ 8*(D*(B*Y^2)) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = 8*(D*B*Y^2) := by ring
    _ ≤ 8*L := mul_le_mul_of_nonneg_left hpre (by norm_num)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteFamilyOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common row with many large intersections, for the two-sided
additive-energy refinements. -/
namespace Falconer

 theorem finite_membership_sum {β : Type*} [DecidableEq β]
    (U S : Finset β) (hS : S ⊆ U) :
    (∑ x ∈ U, if x ∈ S then (1 : ℝ) else 0) = S.card := by
  have he : U.filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hx => hS hx)
  rw [Finset.sum_boole,he]

 theorem finite_family_overlap_moment {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hsub : ∀ i ∈ I, A i ⊆ U) :
    (∑ i ∈ I, ((A i).card : ℝ))^2 ≤
      (U.card : ℝ)*(∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)) := by
  classical
  let d := fun x => ∑ i ∈ I, if x ∈ A i then (1 : ℝ) else 0
  have htotal : ∑ x ∈ U, d x = ∑ i ∈ I, ((A i).card : ℝ) := by
    dsimp [d]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => finite_membership_sum U (A i) (hsub i hi)
  have hsquare : (∑ x ∈ U, (d x)^2) =
      ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ) := by
    calc
      _ = ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        simp only [d,pow_two,Finset.sum_mul_sum]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        have he (x : β) :
            (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) =
            if x ∈ A i ∩ A j then 1 else 0 := by
          by_cases hx : x ∈ A i <;> by_cases hy : x ∈ A j <;> simp [hx,hy]
        simp_rw [he]
        exact finite_membership_sum U _ fun x hx => hsub i hi (Finset.mem_inter.mp hx).1
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) d
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,htotal,hsquare] using hCS

 theorem finite_family_common_row {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {m : ℝ} (hm : 0 < m)
    (hsub : ∀ i ∈ I, A i ⊆ U) (hsize : ∀ i ∈ I, m ≤ ((A i).card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ 2*(U.card : ℝ)*(J.card : ℝ) ∧
      ∀ j ∈ J, m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ) := by
  classical
  have hIpos : 0 < (I.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hI)
  have hUpos : 0 < (U.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  let w := fun i => ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
  obtain ⟨i₀,hi₀,hmax⟩ := I.exists_max_image w hI
  have hsum : m*(I.card : ℝ) ≤ ∑ i ∈ I, ((A i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ I, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hsize
  have hmoment := finite_family_overlap_moment I U A hsub
  have hmaxsum : (∑ i ∈ I, w i) ≤ (I.card : ℝ)*w i₀ := by
    calc
      _ ≤ ∑ _i ∈ I, w i₀ := Finset.sum_le_sum fun i hi => hmax i hi
      _ = _ := by simp
  have hlower : (m*(I.card : ℝ))^2 ≤ (U.card : ℝ)*((I.card : ℝ)*w i₀) := by
    exact (pow_le_pow_left₀ (mul_pos hm hIpos).le hsum 2).trans
      (hmoment.trans (mul_le_mul_of_nonneg_left hmaxsum hUpos.le))
  have hw : (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ w i₀ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hUpos).2
    apply (mul_le_mul_iff_left₀ hIpos).1
    calc
      _ = (m*(I.card : ℝ))^2 := by ring
      _ ≤ _ := hlower
      _ = _ := by ring
  let J := I.filter fun j => m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ)
  have hp := finite_popular_mass I (fun j => ((A i₀ ∩ A j).card : ℝ))
    (I := (m^2/(U.card : ℝ))*(I.card : ℝ))
    (θ := m^2/(2*(U.card : ℝ))) (L := (U.card : ℝ))
    (by positivity) hw (le_of_eq (by ring))
    (fun j _ => Nat.cast_le.mpr (Finset.card_le_card
      (fun x hx => hsub i₀ hi₀ (Finset.mem_inter.mp hx).1)))
  refine ⟨i₀,hi₀,J,Finset.filter_subset _ _,?_,?_⟩
  · have hh := hp.2
    change (m^2/(U.card : ℝ))*(I.card : ℝ)/2 ≤ (U.card : ℝ)*(J.card : ℝ) at hh
    linarith
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonRectangles
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous large intersections for both factors of a family of
rectangles. The reference rectangle is an actual member of the family. -/
namespace Falconer

 theorem common_rectangular_subsets {α : Type*}
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧
      ∀ j ∈ J,
        ρ^4*(X.card : ℝ)/2 ≤ ((A i₀ ∩ A j).card : ℝ) ∧
        ρ^4*(Y.card : ℝ)/2 ≤ ((B i₀ ∩ B j).card : ℝ) := by
  classical
  have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hYpos : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  let R := fun i => (A i) ×ˢ (B i)
  have hRsub (i) (hi : i ∈ I) : R i ⊆ X ×ˢ Y := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hA i hi ha,hB i hi hb⟩
  have hRsize (i) (hi : i ∈ I) : ρ^2*(X.card : ℝ)*(Y.card : ℝ) ≤ ((R i).card : ℝ) := by
    have hh := mul_le_mul (hsizeA i hi) (hsizeB i hi)
      (mul_pos hρ hYpos).le (Nat.cast_nonneg _)
    simpa only [R,Finset.card_product,Nat.cast_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
  obtain ⟨i₀,hi₀,J,hJI,hJ,hrect⟩ := finite_family_common_row I (X ×ˢ Y) R
    hI (hX.product hY) (by positivity : 0 < ρ^2*(X.card : ℝ)*(Y.card : ℝ)) hRsub hRsize
  have hn : (ρ^2*(X.card : ℝ)*(Y.card : ℝ))^2/((X.card : ℝ)*(Y.card : ℝ)) =
      ρ^4*(X.card : ℝ)*(Y.card : ℝ) := by
    field_simp
  have hnorm : (ρ^2*(X.card : ℝ)*(Y.card : ℝ))^2/(2*((X.card : ℝ)*(Y.card : ℝ))) =
      ρ^4*(X.card : ℝ)*(Y.card : ℝ)/2 := by
    field_simp
  simp only [Finset.card_product,Nat.cast_mul,hn] at hJ
  refine ⟨i₀,hi₀,J,hJI,?_,?_⟩
  · apply (mul_le_mul_iff_left₀ (mul_pos hXpos hYpos)).1
    first | (convert hJ using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hJ.trans (le_of_eq (by ring)))
  · intro j hj
    have hh := hrect j hj
    simp only [R,Finset.product_inter_product,Finset.card_product,Nat.cast_mul,hnorm] at hh
    have ha : ((A i₀ ∩ A j).card : ℝ) ≤ (X.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans (hA i₀ hi₀)))
    have hb : ((B i₀ ∩ B j).card : ℝ) ≤ (Y.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans (hB i₀ hi₀)))
    constructor
    · have hx := hh.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
      apply (mul_le_mul_iff_left₀ hYpos).1
      convert hx using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · have hy := hh.trans (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))
      apply (mul_le_mul_iff_left₀ hXpos).1
      first | (convert hy using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hy.trans (le_of_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonRatioProjections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large rectangles from the scalar energy refinement have a common
reference set with small ratio projections. -/
namespace Falconer
open scoped Pointwise

 theorem common_small_ratio_projections {α : Type*} {δ ρ L : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I,
      ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card : ℝ) ≤ L) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧
      ∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ)*
          ρ^12*(X.card : ℝ)*(Y.card : ℝ)^2 ≤
            4096*(2*(M*M)+3)*(2*M+3)^2*L^4 := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hoverlap⟩ := common_rectangular_subsets I X Y A B
    hI hX hY hρ hA hB hsizeA hsizeB
  refine ⟨i₀,hi₀,J,hJI,hJ,?_⟩
  intro j hj
  have hjI := hJI hj
  let Xj := A i₀ ∩ A j
  let Yj := B i₀ ∩ B j
  have hXj : Xj ⊆ X := Finset.inter_subset_left.trans (hA i₀ hi₀)
  have hYj : Yj ⊆ Y := Finset.inter_subset_left.trans (hB i₀ hi₀)
  have h0 : ((scalarCells δ (A i₀+Yj.image (fun y => c i₀*y))).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add (Finset.Subset.refl _) (Finset.image_subset_image
        (show Yj ⊆ B i₀ from Finset.inter_subset_left)))))).trans (hproj i₀ hi₀)
  have h1 : ((scalarCells δ (Xj+Yj.image (fun y => c j*y))).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add (show Xj ⊆ A j from Finset.inter_subset_right)
        (Finset.image_subset_image (show Yj ⊆ B j from Finset.inter_subset_right)))))).trans (hproj j hjI)
  have hr : |c j/c i₀| ≤ (M*M : ℕ) := by
    rw [div_eq_mul_inv,abs_mul,Nat.cast_mul]
    exact mul_le_mul (hc j hjI).2.1 (hc i₀ hi₀).2.2 (abs_nonneg _) (Nat.cast_nonneg _)
  have ht := scalar_ratio_card_bound hδ hL (hc i₀ hi₀).1 (hc j hjI).1
    (A i₀) Xj Yj (show Xj ⊆ A i₀ from Finset.inter_subset_left)
    (fun x hx y hy hxy => hXsep x (hXj hx) y (hXj hy) hxy)
    (fun x hx y hy hxy => hYsep x (hYj hx) y (hYj hy) hxy)
    (div_mul_cancel₀ (c j) (hc i₀ hi₀).1) M (M*M) (hc i₀ hi₀).2.2 (hc j hjI).2.2 hr h0 h1
  have hh := scalar_ratio_card_lower (by positivity : 0 ≤
      ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ))
    (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card)
    (hoverlap j hj).1 (hoverlap j hj).2 ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRepeatedSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding errors for repeated scalar sumsets. Only one interval of
integer carries is required, so the loss is linear in the number of terms. -/
namespace Falconer
open scoped Pointwise

theorem scalar_nsum_floor (δ : ℝ) (X : Finset ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • scalarCells δ X, ∃ k : ℤ,
      0 ≤ k ∧ k ≤ (n : ℤ) ∧ ⌊x/δ⌋ = z+k := by
  classical
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact ⟨0,by simp,0,by norm_num,by norm_num,by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,k,hk0,hkn,hk⟩ := ih ha
    have hbq : ⌊b/δ⌋ ∈ scalarCells δ X := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have hmem : z+⌊b/δ⌋ ∈ (n+1) • scalarCells δ X := by
      rw [succ_nsmul]
      exact Finset.add_mem_add hz hbq
    rw [add_div]
    rcases floor_add_carry (a/δ) (b/δ) with he | he
    · refine ⟨z+⌊b/δ⌋,hmem,k,hk0,by omega,?_⟩
      omega
    · refine ⟨z+⌊b/δ⌋,hmem,k+1,by omega,by omega,?_⟩
      omega

theorem scalar_signed_sum_cells_subset (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    scalarCells δ (m • X-n • X) ⊆
      (m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ) := by
  classical
  intro w hw
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨z,hz,k,hk0,hkm,hk⟩ := scalar_nsum_floor δ X m ha
  obtain ⟨v,hv,l,hl0,hln,hl⟩ := scalar_nsum_floor δ X n hb
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with he | he
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

theorem scalar_signed_sum_card (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    (scalarCells δ (m • X-n • X)).card ≤
      (m+n+2)*(m • scalarCells δ X-n • scalarCells δ X).card := by
  classical
  have hc : (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card = m+n+2 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card :=
      Finset.card_le_card (scalar_signed_sum_cells_subset δ X m n)
    _ ≤ (m • scalarCells δ X-n • scalarCells δ X).card*
        (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card := Finset.card_add_le
    _ = _ := by rw [hc,Nat.mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPluennecke
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The application form of Pluennecke's inequality for scalar covering
numbers. Its only rounding loss is linear in the number of summands. -/
namespace Falconer
open scoped Pointwise

theorem scalar_pluennecke (δ : ℝ) (A B : Finset ℝ) (hA : A.Nonempty)
    {K : ℝ}
    (hsmall : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ A).card)
    (m n : ℕ) :
    ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*(2*K)^(m+n)*(scalarCells δ A).card := by
  have hAQ : (scalarCells δ A).Nonempty := Finset.image_nonempty.mpr hA
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hAQ)
  have hR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hAQ
    (scalarCells δ B) m n
  have hRR : ((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) ≤
      (((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card)^(m+n)*
        (scalarCells δ A).card := by
    have hReal := NNRat.cast_mono (K := ℝ) hR
    push_cast at hReal
    exact hReal
  have hsum : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ A).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  have hratio : ((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card ≤
      2*K := (div_le_iff₀ hAc).2 hsum
  have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hAc.le) hratio (m+n)
  have hbound := hRR.trans (mul_le_mul_of_nonneg_right hpow hAc.le)
  have hcarry : ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) := by
    exact_mod_cast scalar_signed_sum_card δ B m n
  have hmn : (0 : ℝ) ≤ m+n+2 := by positivity
  exact hcarry.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hmn)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDifferenceDoubling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small difference set supplies the doubling bound needed by
coefficient arithmetic. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_doubling_of_difference (δ : ℝ) (A : Finset ℝ)
    (hA : A.Nonempty) {K : ℝ}
    (hsmall : ((scalarCells δ (A-A)).card : ℝ) ≤ K*(scalarCells δ A).card) :
    ((scalarCells δ (A+A)).card : ℝ) ≤ 16*K^2*(scalarCells δ A).card := by
  have hAB : ((scalarCells δ (A+(-A))).card : ℝ) ≤ K*(scalarCells δ A).card := by
    simpa only [← sub_eq_add_neg] using hsmall
  have hh := scalar_pluennecke δ A (-A) hA hAB 0 2
  have he : (0 : ℕ) • (-A)-(2 : ℕ) • (-A) = A+A := by
    simp only [zero_nsmul,two_nsmul,zero_sub,neg_add,neg_neg]
  rw [he] at hh
  norm_num only [Nat.cast_zero,Nat.cast_ofNat,zero_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarProjectionDoubling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small nondegenerate projection gives doubling of its first factor. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_difference_from_sum {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (A Y : Finset ℝ) (M : ℕ) (haM : |a⁻¹| ≤ M)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    ((scalarCells δ (A-A)).card : ℝ)*(Y.card : ℝ) ≤
      8*(2*M+3)*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2 := by
  have hlower := scalar_scaled_cells_lower hδ ha Y M haM hYsep
  have ht : ((scalarCells δ (A-A)).card : ℝ)*
      (scalarCells δ (Y.image (fun y => a*y))).card ≤
      8*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2 := by
    have hh := scalar_ruzsa_triangle δ A (Y.image fun y => a*y) A
    exact_mod_cast (by simpa only [pow_two,mul_assoc] using hh)
  calc
    _ ≤ ((scalarCells δ (A-A)).card : ℝ)*
        ((2*M+3)*((scalarCells δ (Y.image (fun y => a*y))).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg _)
    _ = (2*M+3 : ℝ)*(((scalarCells δ (A-A)).card : ℝ)*
        (scalarCells δ (Y.image (fun y => a*y))).card) := by ring
    _ ≤ (2*M+3 : ℝ)*(8*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

 theorem scalar_doubling_from_projection {δ a K ρ : ℝ} (hδ : 0 < δ)
    (ha : a ≠ 0) (hρ : 0 < ρ)
    (A Y : Finset ℝ) (hA : A.Nonempty) (M : ℕ) (haM : |a⁻¹| ≤ M)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hYsize : ρ*((scalarCells δ A).card : ℝ) ≤ (Y.card : ℝ))
    (hsmall : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤
      K*(scalarCells δ A).card) :
    ((scalarCells δ (A+A)).card : ℝ) ≤
      (1024*(2*M+3)^2*K^4/ρ^2)*(scalarCells δ A).card := by
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.image_nonempty.mpr hA))
  have hd := scalar_difference_from_sum hδ ha A Y M haM hYsep
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hsmall 2
  have hbound : ((scalarCells δ (A-A)).card : ℝ)*(ρ*(scalarCells δ A).card) ≤
      8*(2*M+3)*(K*((scalarCells δ A).card : ℝ))^2 := by
    calc
      _ ≤ ((scalarCells δ (A-A)).card : ℝ)*(Y.card : ℝ) :=
        mul_le_mul_of_nonneg_left hYsize (Nat.cast_nonneg _)
      _ ≤ _ := hd.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hdiff : ((scalarCells δ (A-A)).card : ℝ) ≤
      (8*(2*M+3)*K^2/ρ)*(scalarCells δ A).card := by
    calc
      _ ≤ (8*(2*M+3)*(K*((scalarCells δ A).card : ℝ))^2)/
          (ρ*(scalarCells δ A).card) := (le_div_iff₀ (mul_pos hρ hAc)).2 hbound
      _ = _ := by field_simp
  have hh := scalar_doubling_of_difference δ A hA hdiff
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_UnbalancedRatioNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of common ratio counts when the two original coordinate
sets have comparable, rather than identical, cardinalities. -/
namespace Falconer

 theorem normalize_unbalanced_ratio {D C K ρ N P Q A : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hN : 0 < N) (hP : 0 < P)
    (hNP : N ≤ Q*P) (hA : ρ*N ≤ A)
    (hbound : D*ρ^12*N*P^2 ≤ C*(K*N)^4) :
    D ≤ (C*K^4*Q^2/ρ^13)*A := by
  have hNP2 : N^2 ≤ Q^2*P^2 := by
    have hh := pow_le_pow_left₀ hN.le hNP 2
    nlinarith
  have hcore : D*ρ^12 ≤ C*K^4*N*Q^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hN (sq_pos_of_pos hP))).1
    calc
      _ = D*ρ^12*N*P^2 := by ring
      _ ≤ C*(K*N)^4 := hbound
      _ = (C*K^4*N^2)*N^2 := by ring
      _ ≤ (C*K^4*N^2)*(Q^2*P^2) :=
        mul_le_mul_of_nonneg_left hNP2 (by positivity)
      _ = _ := by ring
  have hd : D ≤ (C*K^4*Q^2/ρ^12)*N := by
    have hh := (le_div_iff₀ (pow_pos hρ 12)).2 hcore
    convert hh using 1 <;> first | rfl | ring
  have hs := mul_le_mul_of_nonneg_left hA (show 0 ≤ C*K^4*Q^2/ρ^13 by positivity)
  calc
    _ ≤ (C*K^4*Q^2/ρ^12)*N := hd
    _ = (C*K^4*Q^2/ρ^13)*(ρ*N) := by field_simp
    _ ≤ _ := hs

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonUnbalancedProjections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common reference projection bounds with an explicit cardinality-ratio
loss. This avoids padding the actual planar coordinate sets. -/
namespace Falconer
open scoped Pointwise

 theorem common_unbalanced_ratio_projections {α : Type*} {δ ρ K Q : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hK : 0 ≤ K) (hQ : 1 ≤ Q)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : (X.card:ℝ) ≤ Q*(Y.card:ℝ))
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card : ℝ) ≤
      K*(X.card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧ (A i₀).Nonempty ∧
      ((scalarCells δ (A i₀+A i₀)).card : ℝ) ≤
        (1024*(2*M+3)^2*K^4*Q^2/ρ^6)*(scalarCells δ (A i₀)).card ∧
      ∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ) ≤
          (4096*(2*(M*M)+3)*(2*M+3)^2*K^4*Q^2/ρ^13)*(scalarCells δ (A i₀)).card := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hraw⟩ := common_small_ratio_projections hδ hρ
    (by positivity : 0 ≤ K*(X.card : ℝ)) I X Y A B c hI hX hY hXsep hYsep
    hA hB hsizeA hsizeB M hc hproj
  have hN : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hAi0 : 0 < ((A i₀).card : ℝ) := (mul_pos hρ hN).trans_le (hsizeA i₀ hi₀)
  have hAi : (A i₀).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hAi0)
  have hAc : (scalarCells δ (A i₀)).card = (A i₀).card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ
      (fun x hx y hy hxy => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hxy))
  have hP : 0 < (Y.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hbase : ((scalarCells δ (A i₀+(B i₀).image (fun y => c i₀*y))).card : ℝ) ≤
      (K/ρ)*(scalarCells δ (A i₀)).card := by
    apply (hproj i₀ hi₀).trans
    rw [hAc]
    have hh := mul_le_mul_of_nonneg_left (hsizeA i₀ hi₀) (div_nonneg hK hρ.le)
    calc
      _ = (K/ρ)*(ρ*(X.card : ℝ)) := by field_simp
      _ ≤ _ := hh
  have hBsize : (ρ/Q)*((scalarCells δ (A i₀)).card : ℝ) ≤ ((B i₀).card : ℝ) := by
    rw [hAc]
    have hAX : ((A i₀).card:ℝ) ≤ (X.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (hA i₀ hi₀))
    have hh := mul_le_mul_of_nonneg_left (hAX.trans hXY) (show 0 ≤ ρ/Q by positivity)
    calc
      _ ≤ (ρ/Q)*(Q*(Y.card:ℝ)) := hh
      _ = ρ*(Y.card:ℝ) := by field_simp
      _ ≤ _ := hsizeB i₀ hi₀
  have hd := scalar_doubling_from_projection hδ (hc i₀ hi₀).1 (div_pos hρ hQpos) (A i₀) (B i₀)
    hAi M (hc i₀ hi₀).2.2
    (fun x hx y hy hxy => hYsep x (hB i₀ hi₀ hx) y (hB i₀ hi₀ hy) hxy) hBsize hbase
  refine ⟨i₀,hi₀,J,hJI,hJ,hAi,?_,?_⟩
  · convert hd using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  · intro j hj
    have hb := hraw j hj
    have hh := normalize_unbalanced_ratio
      (by positivity : 0 ≤ (4096 : ℝ)*(2*(M*M)+3)*(2*M+3)^2)
      hρ hN hP hXY (hsizeA i₀ hi₀) hb
    rw [hAc]
    exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarProductBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fine-scale ball bounds for a Cartesian product of separated scalar
sets, with its actual Euclidean embedding. -/
namespace Falconer

theorem rowPoint_pair_injective : Function.Injective (fun p : ℝ × ℝ => rowPoint p.1 p.2) := by
  intro p q h
  have h0 := congrArg (fun v : Space 2 => v 0) h
  have h1 := congrArg (fun v : Space 2 => v 1) h
  exact Prod.ext h0 h1

theorem scalarProductPoints_card (X Y : Finset ℝ) :
    (scalarProductPoints X Y).card = X.card*Y.card := by
  rw [scalarProductPoints,Finset.card_image_of_injective _ rowPoint_pair_injective,Finset.card_product]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFivePaths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Five-edge sum labels give the two-sided small-sumset refinement used
to pass from projection collisions to a Cartesian product. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem integerFiveSums_alternating (a c : ℤ) (p : IntegerFivePath) :
    (integerFiveSums a c p).1-(integerFiveSums a c p).2.1.1+
      (integerFiveSums a c p).2.1.2-(integerFiveSums a c p).2.2.1+
      (integerFiveSums a c p).2.2.2 = a+c := by
  dsimp [integerFiveSums,integerPathSums]
  ring

theorem integerFiveSums_injective (a c : ℤ) : Function.Injective (integerFiveSums a c) := by
  rintro ⟨b,p⟩ ⟨d,q⟩ he
  have hb := congrArg Prod.fst he
  change a+b = a+d at hb
  have hbd : b = d := add_left_cancel hb
  subst d
  have hp := congrArg Prod.snd he
  have hpq : p = q := integerPathSums_injective b c hp
  subst q
  rfl

theorem integerFiveSums_mem (A B C G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hGB : G ⊆ B) (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {a c : ℤ} (ha : a ∈ A) (hc : c ∈ B) {p : IntegerFivePath}
    (hp : p ∈ integerFivePaths A B G e a c) :
    integerFiveSums a c p ∈ C ×ˢ ((C ×ˢ C) ×ˢ (C ×ˢ C)) := by
  obtain ⟨hb,hpath⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hbG,he⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_product.mpr ⟨hlabels a ha _ (hGB hbG) he,
    integerPathSums_mem A B C e hlabels (hGB hbG) hc hpath⟩

theorem integerFivePaths_lower (A B G : Finset ℤ) (e : ℤ → ℤ → Prop)
    {a c : ℤ} {m k : ℝ} (hk : 0 ≤ k)
    (hdegree : m ≤ ((G.filter fun b => e a b).card : ℝ))
    (hfour : ∀ b ∈ G, k ≤ ((integerFourPaths A B e b c).card : ℝ)) :
    m*k ≤ ((integerFivePaths A B G e a c).card : ℝ) := by
  calc
    _ ≤ ((G.filter fun b => e a b).card : ℝ)*k := mul_le_mul_of_nonneg_right hdegree hk
    _ = ∑ _b ∈ G.filter (fun b => e a b), k := by simp
    _ ≤ ∑ b ∈ G.filter (fun b => e a b), ((integerFourPaths A B e b c).card : ℝ) :=
      Finset.sum_le_sum fun b hb => hfour b (Finset.mem_filter.mp hb).1
    _ = _ := by simp only [integerFivePaths,Finset.card_sigma,Nat.cast_sum]

theorem five_path_sum_bound (A B C X G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hXA : X ⊆ A) (hGB : G ⊆ B)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {k : ℝ} (hpaths : ∀ a ∈ X, ∀ c ∈ G, k ≤ (integerFivePaths A B G e a c).card) :
    ((X+G).card : ℝ)*k ≤ (C.card : ℝ)^5 := by
  have hex (z : ℤ) : ∃ a c : ℤ, z ∈ X+G → a ∈ X ∧ c ∈ G ∧ a+c = z := by
    by_cases hz : z ∈ X+G
    · obtain ⟨a,ha,c,hc,he⟩ := Finset.mem_add.mp hz
      exact ⟨a,c,fun _ => ⟨ha,hc,he⟩⟩
    · exact ⟨0,0,fun h => False.elim (hz h)⟩
  choose a c hac using hex
  let W := (X+G).sigma fun z => integerFivePaths A B G e (a z) (c z)
  let code : (Σ _z : ℤ, IntegerFivePath) → ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) :=
    fun p => integerFiveSums (a p.1) (c p.1) p.2
  let V : Finset (ℤ × ((ℤ × ℤ) × (ℤ × ℤ))) := C ×ˢ ((C ×ˢ C) ×ˢ (C ×ˢ C))
  have hlower : ((X+G).card : ℝ)*k ≤ (W.card : ℝ) := by
    calc
      _ = ∑ _z ∈ X+G, k := by simp
      _ ≤ ∑ z ∈ X+G, ((integerFivePaths A B G e (a z) (c z)).card : ℝ) :=
        Finset.sum_le_sum fun z hz => hpaths _ (hac z hz).1 _ (hac z hz).2.1
      _ = _ := by simp only [W,Finset.card_sigma,Nat.cast_sum]
  have hmap : Set.MapsTo code (W : Set (Σ _z : ℤ, IntegerFivePath))
      (V : Set (ℤ × ((ℤ × ℤ) × (ℤ × ℤ)))) := by
    intro p hp
    obtain ⟨hz,hp⟩ := Finset.mem_sigma.mp hp
    exact integerFiveSums_mem A B C G e hGB hlabels (hXA (hac p.1 hz).1)
      (hGB (hac p.1 hz).2.1) hp
  have hinj : Set.InjOn code (W : Set (Σ _z : ℤ, IntegerFivePath)) := by
    rintro ⟨z,p⟩ hp ⟨w,q⟩ hq he
    have hz := (Finset.mem_sigma.mp hp).1
    have hw := (Finset.mem_sigma.mp hq).1
    have hd := congrArg (fun t : ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) =>
      t.1-t.2.1.1+t.2.1.2-t.2.2.1+t.2.2.2) he
    change (integerFiveSums (a z) (c z) p).1-(integerFiveSums (a z) (c z) p).2.1.1+
        (integerFiveSums (a z) (c z) p).2.1.2-(integerFiveSums (a z) (c z) p).2.2.1+
        (integerFiveSums (a z) (c z) p).2.2.2 =
      (integerFiveSums (a w) (c w) q).1-(integerFiveSums (a w) (c w) q).2.1.1+
        (integerFiveSums (a w) (c w) q).2.1.2-(integerFiveSums (a w) (c w) q).2.2.1+
        (integerFiveSums (a w) (c w) q).2.2.2 at hd
    rw [integerFiveSums_alternating,integerFiveSums_alternating,
      (hac z hz).2.2,(hac w hw).2.2] at hd
    subst w
    have hpq : p = q := integerFiveSums_injective (a z) (c z) he
    subst q
    rfl
  have hc := Finset.card_le_card_of_injOn code hmap hinj
  dsimp [V] at hc
  simp only [Finset.card_product] at hc
  have hu : (W.card : ℝ) ≤ (C.card : ℝ)^5 := by
    have hc' : (W.card : ℝ) ≤ (C.card : ℝ)*
        (((C.card : ℝ)*(C.card : ℝ))*((C.card : ℝ)*(C.card : ℝ))) := by exact_mod_cast hc
    exact hc'.trans_eq (by ring)
  exact hlower.trans hu

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerMixedRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-sided dense-graph refinement. Both vertex sets stay large and
their full sumset is bounded by the original restricted sum labels. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem integer_mixed_refinement_with_degrees (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C) :
    ∃ X ⊆ A, ∃ G ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((X+G).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        1048576*(C.card : ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(G.card:ℝ)/64 ≤ ((G.filter fun b => e x b).card:ℝ) := by
  have hAc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hBc : 0 < (B.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  let L : ℝ := ρ^2*(A.card : ℝ)/32
  let u : ℝ := ρ*(B.card : ℝ)/4
  have hL : 0 < L := div_pos (mul_pos (sq_pos_of_pos hρ) hAc) (by norm_num)
  have hu : 0 < u := div_pos (mul_pos hρ hBc) (by norm_num)
  obtain ⟨a,_,G,hGN,hGsize,hpartners⟩ := integer_dense_good_partners A B e hA hB hρ
    hL.le (le_refl L) hdense
  have hGB : G ⊆ B := hGN.trans (Finset.filter_subset _ _)
  have hGc : 0 < (G.card : ℝ) := hu.trans_le hGsize
  have hfour (b : ℤ) (hb : b ∈ G) (c : ℤ) (hc : c ∈ G) :
      u*L^2 ≤ (integerFourPaths A B e b c).card := by
    let V := (integerNeighbors B e a).filter fun v =>
      L ≤ (integerCommonNeighbors A e b v).card ∧ L ≤ (integerCommonNeighbors A e c v).card
    have hVB : V ⊆ B := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hV : u ≤ (V.card : ℝ) := hpartners b hb c hc
    have hlower := integerFourPaths_lower A B V e b c hVB hL.le
      (fun v hv => (Finset.mem_filter.mp hv).2)
    exact (mul_le_mul_of_nonneg_right hV (sq_nonneg L)).trans hlower
  have hcolumn (b : ℤ) (hb : b ∈ G) : L ≤ ((A.filter fun x => e x b).card : ℝ) := by
    let V := (integerNeighbors B e a).filter fun v =>
      L ≤ (integerCommonNeighbors A e b v).card ∧ L ≤ (integerCommonNeighbors A e b v).card
    have hV : 0 < (V.card : ℝ) := hu.trans_le (hpartners b hb b hb)
    have hVnat : 0 < V.card := by exact_mod_cast hV
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hVnat
    have hl := (Finset.mem_filter.mp hv).2.1
    have hsub : integerCommonNeighbors A e b v ⊆ A.filter (fun x => e x b) := by
      intro x hx
      obtain ⟨hx,hxb,_⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx,hxb⟩
    exact hl.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  let w : ℤ → ℝ := fun x => ((G.filter fun b => e x b).card : ℝ)
  have htotal : L*(G.card : ℝ) ≤ ∑ x ∈ A, w x := by
    have hsum : (∑ x ∈ A, w x) = ∑ b ∈ G, ((A.filter fun x => e x b).card : ℝ) := by
      have hn := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := A) (t := G) e
      dsimp only [Finset.bipartiteAbove,Finset.bipartiteBelow] at hn
      dsimp only [w]
      exact_mod_cast hn
    rw [hsum]
    calc
      _ = ∑ _b ∈ G, L := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcolumn
  let θ : ℝ := L*(G.card : ℝ)/(2*(A.card : ℝ))
  have hθ : 0 ≤ θ := div_nonneg (mul_nonneg hL.le hGc.le) (by positivity)
  have hsmall : θ*(A.card : ℝ) ≤ L*(G.card : ℝ)/2 := by
    dsimp [θ]
    field_simp
    rfl
  have hupper (x : ℤ) (_hx : x ∈ A) : w x ≤ (G.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hp := finite_popular_mass A w hθ htotal hsmall hupper
  let X := A.filter fun x => θ ≤ w x
  have hXsize : L/2 ≤ (X.card : ℝ) := by
    have hb : L*(G.card : ℝ)/2 ≤ (G.card : ℝ)*(X.card : ℝ) := hp.2
    nlinarith
  have hpaths (x : ℤ) (hx : x ∈ X) (c : ℤ) (hc : c ∈ G) :
      θ*(u*L^2) ≤ (integerFivePaths A B G e x c).card :=
    integerFivePaths_lower A B G e (mul_nonneg hu.le (sq_nonneg L))
      (Finset.mem_filter.mp hx).2 (fun b hb => hfour b hb c hc)
  have hbound := five_path_sum_bound A B C X G e (Finset.filter_subset _ _) hGB hlabels hpaths
  have hθlower : L*u/(2*(A.card : ℝ)) ≤ θ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGsize hL.le) (by positivity)
  have hcoeff : (ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2)/1048576 ≤ θ*(u*L^2) := by
    have he : (L*u/(2*(A.card : ℝ)))*(u*L^2) =
        (ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2)/1048576 := by
      dsimp [L,u]
      field_simp
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_right hθlower (mul_nonneg hu.le (sq_nonneg L))
  have hfinal := (mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg (X+G).card)).trans hbound
  refine ⟨X,Finset.filter_subset _ _,G,hGB,?_,hGsize,?_,?_⟩
  · have he : ρ^2*(A.card : ℝ)/64 = L/2 := by dsimp [L]; ring
    rwa [he]
  · nlinarith

  · intro x hx
    have hh : θ ≤ w x := (Finset.mem_filter.mp hx).2
    have he : θ = ρ^2*(G.card:ℝ)/64 := by
      dsimp [θ,L]
      field_simp
      ring
    rw [he] at hh
    exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ScalarGraphCoding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact graph transport under scalar quantization. The inverse is used
only on occupied cells of separated original sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem scalar_graph_coding_pointwise {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (C : Finset ℤ)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C) :
    ∃ d : ℤ → ℤ → Prop,
      (∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ)) =
        ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ) ∧
      (∀ u ∈ scalarCells δ A, ∀ v ∈ scalarCells δ B, d u v → u+v ∈ C) ∧
      ∀ a ∈ A, ∀ b ∈ B, d ⌊a/δ⌋ ⌊b/δ⌋ ↔ e a b := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let aInv := Function.invFunOn q (A : Set ℝ)
  let bInv := Function.invFunOn q (B : Set ℝ)
  let d : ℤ → ℤ → Prop := fun u v => e (aInv u) (bInv v)
  have hAi : Set.InjOn q (A : Set ℝ) := scalarCells_injective hδ hAsep
  have hBi : Set.InjOn q (B : Set ℝ) := scalarCells_injective hδ hBsep
  have haInv (a : ℝ) (ha : a ∈ A) : aInv (q a) = a := hAi.leftInvOn_invFunOn ha
  have hbInv (b : ℝ) (hb : b ∈ B) : bInv (q b) = b := hBi.leftInvOn_invFunOn hb
  have hneighbor (a : ℝ) (ha : a ∈ A) :
      integerNeighbors (scalarCells δ B) d (q a) = (B.filter fun b => e a b).image q := by
    ext v
    simp only [integerNeighbors,Finset.mem_filter]
    change (v ∈ B.image q ∧ d (q a) v) ↔ _
    simp only [Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨⟨b,hb,rfl⟩,he⟩
      have he' : e a b := by
        simpa only [d,haInv a ha,hbInv b hb] using he
      exact ⟨b,⟨hb,he'⟩,rfl⟩
    · rintro ⟨b,⟨hb,he⟩,rfl⟩
      refine ⟨⟨b,hb,rfl⟩,?_⟩
      simpa only [d,haInv a ha,hbInv b hb] using he
  have hneighborCard (a : ℝ) (ha : a ∈ A) :
      (integerNeighbors (scalarCells δ B) d (q a)).card = (B.filter fun b => e a b).card := by
    rw [hneighbor a ha]
    exact Finset.card_image_of_injOn (hBi.mono (Finset.filter_subset _ _))
  have hsum : (∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ)) =
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ) := by
    change (∑ u ∈ A.image q, _) = _
    rw [Finset.sum_image hAi]
    exact Finset.sum_congr rfl (fun a ha => by rw [hneighborCard a ha])
  have hlabels' : ∀ u ∈ scalarCells δ A, ∀ v ∈ scalarCells δ B, d u v → u+v ∈ C := by
    intro u hu v hv he
    change u ∈ A.image q at hu
    change v ∈ B.image q at hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    apply hlabels a ha b hb
    simpa only [d,haInv a ha,hbInv b hb] using he
  refine ⟨d,hsum,hlabels',?_⟩
  intro a ha b hb
  change d (q a) (q b) ↔ e a b
  simp only [d,haInv a ha,hbInv b hb]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarMixedRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-sided refinement for separated real sets. Large subsets of
the original sets have a small full sumset at the original scale. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem scalar_mixed_refinement_with_degrees {δ ρ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ) (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+b)/δ⌋ ∈ D) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (Y.card : ℝ) ∧
      ((scalarCells δ (X+Y)).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        67108864*(D.card : ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(Y.card:ℝ)/64 ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  classical
  let C := D ∪ D.image (fun z => z-1)
  have hC : (C.card : ℝ) ≤ 2*(D.card : ℝ) := by
    have h := (Finset.card_union_le D (D.image fun z => z-1)).trans
      (Nat.add_le_add_left (Finset.card_image_le (s := D)) D.card)
    have h' : C.card ≤ 2*D.card := by dsimp [C]; omega
    exact_mod_cast h'
  have hlabelC : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C := by
    intro a ha b hb he
    have hmem := hlabels a ha b hb he
    rw [add_div] at hmem
    rcases floor_add_carry (a/δ) (b/δ) with h | h
    · exact Finset.mem_union_left _ (h ▸ hmem)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⌊a/δ+b/δ⌋,hmem,by omega⟩)
  obtain ⟨d,hsum,hlabels',hpoint⟩ := scalar_graph_coding_pointwise hδ A B hAsep hBsep e C hlabelC
  have hAi := scalarCells_injective hδ hAsep
  have hBi := scalarCells_injective hδ hBsep
  have hAc : (scalarCells δ A).card = A.card := Finset.card_image_of_injOn hAi
  have hBc : (scalarCells δ B).card = B.card := Finset.card_image_of_injOn hBi
  have hdense' : ρ*((scalarCells δ A).card : ℝ)*((scalarCells δ B).card : ℝ) ≤
      ∑ a ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d a).card : ℝ) := by
    rw [hAc,hBc,hsum]
    exact hdense
  obtain ⟨S,hSA,T,hTB,hS,hT,hbound,hdegrees⟩ := integer_mixed_refinement_with_degrees
    (scalarCells δ A) (scalarCells δ B) C d
    (Finset.image_nonempty.mpr hA) (Finset.image_nonempty.mpr hB) hρ hdense' hlabels'
  obtain ⟨X,hXA,hXimage⟩ := Finset.subset_image_iff.mp hSA
  obtain ⟨Y,hYB,hYimage⟩ := Finset.subset_image_iff.mp hTB
  have hXc : X.card = S.card := by
    rw [← hXimage]
    exact (Finset.card_image_of_injOn (hAi.mono hXA)).symm
  have hYc : Y.card = T.card := by
    rw [← hYimage]
    exact (Finset.card_image_of_injOn (hBi.mono hYB)).symm
  have hsumcard := scalarCells_add_card δ X Y
  change (scalarCells δ (X+Y)).card ≤
    2*(X.image (fun x => ⌊x/δ⌋)+Y.image (fun x => ⌊x/δ⌋)).card at hsumcard
  rw [hXimage,hYimage] at hsumcard
  rw [hAc] at hS
  rw [hBc] at hT
  rw [hAc,hBc] at hbound
  refine ⟨X,hXA,Y,hYB,by simpa only [hXc] using hS,by simpa only [hYc] using hT,?_,?_⟩
  · have hsumR : ((scalarCells δ (X+Y)).card : ℝ) ≤ 2*((S+T).card : ℝ) := by
      exact_mod_cast hsumcard
    have hk : 0 ≤ ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2 := by positivity
    have hb := mul_le_mul_of_nonneg_right hsumR hk
    have hc5 : (C.card : ℝ)^5 ≤ (2*(D.card : ℝ))^5 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hC 5
    nlinarith
  · intro x hx
    have hxS : ⌊x/δ⌋ ∈ S := by
      rw [← hXimage]
      exact Finset.mem_image_of_mem _ hx
    have hd := hdegrees ⌊x/δ⌋ hxS
    have he : integerNeighbors T d ⌊x/δ⌋ =
        (Y.filter fun y => e x y).image (fun y => ⌊y/δ⌋) := by
      rw [← hYimage]
      ext v
      constructor
      · intro hv
        obtain ⟨hvT,hvd⟩ := Finset.mem_filter.mp hv
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hvT
        exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,
          (hpoint x (hXA hx) y (hYB hy)).1 hvd⟩,rfl⟩
      · intro hv
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hy,hye⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hy,
          (hpoint x (hXA hx) y (hYB hy)).2 hye⟩
    change ρ^2*(T.card:ℝ)/64 ≤ ((integerNeighbors T d ⌊x/δ⌋).card:ℝ) at hd
    rw [he,Finset.card_image_of_injOn (hBi.mono ((Finset.filter_subset _ _).trans hYB)),← hYc] at hd
    exact hd

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarRuzsaCovering
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ruzsa covering at a fixed scalar resolution, with actual centers
from the original set and an explicit rounding error. -/
namespace Falconer
open scoped Pointwise

theorem scalar_ruzsa_covering {δ K : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hB : B.Nonempty)
    (hsum : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ B).card) :
    ∃ F ⊆ A, (F.card : ℝ) ≤ 2*K ∧
      ∀ a ∈ A, ∃ f ∈ F, ∃ b ∈ B, ∃ c ∈ B, |a-(f+(b-c))| ≤ 2*δ := by
  classical
  have hsum' : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ B).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  obtain ⟨D,hDA,hD,hcover⟩ := Finset.ruzsa_covering_add
    (Finset.image_nonempty.mpr hB) hsum'
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  have hg (d : ℤ) (hd : d ∈ D) : g d ∈ A ∧ q (g d) = d :=
    Function.invFunOn_pos (Finset.mem_image.mp (hDA hd))
  let F := D.image g
  have hFA : F ⊆ A := by
    rintro f hf
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hf
    exact (hg d hd).1
  have hF : (F.card : ℝ) ≤ 2*K :=
    (Nat.cast_le.mpr (Finset.card_image_le (s := D) (f := g))).trans hD
  refine ⟨F,hFA,hF,?_⟩
  intro a ha
  have hqa : q a ∈ scalarCells δ A := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  obtain ⟨d,hd,z,hz,he⟩ := Finset.mem_add.mp (hcover hqa)
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_sub.mp hz
  obtain ⟨b,hb,hqb⟩ := Finset.mem_image.mp hu
  obtain ⟨c,hc,hqc⟩ := Finset.mem_image.mp hv
  refine ⟨g d,Finset.mem_image.mpr ⟨d,hd,rfl⟩,b,hb,c,hc,?_⟩
  have hqe : q a = q (g d)+q b-q c := by
    rw [(hg d hd).2]
    change q b = u at hqb
    change q c = v at hqc
    rw [hqb,hqc]
    omega
  have hqR : (q a : ℝ) = (q (g d) : ℝ)+(q b : ℝ)-(q c : ℝ) := by exact_mod_cast hqe
  have hqδ := congrArg (fun t : ℝ => t*δ) hqR
  have h0 (x : ℝ) : (q x : ℝ)*δ ≤ x := (le_div_iff₀ hδ).1 (Int.floor_le (x/δ))
  have h1 (x : ℝ) : x < ((q x : ℝ)+1)*δ := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x/δ))
  rw [abs_le]
  constructor <;> linarith [h0 a,h0 (g d),h0 b,h0 c,h1 a,h1 (g d),h1 b,h1 c]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarSmallSumCover
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small mixed sumset covers the other factor by few short intervals,
with centers and radius in the original scalar coordinates. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_small_sum_cover {δ R z c M K : ℝ} (hδ : 0 < δ)
    (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (F Y : Finset ℝ) (hF : F.Nonempty)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(F.card:ℝ)) :
    ∃ Q : Finset ℝ, (Q.card:ℝ) ≤ 2*K ∧
      ∀ y ∈ Y, ∃ q ∈ Q, |y-q| ≤ 4*M*R := by
  classical
  have hcard : (scalarCells δ F).card = F.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  have hs : ((scalarCells δ (Y.image (fun y => c*y)+F)).card:ℝ) ≤
      K*(scalarCells δ F).card := by
    rwa [add_comm,hcard]
  obtain ⟨D,hD,hDcard,hcover⟩ := scalar_ruzsa_covering hδ _ F hF hs
  refine ⟨D.image (fun d => d/c),?_,?_⟩
  · exact (Nat.cast_le.mpr (Finset.card_image_le (s := D))).trans hDcard
  · intro y hy
    obtain ⟨d,hd,u,hu,v,hv,he⟩ := hcover (c*y) (Finset.mem_image_of_mem _ hy)
    refine ⟨d/c,Finset.mem_image_of_mem _ hd,?_⟩
    have huv : |u-v| ≤ 2*R := by
      have hh := abs_sub_le u z v
      rw [abs_sub_comm z v] at hh
      linarith [hlocal u hu,hlocal v hv]
    have hcy : |c*y-d| ≤ 4*R := by
      have hh := abs_sub_le (c*y) (d+(u-v)) d
      have heq : d+(u-v)-d = u-v := by ring
      rw [heq] at hh
      linarith
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
    have heq : y-d/c = c⁻¹*(c*y-d) := by field_simp
    rw [heq,abs_mul]
    exact (mul_le_mul hM hcy (abs_nonneg _) hM0).trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphBallCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_dist_le_sum {x y z w R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : |x-z| ≤ R) (hy : |y-w| ≤ S) :
    dist (rowPoint x y) (rowPoint z w) ≤ R+S := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint x y) (rowPoint z w)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  have hx2 := mul_le_mul hx hx (abs_nonneg _) hR
  have hy2 := mul_le_mul hy hy (abs_nonneg _) hS
  nlinarith [sq_abs (x-z),sq_abs (y-w),mul_nonneg hR hS,
    dist_nonneg (x := rowPoint x y) (y := rowPoint z w)]

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

 theorem scalar_graph_ball_cover {δ t K R S z : ℝ}
    (F Y Q : Finset ℝ) (e : ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hδ : δ ≤ R+S)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hreg : NormalizedFiniteBallBound δ t K G)
    (hF : ∀ x ∈ F, |x-z| ≤ R)
    (hcover : ∀ y ∈ Y, ∃ q ∈ Q, |y-q| ≤ S)
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G) :
    (∑ x ∈ F, ((Y.filter fun y => e x y).card:ℝ)) ≤
      (Q.card:ℝ)*K*(R+S)^t*(G.card:ℝ) := by
  classical
  let A := (F ×ˢ Y).filter fun p => e p.1 p.2
  let H := A.image fun p => rowPoint p.1 p.2
  have hcard : H.card = ∑ x ∈ F, (Y.filter fun y => e x y).card := by
    rw [show H.card = A.card from Finset.card_image_of_injective _ rowPoint_pair_injective]
    simp only [A,Finset.card_filter,Finset.sum_product]
  let B := fun q => G.filter fun p => dist p (rowPoint z q) ≤ R+S
  have hsub : H ⊆ Q.biUnion B := by
    intro p hp
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨q,hq,hyq⟩ := hcover y hy
    exact Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_filter.mpr
      ⟨hgraph x hx y hy he,rowPoint_dist_le_sum hR hS (hF x hx) hyq⟩⟩
  have hc : (H.card:ℝ) ≤ ∑ q ∈ Q, ((B q).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hb (q : ℝ) : ((B q).card:ℝ) ≤ K*(R+S)^t*(G.card:ℝ) :=
    normalized_ball_bound_all_radii ht hK hreg _ _ hδ
  calc
    _ = (H.card:ℝ) := by rw [hcard,Nat.cast_sum]
    _ ≤ ∑ q ∈ Q, ((B q).card:ℝ) := hc
    _ ≤ ∑ _q ∈ Q, K*(R+S)^t*(G.card:ℝ) := Finset.sum_le_sum fun q _ => hb q
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphDensity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small mixed projections and retained graph degrees control the
concentration of the actual reference factor. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_graph_density_bound {δ R z c M K Kreg t ρ : ℝ}
    (hδ : 0 < δ) (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg)
    (F Y : Finset ℝ) (hF : F.Nonempty) (e : ℝ → ℝ → Prop)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hdegree : ∀ x ∈ F, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(F.card:ℝ)) :
    ρ*(F.card:ℝ)*(Y.card:ℝ) ≤
      2*K*Kreg*((1+4*M)*R)^t*(G.card:ℝ) := by
  obtain ⟨Q,hQ,hcover⟩ := scalar_small_sum_cover hδ hR hc hM F Y hF hsep hlocal hsum
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hR0 : 0 ≤ R := hδ.le.trans hR
  have hδ' : δ ≤ R+4*M*R := by nlinarith
  have hb := scalar_graph_ball_cover F Y Q e G hR0 (by positivity : 0 ≤ 4*M*R)
    hδ' ht hKreg hreg hlocal hcover hgraph
  calc
    _ = ∑ _x ∈ F, ρ*(Y.card:ℝ) := by simp; ring
    _ ≤ ∑ x ∈ F, ((Y.filter fun y => e x y).card:ℝ) := Finset.sum_le_sum hdegree
    _ ≤ (Q.card:ℝ)*Kreg*(R+4*M*R)^t*(G.card:ℝ) := hb
    _ = (Q.card:ℝ)*(Kreg*(R+4*M*R)^t*(G.card:ℝ)) := by ring
    _ ≤ (2*K)*(Kreg*(R+4*M*R)^t*(G.card:ℝ)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by rw [show R+4*M*R = (1+4*M)*R by ring]; ring

 theorem scalar_graph_density_relative {δ R z c M K Kreg t ρ N L : ℝ}
    (hδ : 0 < δ) (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg) (hK : 0 ≤ K) (hN : 0 < N) (hρ : 0 < ρ)
    (F Y : Finset ℝ) (hF : F.Nonempty) (hY : Y.Nonempty) (e : ℝ → ℝ → Prop)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hdegree : ∀ x ∈ F, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsize : (G.card:ℝ) ≤ L*N*(Y.card:ℝ))
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*N) :
    ((F.card:ℝ)/N)^2 ≤ (2*K*Kreg*L/ρ)*((1+4*M)*R)^t := by
  have hFpos : 0 < (F.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
  have hYpos : 0 < (Y.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  have hs : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤
      (K*N/(F.card:ℝ))*(F.card:ℝ) := by rwa [div_mul_cancel₀ _ hFpos.ne']
  have hb := scalar_graph_density_bound hδ hR hc hM ht hKreg F Y hF e G hreg
    hsep hlocal hdegree hgraph hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hKreg0 : 0 ≤ Kreg := zero_le_one.trans hKreg
  have hR0 : 0 ≤ R := hδ.le.trans hR
  have hrad : 0 ≤ ((1+4*M)*R)^t := Real.rpow_nonneg (by positivity) _
  have hm := mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 2*(K*N/(F.card:ℝ))*Kreg*((1+4*M)*R)^t by positivity)
  have hb' := mul_le_mul_of_nonneg_right (hb.trans hm) hFpos.le
  have heq : (2*(K*N/(F.card:ℝ))*Kreg*((1+4*M)*R)^t*(L*N*(Y.card:ℝ)))*(F.card:ℝ) =
      (2*K*Kreg*L*((1+4*M)*R)^t*N^2)*(Y.card:ℝ) := by field_simp
  rw [heq] at hb'
  have hcore : ρ*(F.card:ℝ)^2 ≤ 2*K*Kreg*L*((1+4*M)*R)^t*N^2 := by
    apply (mul_le_mul_iff_right₀ hYpos).1
    first | (convert hb' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hb'.trans (le_of_eq (by ring)))
  apply (mul_le_mul_iff_left₀ hρ).1
  have hh : (ρ*(F.card:ℝ)^2)/N^2 ≤ 2*K*Kreg*L*((1+4*M)*R)^t :=
    (div_le_iff₀ (sq_pos_of_pos hN)).2 hcore
  have heL : ρ*((F.card:ℝ)/N)^2 = (ρ*(F.card:ℝ)^2)/N^2 := by ring
  have heR : ρ*((2*K*Kreg*L/ρ)*((1+4*M)*R)^t) =
      2*K*Kreg*L*((1+4*M)*R)^t := by field_simp
  calc
    _ = (ρ*(F.card:ℝ)^2)/N^2 := by rw [mul_comm _ ρ,heL]
    _ ≤ 2*K*Kreg*L*((1+4*M)*R)^t := hh
    _ = _ := by rw [mul_comm _ ρ,heR]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphScalarRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dense small-projection graph transfers its planar ball bound to the
actual scalar reference set, with half the planar exponent. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_graph_ball_bound {δ t c M K Kreg ρ L : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (hK : 0 ≤ K) (hKreg : 1 ≤ Kreg) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (X Y : Finset ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hdegree : ∀ x ∈ X, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ X, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsize : (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ))
    (hsum : ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ)) :
    ∀ z r : ℝ, δ ≤ r →
      scalarBallMass X z r ≤
        Real.sqrt ((2*K*Kreg*L/ρ)*(1+4*M)^t)*r^(t/2)*(X.card:ℝ) := by
  classical
  intro z r hdr
  let F := X.filter fun x => |x-z| ≤ r
  have hr : 0 < r := hδ.trans_le hdr
  have hXpos : 0 < (X.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hKreg0 : 0 ≤ Kreg := zero_le_one.trans hKreg
  let C := (2*K*Kreg*L/ρ)*(1+4*M)^t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnonneg : 0 ≤ Real.sqrt C*r^(t/2) := by positivity
  by_cases hF : F.Nonempty
  · have hFsub : F ⊆ X := Finset.filter_subset _ _
    have hFsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
        (Finset.add_subset_add hFsub (Finset.Subset.refl _))))).trans hsum
    have hrelative := scalar_graph_density_relative hδ hdr hc hM ht hKreg hK hXpos hρ
      F Y hF hY e G hreg
      (fun x hx y hy hne => hsep x (hFsub hx) y (hFsub hy) hne)
      (fun _ hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => hdegree x (hFsub hx)) (fun x hx => hgraph x (hFsub hx)) hsize hFsum
    rw [Real.mul_rpow (by positivity : 0 ≤ 1+4*M) hr.le] at hrelative
    have hrel : ((F.card:ℝ)/(X.card:ℝ))^2 ≤ C*r^t := by
      convert hrelative using 1 <;> first | rfl | ring
    have he : (Real.sqrt C*r^(t/2))^2 = C*r^t := by
      rw [mul_pow,Real.sq_sqrt hC,← Real.rpow_mul_natCast hr.le]
      norm_num
    have hquot : (F.card:ℝ)/(X.card:ℝ) ≤ Real.sqrt C*r^(t/2) := by
      nlinarith
    exact (div_le_iff₀ hXpos).1 hquot
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonUnbalancedReference
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual regular common reference with comparable coordinate counts. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem common_unbalanced_regular_reference {α : Type*} {δ ρ K η t Kreg L Q : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hK : 0 ≤ K) (hQ : 1 ≤ Q) (hη : 0 < η)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg) (hL : 0 ≤ L)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : (X.card:ℝ) ≤ Q*(Y.card:ℝ))
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card:ℝ) ≤ ((A i).card:ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card:ℝ) ≤ ((B i).card:ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card:ℝ) ≤
      K*(X.card:ℝ))
    (e : α → ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hdegree : ∀ i ∈ I, ∀ x ∈ A i,
      η*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ))
    (hgraph : ∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G)
    (hGsize : (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card:ℝ) ≤ 2*(J.card:ℝ) ∧ (A i₀).Nonempty ∧
      ((scalarCells δ (A i₀+A i₀)).card:ℝ) ≤
        (1024*(2*M+3)^2*K^4*Q^2/ρ^6)*(scalarCells δ (A i₀)).card ∧
      (∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card:ℝ) ≤
          (4096*(2*(M*M)+3)*(2*M+3)^2*K^4*Q^2/ρ^13)*(scalarCells δ (A i₀)).card) ∧
      ∀ u r : ℝ, δ ≤ r → scalarBallMass (A i₀) u r ≤
        Real.sqrt ((2*(K/ρ)*Kreg*(L/ρ^2)/η)*(1+4*(M:ℝ))^t)*
          r^(t/2)*((A i₀).card:ℝ) := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hr⟩ := common_unbalanced_ratio_projections
    hδ hρ hK hQ I X Y A B c hI hX hY hXY hXsep hYsep hA hB hsizeA hsizeB M hc hproj
  refine ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hr,?_⟩
  have hYpos : 0 < (Y.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  have hBi : (B i₀).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hρ hYpos).trans_le (hsizeB i₀ hi₀)))
  have hXA : (X.card:ℝ) ≤ ((A i₀).card:ℝ)/ρ :=
    (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hsizeA i₀ hi₀)
  have hYB : (Y.card:ℝ) ≤ ((B i₀).card:ℝ)/ρ :=
    (le_div_iff₀ hρ).2 (by simpa only [mul_comm] using hsizeB i₀ hi₀)
  have hGp : (G.card:ℝ) ≤ (L/ρ^2)*((A i₀).card:ℝ)*((B i₀).card:ℝ) := by
    calc
      _ ≤ L*(X.card:ℝ)*(Y.card:ℝ) := hGsize
      _ = L*((X.card:ℝ)*(Y.card:ℝ)) := by ring
      _ ≤ L*((((A i₀).card:ℝ)/ρ)*(((B i₀).card:ℝ)/ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hXA hYB (Nat.cast_nonneg _)
          (by positivity)) hL
      _ = _ := by ring
  have hsmall : ((scalarCells δ (A i₀+(B i₀).image (fun y => c i₀*y))).card:ℝ) ≤
      (K/ρ)*((A i₀).card:ℝ) := by
    calc
      _ ≤ K*(X.card:ℝ) := hproj i₀ hi₀
      _ ≤ K*(((A i₀).card:ℝ)/ρ) := mul_le_mul_of_nonneg_left hXA hK
      _ = _ := by ring
  exact scalar_graph_ball_bound hδ ht (hc i₀ hi₀).1 (hc i₀ hi₀).2.2
    (div_nonneg hK hρ.le) hKreg hη (div_nonneg hL (sq_nonneg _))
    (A i₀) (B i₀) hAi hBi
    (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne)
    (e i₀) G hreg (hdegree i₀ hi₀) (hgraph i₀ hi₀) hGp hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientMul
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplying coefficients with small scalar sumsets, with the
rounding cost controlled by an explicit bound for the first coefficient. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_mul {δ K a b : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (M : ℕ) (haM : |a| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hb : ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (3584*(4*(M : ℝ)+11))*K^8*(scalarCells δ X).card := by
  classical
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hb' : ((scalarCells δ (X.image (fun x => b*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact hb
  obtain ⟨Fa,_,hFa,hca⟩ := scalar_ruzsa_covering hδ (X.image fun x => a*x) X hX ha'
  obtain ⟨Fb,_,hFb,hcb⟩ := scalar_ruzsa_covering hδ (X.image fun x => b*x) X hX hb'
  let F := (Fb.image fun f => a*f)+Fa-Fa
  let Z := 3 • X-2 • X
  have hcover : ∀ p ∈ X+X.image (fun x => (a*b)*x),
      ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ (2*M+4 : ℕ)*δ := by
    intro p hp
    obtain ⟨x,hx,t,ht,rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨fb,hfb,u,hu,v,hv,heb⟩ := hcb (b*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    obtain ⟨f₁,hf₁,u₁,hu₁,v₁,hv₁,he₁⟩ := hca (a*u) (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    obtain ⟨f₂,hf₂,u₂,hu₂,v₂,hv₂,he₂⟩ := hca (a*v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    have hf : a*fb+f₁-f₂ ∈ F := Finset.sub_mem_sub
      (Finset.add_mem_add (Finset.mem_image.mpr ⟨fb,hfb,rfl⟩) hf₁) hf₂
    have h3 : x+u₁+v₂ ∈ 3 • X := by
      have hm := Finset.add_mem_add (Finset.add_mem_add hx hu₁) hv₂
      simpa only [show (3 : ℕ) = 2+1 from rfl,add_nsmul,one_nsmul,two_nsmul] using hm
    have h2 : v₁+u₂ ∈ 2 • X := by simpa only [two_nsmul] using Finset.add_mem_add hv₁ hu₂
    refine ⟨a*fb+f₁-f₂,hf,(x+u₁+v₂)-(v₁+u₂),Finset.sub_mem_sub h3 h2,?_⟩
    have he₀ : |a*(b*y-(fb+(u-v)))| ≤ 2*(M : ℝ)*δ := by
      rw [abs_mul]
      have hh := mul_le_mul haM heb (abs_nonneg _) (Nat.cast_nonneg M)
      nlinarith
    have htri : |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂)))| ≤
        |a*(b*y-(fb+(u-v)))|+|a*u-(f₁+(u₁-v₁))|+|a*v-(f₂+(u₂-v₂))| := by
      calc
        _ ≤ |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))|+
            |-(a*v-(f₂+(u₂-v₂)))| := by
          simpa only [sub_eq_add_neg] using abs_add_le
            (a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))) (-(a*v-(f₂+(u₂-v₂))))
        _ ≤ _ := by
          rw [abs_neg]
          exact add_le_add (abs_add_le
            (a*(b*y-(fb+(u-v)))) (a*u-(f₁+(u₁-v₁)))) le_rfl
    have heq : x+(a*b)*y-((a*fb+f₁-f₂)+((x+u₁+v₂)-(v₁+u₂))) =
        a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂))) := by ring
    rw [heq]
    push_cast
    linarith
  have hcNat := scalarCells_translate_cover hδ (X+X.image (fun x => (a*b)*x)) F Z (2*M+4) hcover
  have hc : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := by
    have hh : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
        2*(2*((2*(M : ℝ))+4)+3)*(F.card : ℝ)*(scalarCells δ Z).card := by exact_mod_cast hcNat
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hFc : (F.card : ℝ) ≤ (Fb.card : ℝ)*(Fa.card : ℝ)*(Fa.card : ℝ) := by
    have hn := (Finset.card_sub_le (s := (Fb.image fun f => a*f)+Fa) (t := Fa)).trans
      (Nat.mul_le_mul_right Fa.card ((Finset.card_add_le (s := Fb.image fun f => a*f) (t := Fa)).trans
        (Nat.mul_le_mul_right Fa.card (Finset.card_image_le (s := Fb)))))
    exact_mod_cast hn
  have hF : (F.card : ℝ) ≤ 8*K^3 := by
    have h1 := mul_le_mul hFb hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ 2*K)
    have h2 := mul_le_mul h1 hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ (2*K)*(2*K))
    exact hFc.trans (h2.trans_eq (by ring))
  have hZ : ((scalarCells δ Z).card : ℝ) ≤ 7*(2*K)^5*(scalarCells δ X).card := by
    have hz := scalar_pluennecke δ X X hX hdoubling 3 2
    norm_num only at hz
    exact hz
  calc
    _ ≤ (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := hc
    _ ≤ ((2*(4*(M : ℝ)+11))*(8*K^3))*(7*(2*K)^5*(scalarCells δ X).card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by positivity)) hZ
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDilatedRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-sum refinement with the second factor kept in its original
coordinates. Both the exact graph and all retained degrees are transported. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_dilation_filter {c : ℝ} (hc : c ≠ 0) (B : Finset ℝ) (p : ℝ → Prop) :
    (B.image (fun y => c*y)).filter (fun v => p (v/c)) =
      (B.filter p).image (fun y => c*y) := by
  classical
  have he (y : ℝ) : c*y/c = y := by field_simp
  ext v
  constructor
  · intro hv
    obtain ⟨hv,hp⟩ := Finset.mem_filter.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    rw [he] at hp
    exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hp⟩,rfl⟩
  · intro hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hy,hp⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hy,by rwa [he]⟩

 theorem scalar_dilation_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (fun y : ℝ => c*y) := by
  intro x y h
  have hh := congrArg (fun v => v/c) h
  have he (z : ℝ) : c*z/c = z := by field_simp
  simpa only [he] using hh

 theorem scalar_dilated_refinement {δ ρ c : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hc : c ≠ 0)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B.image (fun y => c*y), ∀ y ∈ B.image (fun y => c*y), x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ)
    (hdense : ρ*(A.card:ℝ)*(B.card:ℝ) ≤ ∑ a ∈ A, ((B.filter fun b => e a b).card:ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+c*b)/δ⌋ ∈ D) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ρ^2*(A.card:ℝ)/64 ≤ (X.card:ℝ) ∧ ρ*(B.card:ℝ)/4 ≤ (Y.card:ℝ) ∧
      ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ)*(ρ^8*(A.card:ℝ)^2*(B.card:ℝ)^2) ≤
        67108864*(D.card:ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(Y.card:ℝ)/64 ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  classical
  have hinj := scalar_dilation_injective hc
  have he (y : ℝ) : c*y/c = y := by field_simp
  have hcard (V : Finset ℝ) : (V.image (fun y => c*y)).card = V.card :=
    Finset.card_image_of_injective V hinj
  have hcount (V : Finset ℝ) (x : ℝ) :
      ((V.image (fun y => c*y)).filter (fun v => e x (v/c))).card =
        (V.filter fun y => e x y).card := by
    rw [scalar_dilation_filter hc,hcard]
  have hd : ρ*(A.card:ℝ)*((B.image (fun y => c*y)).card:ℝ) ≤
      ∑ a ∈ A, (((B.image (fun y => c*y)).filter fun v => e a (v/c)).card:ℝ) := by
    simp only [hcard,hcount]
    exact hdense
  have hl : ∀ a ∈ A, ∀ v ∈ B.image (fun y => c*y), e a (v/c) → ⌊(a+v)/δ⌋ ∈ D := by
    intro a ha v hv hev
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    rw [he] at hev
    exact hlabels a ha b hb hev
  obtain ⟨X,hXA,V,hVB,hX,hV,hsum,hdegrees⟩ := scalar_mixed_refinement_with_degrees hδ
    A (B.image (fun y => c*y)) hA (hB.image _) hAsep hBsep
    (fun x v => e x (v/c)) D hρ hd hl
  obtain ⟨Y,hYB,hYimage⟩ := Finset.subset_image_iff.mp hVB
  have hYc : V.card = Y.card := by rw [← hYimage,hcard]
  rw [hcard] at hV hsum
  refine ⟨X,hXA,Y,hYB,hX,by simpa only [hYc] using hV,?_,?_⟩
  · simpa only [hYimage] using hsum
  · intro x hx
    have hh := hdegrees x hx
    rw [← hYimage,hcount,hcard] at hh
    exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarZoom
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite scalar zooming and its ball-count identity. -/
namespace Falconer

 theorem scalarZoom_injective {z R : ℝ} (hR : R ≠ 0) :
    Function.Injective (fun x : ℝ => (x-z)/R) := by
  intro x y h
  have hh := congrArg (fun t : ℝ => t*R) h
  simp only [div_mul_cancel₀ _ hR] at hh
  linarith

 theorem scalarZoom_card {z R : ℝ} (hR : R ≠ 0) (E : Finset ℝ) :
    (scalarZoom z R E).card = E.card :=
  Finset.card_image_of_injective _ (scalarZoom_injective hR)

 theorem scalarZoom_ball_iff {z R u r x : ℝ} (hR : 0 < R) :
    |(x-z)/R-u| ≤ r ↔ |x-(z+R*u)| ≤ R*r := by
  have he : (x-z)/R-u = (x-(z+R*u))/R := by field_simp; ring
  rw [he,abs_div,abs_of_pos hR,div_le_iff₀ hR]
  rw [mul_comm r R]

 theorem scalarZoom_ball_mass {z R : ℝ} (hR : 0 < R) (E : Finset ℝ) (u r : ℝ) :
    scalarBallMass (scalarZoom z R E) u r = scalarBallMass E (z+R*u) (R*r) := by
  classical
  have he : (scalarZoom z R E).filter (fun x => |x-u| ≤ r) =
      (E.filter fun x => |x-(z+R*u)| ≤ R*r).image (fun x => (x-z)/R) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyE,hyB⟩ := Finset.mem_filter.mp hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyE
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,(scalarZoom_ball_iff hR).1 hyB⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxE,hxB⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hxE,rfl⟩,(scalarZoom_ball_iff hR).2 hxB⟩
  unfold scalarBallMass
  rw [he,Finset.card_image_of_injective _ (scalarZoom_injective hR.ne')]

 theorem scalarZoom_separated {δ z R : ℝ} (hR : 0 < R) (E : Finset ℝ)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|) :
    ∀ x ∈ scalarZoom z R E, ∀ y ∈ scalarZoom z R E, x ≠ y → δ/R ≤ |x-y| := by
  intro x hx y hy hne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by intro h; apply hne; rw [h]
  rw [← sub_div,show (a-z)-(b-z) = a-b by ring,abs_div,abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hsep a ha b hb hab) hR.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRatioFamily
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting and ball regularity for the actual ratio coefficients retained
by the common-rectangle selection. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_ball_bound_all_radii {δ s K : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s)
    (E : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ K*r^s*(E.card:ℝ))
    (u r : ℝ) (hr : δ ≤ r) : scalarBallMass E u r ≤ K*r^s*(E.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hball u r hr hr1
  · have hp : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr1) hs
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hc : scalarBallMass E u r ≤ (E.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hf : 1 ≤ K*r^s := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) E.card])

 theorem scalar_ratio_family_card {c : ℝ} (hc : c ≠ 0) (J : Finset ℝ) :
    (J.image (fun y => -y/c)).card = J.card := by
  apply Finset.card_image_of_injective
  intro x y h
  have hh := congrArg (fun a => a*c) h
  simp only [div_mul_cancel₀ _ hc] at hh
  linarith

 theorem scalar_ratio_family_ball {δ s K A M c : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hM : 1 ≤ M) (hc : c ≠ 0) (hcM : |c| ≤ M)
    (I J : Finset ℝ) (hJI : J ⊆ I) (hsize : (I.card:ℝ) ≤ A*(J.card:ℝ))
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^s*(I.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ r →
      scalarBallMass (J.image (fun y => -y/c)) u r ≤
        (A*K*M^s)*r^s*((J.image (fun y => -y/c)).card:ℝ) := by
  classical
  intro u r hr
  have hr0 : 0 < r := hδ.trans_le hr
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let F := I.filter fun y => |y-(-c*u)| ≤ M*r
  have hsub : (J.image (fun y => -y/c)).filter (fun a => |a-u| ≤ r) ⊆
      F.image (fun y => -y/c) := by
    intro a ha
    obtain ⟨ha,hnear⟩ := Finset.mem_filter.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hJI hy,?_⟩,rfl⟩
    have he : y-(-c*u) = -c*((-y/c)-u) := by field_simp; ring
    rw [he,abs_mul,abs_neg]
    exact mul_le_mul hcM hnear (abs_nonneg _) hM0
  have hcount : scalarBallMass (J.image (fun y => -y/c)) u r ≤ scalarBallMass I (-c*u) (M*r) := by
    change (((J.image (fun y => -y/c)).filter (fun a => |a-u| ≤ r)).card:ℝ) ≤ (F.card:ℝ)
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hdr : δ ≤ M*r := by nlinarith
  have hb := scalar_ball_bound_all_radii hK hs I hball (-c*u) (M*r) hdr
  have hm := mul_le_mul_of_nonneg_left hsize (show 0 ≤ K*(M*r)^s by positivity)
  rw [Real.mul_rpow hM0 hr0.le] at hb hm
  rw [scalar_ratio_family_card hc]
  calc
    _ ≤ scalarBallMass I (-c*u) (M*r) := hcount
    _ ≤ K*(M^s*r^s)*(I.card:ℝ) := hb
    _ ≤ K*(M^s*r^s)*(A*(J.card:ℝ)) := hm
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSmallZoomMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balls below the rescaled original resolution remain controlled by
 the exponent reserve in the original coefficient Frostman estimate. -/
namespace Falconer

 theorem scalarBallMass_radius_mono (E : Finset ℝ) (u : ℝ) {r s : ℝ} (h : r ≤ s) :
    scalarBallMass E u r ≤ scalarBallMass E u s := by
  unfold scalarBallMass
  have hs : E.filter (fun x => |x-u| ≤ r) ⊆ E.filter (fun x => |x-u| ≤ s) := by
    intro x hx
    obtain ⟨hxE,hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxE,hxr.trans h⟩
  exact_mod_cast Finset.card_le_card hs

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarResolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing scalar covering and ball counts at two nearby resolutions. -/
namespace Falconer

 theorem scalar_refined_ball_bound {δ ρ C K s : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1)
    (hC : 1 ≤ C) (hscale : ρ ≤ C*δ) (hK : 0 ≤ K) (hs : 0 ≤ s) (X : Finset ℝ)
    (hball : ∀ u r : ℝ, ρ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ K*r^s*(X.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤
      (C^s*K)*r^s*(X.card:ℝ) := by
  intro u r hr hr1
  have hr0 : 0 < r := hδ.trans_le hr
  have hb := hball u (max r ρ) (le_max_right _ _) (max_le hr1 hρ1)
  have hm := scalarBallMass_radius_mono X u (le_max_left r ρ)
  have hmax : max r ρ ≤ C*r := by
    apply max_le
    · nlinarith
    · exact hscale.trans (mul_le_mul_of_nonneg_left hr (by linarith))
  have hp := Real.rpow_le_rpow (le_trans hr0.le (le_max_left _ _)) hmax hs
  rw [Real.mul_rpow (by linarith : 0 ≤ C) hr0.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Nat.cast_nonneg X.card))
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarScaleAlignment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Align any fine dyadic resolution with a fixed block width. The
 difference is at most one block and all covering losses stay fixed. -/
namespace Falconer

 theorem scalar_fixed_losses {η C D : ℝ} (hη : 0 < η) (hC : 0 < C) (hD : 0 < D) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) ∧
      D*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (max (Real.log C) (Real.log D)/((3*η/4)*Real.log 2)))
  have hNpos : 0 < N0 := by
    have hh := (le_max_left _ _).trans_lt hN0
    exact_mod_cast (show (0:ℝ) < N0 by linarith)
  have hbase : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hN0)
    nlinarith
  refine ⟨N0,hNpos,?_⟩
  intro N hN
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN)
    (show 0 ≤ (3*η/4)*Real.log 2 by positivity)
  have hmax : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N:ℝ)*Real.log 2 := by nlinarith
  constructor
  · calc
      _ = Real.exp (Real.log C+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hC]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_left (Real.log C) (Real.log D)])
  · calc
      _ = Real.exp (Real.log D+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hD]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_right (Real.log C) (Real.log D)])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ScalarAffineCovers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and positive zooming preserve scalar cell counts up to
 the single carry in a translated grid. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_translation_cells (δ b : ℝ) (X : Finset ℝ) :
    (scalarCells δ (X.image (fun x => x+b))).card ≤ 2*(scalarCells δ X).card := by
  have he : X.image (fun x => x+b) = X+{b} := by
    ext z
    simp only [Finset.mem_image,Finset.mem_add,Finset.mem_singleton]
    aesop
  rw [he]
  have hh := scalarCells_add_card δ X {b}
  have hc : (scalarCells δ X+scalarCells δ {b}).card ≤ (scalarCells δ X).card := by
    simpa only [scalarCells,Finset.image_singleton,Finset.card_singleton,mul_one] using
      (Finset.card_add_le (s := scalarCells δ X) (t := scalarCells δ {b}))
  exact hh.trans (Nat.mul_le_mul_left 2 hc)

 theorem scalar_zoom_cells {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (z : ℝ) (X : Finset ℝ) :
    (scalarCells (δ/R) (scalarZoom z R X)).card ≤ 2*(scalarCells δ X).card := by
  have he : scalarCells (δ/R) (scalarZoom z R X) =
      scalarCells δ (X.image (fun x => x+(-z))) := by
    unfold scalarCells scalarZoom
    rw [Finset.image_image,Finset.image_image]
    apply Finset.image_congr
    intro x _
    change ⌊((x-z)/R)/(δ/R)⌋ = ⌊(x+(-z))/δ⌋
    congr 1
    field_simp
    ring
  rw [he]
  exact scalar_translation_cells δ (-z) X

 theorem scalar_zoom_linear_sum (z R a : ℝ) (X : Finset ℝ) :
    scalarZoom z R X+(scalarZoom z R X).image (fun x => a*x) =
      scalarZoom ((1+a)*z) R (X+X.image (fun x => a*x)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨x+a*y,Finset.add_mem_add hx (Finset.mem_image.mpr ⟨y,hy,rfl⟩),?_⟩
    ring
  · intro ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_add.mpr ⟨(x-z)/R,Finset.mem_image.mpr ⟨x,hx,rfl⟩,
      a*((y-z)/R),Finset.mem_image.mpr ⟨(y-z)/R,Finset.mem_image.mpr ⟨y,hy,rfl⟩,rfl⟩,?_⟩
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarZoomBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ball transfer through the fixed scalar zoom into the unit interval. -/
namespace Falconer

 theorem scalar_zoom_ball_bound {δ R K s : ℝ} (hδ : 0 < δ) (hR : 1 ≤ R)
    (hK : 1 ≤ K) (hs : 0 ≤ s) (z : ℝ) (X : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ K*r^s*(X.card:ℝ)) :
    ∀ u r : ℝ, δ/R ≤ r → r ≤ 1 → scalarBallMass (scalarZoom z R X) u r ≤
      (R^s*K)*r^s*((scalarZoom z R X).card:ℝ) := by
  have hR0 : 0 < R := by linarith
  intro u r hr _
  have hr0 : 0 < r := (div_pos hδ hR0).trans_le hr
  rw [scalarZoom_ball_mass hR0,scalarZoom_card hR0.ne']
  by_cases hsmall : R*r ≤ 1
  · have hδr : δ ≤ R*r := by
      have hh := (div_le_iff₀ hR0).1 hr
      nlinarith
    have hh := hball (z+R*u) (R*r) hδr hsmall
    rw [Real.mul_rpow hR0.le hr0.le] at hh
    nlinarith
  · have hcount : scalarBallMass X (z+R*u) (R*r) ≤ (X.card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast Finset.card_filter_le _ _
    have hp : 1 ≤ (R*r)^s := Real.one_le_rpow (le_of_not_ge hsmall) hs
    rw [Real.mul_rpow hR0.le hr0.le] at hp
    have hfactor : 1 ≤ R^s*K*r^s := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg X.card)
    nlinarith

 theorem scalar_quarter_zoom_unit (X : Finset ℝ) (hX : ∀ x ∈ X, |x| ≤ 1) :
    ∀ y ∈ scalarZoom (-2) 4 X, 0 ≤ y ∧ y < 1 := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have hh := abs_le.mp (hX x hx)
  constructor <;> linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarBoundedProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar projection theorem for arbitrary bounded real point sets,
 at every sufficiently fine dyadic resolution. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_bounded_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨η,N0,hη,hN0,hprojection⟩ := scalar_dyadic_projection hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη (by norm_num : (0:ℝ) < 2)
    (by positivity : (0:ℝ) < (4:ℝ)^(2*κ))
  refine ⟨η/4,max N0 N1,by positivity,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXbound hsep hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^N
  let W := Real.exp ((η/4)*(N:ℝ)*Real.log 2)
  let Wf := Real.exp (η*(N+2:ℕ)*Real.log 2)
  let Y := scalarZoom (-2) 4 X
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδf : (1/2:ℝ)^(N+2) = δ/4 := by
    rw [pow_add]
    dsimp [δ]
    norm_num
    ring
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hExp : Real.exp (η*(N:ℝ)*Real.log 2) ≤ Wf := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  obtain ⟨hcover,hball⟩ := hloss N ((le_max_right _ _).trans hN)
  have hcover' : 2*W ≤ Wf := hcover.trans hExp
  have hball' : (4:ℝ)^(2*κ)*W ≤ Wf := hball.trans hExp
  have hpointFactor : (4:ℝ)^κ*W ≤ Wf :=
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) hW.le).trans hball'
  have hYcard : Y.card = X.card := scalarZoom_card (by norm_num) X
  have hYne : Y.Nonempty := hX.image _
  have hYunit : ∀ y ∈ Y, 0 ≤ y ∧ y < 1 := scalar_quarter_zoom_unit X hXbound
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → (1/2:ℝ)^(N+2) ≤ |x-y| := by
    rw [hδf]
    exact scalarZoom_separated (by norm_num) X hsep
  have htransfer (a : ℝ) : ((scalarCells ((1/2:ℝ)^(N+2)) (Y+Y.image (fun x => a*x))).card:ℝ) ≤
      2*((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
    dsimp only [Y]
    rw [hδf,scalar_zoom_linear_sum]
    exact_mod_cast scalar_zoom_cells hδ (by norm_num : (0:ℝ) < 4) ((1+a)*(-2))
      (X+X.image (fun x => a*x))
  have hYdouble : ((scalarCells ((1/2:ℝ)^(N+2)) (Y+Y)).card:ℝ) ≤ Wf*(Y.card:ℝ) := by
    have hh := htransfer 1
    simp only [one_mul,Finset.image_id'] at hh
    rw [hYcard]
    have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
    nlinarith
  have hYballs : ∀ u r : ℝ, (1/2:ℝ)^(N+2) ≤ r → r ≤ 1 →
      scalarBallMass Y u r ≤ Wf*r^κ*(Y.card:ℝ) := by
    intro u r hr hr1
    rw [hδf] at hr
    have hh := scalar_zoom_ball_bound hδ (by norm_num : (1:ℝ) ≤ 4) hW1 hκ.le (-2) X hpoint u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hpointFactor
      (mul_nonneg (Real.rpow_nonneg ((div_pos hδ (by norm_num)).le.trans hr) κ) (Nat.cast_nonneg Y.card))
    nlinarith
  have hEballs : ∀ u r : ℝ, (1/2:ℝ)^(N+2) ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ Wf*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    rw [hδf] at hr
    have hh := scalar_refined_ball_bound (div_pos hδ (by norm_num)) hδ1
      (by norm_num : (1:ℝ) ≤ 4) (by linarith : δ ≤ 4*(δ/4)) hW.le
      (by linarith : 0 ≤ 2*κ) E hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hball'
      (mul_nonneg (Real.rpow_nonneg ((div_pos hδ (by norm_num)).le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  have hYsize : Real.log (Y.card:ℝ) ≤ (1-κ)*(N+2:ℕ)*Real.log 2 := by
    rw [hYcard]
    push_cast
    have hh : 0 ≤ (1-κ)*Real.log 2 := mul_nonneg (sub_nonneg.mpr hκ1)
      (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection (N+2) (by omega) Y hYne hYunit hYsep hYsize
    hYdouble hYballs E hE hEbound hEballs
  by_contra hn
  push Not at hn
  have hh := htransfer a
  have hp := hn a ha
  have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
  rw [hYcard] at hgain
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarReferenceObstruction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular reference set cannot have small projections in every retained
ratio direction. All assumptions are finite-set counts at the original scale. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_negative_sum (X : Finset ℝ) (a : ℝ) :
    X+X.image (fun x => (-a)*x) = X-X.image (fun x => a*x) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sub.mpr ⟨x,hx,a*y,Finset.mem_image_of_mem _ hy,by ring⟩
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_add.mpr ⟨x,hx,(-a)*y,Finset.mem_image_of_mem _ hy,by ring⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarUnbalancedRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense-graph refinement without equal cardinalities for the coordinate
sets. The explicit cost is the square of their cardinality ratio. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_unbalanced_projection_bound {S N P Q D V : ℝ}
    (hS : 0 < S) (hN : 0 < N) (hP : 0 < P) (hD : 0 ≤ D)
    (hcard : D ≤ S*N) (hNP : N ≤ Q*P)
    (hbound : V*((S⁻¹)^8*N^2*P^2) ≤ 67108864*D^5) :
    V ≤ 67108864*S^13*Q^2*N := by
  have hNP2 : N^2 ≤ Q^2*P^2 := by
    have hh := pow_le_pow_left₀ hN.le hNP 2
    nlinarith
  have hcore : V*(S⁻¹)^8 ≤ 67108864*S^5*N*Q^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hP))).1
    calc
      _ = V*((S⁻¹)^8*N^2*P^2) := by ring
      _ ≤ 67108864*D^5 := hbound
      _ ≤ 67108864*(S*N)^5 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hcard 5) (by norm_num)
      _ = (67108864*S^5*N^3)*N^2 := by ring
      _ ≤ (67108864*S^5*N^3)*(Q^2*P^2) := mul_le_mul_of_nonneg_left hNP2 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (67108864*S^5*N*Q^2)/(S⁻¹)^8 :=
      (le_div_iff₀ (by positivity : 0 < (S⁻¹)^8)).2 hcore
    _ = _ := by field_simp

 theorem scalar_dilated_unbalanced_refinement {δ S c Q : ℝ}
    (hδ : 0 < δ) (hS : 1 ≤ S) (hc : c ≠ 0)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : (A.card:ℝ) ≤ Q*(B.card:ℝ))
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B.image (fun y => c*y), ∀ y ∈ B.image (fun y => c*y), x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ)
    (hdense : S⁻¹*(A.card:ℝ)*(B.card:ℝ) ≤ ∑ a ∈ A, ((B.filter fun b => e a b).card:ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+c*b)/δ⌋ ∈ D)
    (hcard : (D.card:ℝ) ≤ S*(A.card:ℝ)) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ((S⁻¹)^2/64)*(A.card:ℝ) ≤ (X.card:ℝ) ∧
      ((S⁻¹)^2/64)*(B.card:ℝ) ≤ (Y.card:ℝ) ∧
      ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ) ≤ 67108864*S^13*Q^2*(A.card:ℝ) ∧
      ∀ x ∈ X, ((S⁻¹)^2/64)*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  obtain ⟨X,hXA,Y,hYB,hX,hY,hproj,hdegree⟩ := scalar_dilated_refinement
    hδ (inv_pos.mpr hSpos) hc A B hA hB hAsep hBsep e D hdense hlabels
  have hN : 0 < (A.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hP : 0 < (B.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  have hproj' := scalar_unbalanced_projection_bound hSpos hN hP (Nat.cast_nonneg _)
    hcard hAB hproj
  have hρ1 : S⁻¹ ≤ 1 := (inv_le_one₀ hSpos).2 hS
  have hρ0 : 0 ≤ S⁻¹ := (inv_pos.mpr hSpos).le
  have hρ2 : (S⁻¹)^2 ≤ S⁻¹ := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hρ2 (Nat.cast_nonneg (α := ℝ) B.card)
  refine ⟨X,hXA,Y,hYB,?_,?_,hproj',?_⟩
  · nlinarith
  · nlinarith
  · intro x hx
    have hd := hdegree x hx
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarMaxRatioProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalizing by an actual coefficient of magnitude at least one costs
only a fixed polynomial, even when the coefficient radius grows with scale. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_max_ratio_projection {δ K a b : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (ha : |a| ≤ K) (hb : 1 ≤ |b|)
    (hd : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hpa : ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hpb : ((scalarCells δ (X+X.image (fun x => b*x))).card:ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a/b)*x))).card:ℝ) ≤
      (68096*(5:ℝ)^8)*K^9*(scalarCells δ X).card := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hbpos : 0 < |b| := zero_lt_one.trans_le hb
  have hbne : b ≠ 0 := abs_pos.mp hbpos
  have hbinv : |b⁻¹| ≤ (1:ℝ) := by
    rw [abs_inv]
    exact (inv_le_one₀ hbpos).2 hb
  have hi := scalar_inverse_coefficient_cells hδ hbne X 1 (by simpa only [Nat.cast_one] using hbinv)
  have hiR : ((scalarCells δ (X+X.image (fun x => b⁻¹*x))).card:ℝ) ≤
      5*((scalarCells δ (X+X.image (fun x => b*x))).card:ℝ) := by exact_mod_cast hi
  have hib : ((scalarCells δ (X+X.image (fun x => b⁻¹*x))).card:ℝ) ≤
      (5*K)*(scalarCells δ X).card :=
    hiR.trans ((mul_le_mul_of_nonneg_left hpb (by norm_num)).trans_eq (by ring))
  let m := ⌈K⌉₊
  have hmlo : K ≤ (m:ℝ) := Nat.le_ceil K
  have hmhi : (m:ℝ) ≤ 2*K := by
    have hh := Nat.ceil_lt_add_one hK0
    change (m:ℝ) < K+1 at hh
    linarith
  have hK5 : K ≤ 5*K := by linarith
  have hm := scalar_coefficient_mul hδ (by positivity : 0 ≤ 5*K) X hX m (ha.trans hmlo)
    (hd.trans (mul_le_mul_of_nonneg_right hK5 (Nat.cast_nonneg _)))
    (hpa.trans (mul_le_mul_of_nonneg_right hK5 (Nat.cast_nonneg _))) hib
  have hf : 3584*(4*(m:ℝ)+11) ≤ 68096*K := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hf (show 0 ≤ (5*K)^8*(scalarCells δ X).card by positivity)
  calc
    _ ≤ (3584*(4*(m:ℝ)+11))*(5*K)^8*(scalarCells δ X).card := by
      simpa only [div_eq_mul_inv] using hm
    _ ≤ (68096*K)*((5*K)^8*(scalarCells δ X).card) := by nlinarith
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarWeakRadiusProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar projection gain when the coefficient radius is allowed the same
small power loss as the ball and projection estimates. Normalization uses
an actual maximal coefficient and costs only a fixed polynomial. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_radius_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ W) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  classical
  obtain ⟨η,N0,hη,hN0,hprojection⟩ := scalar_bounded_projection hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη
    (by norm_num : (0:ℝ) < 68096*(5:ℝ)^8) zero_lt_one
  let ε := η/36
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,max N0 N1,hε,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXbound hsep hsize hd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let WF := Real.exp (η*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
  have hpower (n : ℕ) (hn : (n:ℝ) ≤ 36) : W^n ≤ WF := by
    rw [show W = Real.exp (ε*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp [ε]
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hη.le hlog)
    nlinarith
  have hWWF : W ≤ WF := by simpa only [pow_one] using hpower 1 (by norm_num)
  have hbudget : (68096*(5:ℝ)^8)*W^9 ≤ WF := by
    have he : W^9 = Real.exp ((η/4)*(N:ℝ)*Real.log 2) := by
      rw [show W = Real.exp (ε*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
      congr 1
      dsimp [ε]
      ring
    rw [he]
    exact (hloss N ((le_max_right _ _).trans hN)).1
  have hpointF : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ WF*r^κ*(X.card:ℝ) := by
    intro u r hr hr1
    have hh := mul_le_mul_of_nonneg_right hWWF
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) κ) (Nat.cast_nonneg X.card))
    exact (hpoint u r hr hr1).trans (by nlinarith)
  have hdF : ((scalarCells δ (X+X)).card:ℝ) ≤ WF*(X.card:ℝ) :=
    hd.trans (mul_le_mul_of_nonneg_right hWWF (Nat.cast_nonneg _))
  by_contra hn
  push Not at hn
  obtain ⟨b,hb,hmax⟩ := E.exists_max_image (fun a => |a|) hE
  by_cases hb1 : |b| ≤ 1
  · have heball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ WF*r^(2*κ)*(E.card:ℝ) := by
      intro u r hr hr1
      have hh := mul_le_mul_of_nonneg_right hWWF
        (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
      exact (hEball u r hr hr1).trans (by nlinarith)
    obtain ⟨a,ha,hgain⟩ := hprojection N ((le_max_left _ _).trans hN) X hX hXbound hsep hsize
      hdF hpointF E hE (fun a ha => (hmax a ha).trans hb1) heball
    have hh := (hn a ha).trans (mul_le_mul_of_nonneg_right hWWF (Nat.cast_nonneg _))
    exact (not_lt_of_ge hh) hgain
  · have hbpos : 0 < |b| := zero_lt_one.trans (lt_of_not_ge hb1)
    have hbne : b ≠ 0 := abs_pos.mp hbpos
    let F := E.image (fun a => -a/(-b))
    have hF : F.Nonempty := hE.image _
    have hFbound : ∀ a ∈ F, |a| ≤ 1 := by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      rw [neg_div_neg_eq,abs_div]
      exact (div_le_one hbpos).2 (hmax x hx)
    have hFball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass F u r ≤ WF*r^(2*κ)*(F.card:ℝ) := by
      intro u r hr _
      have hh := scalar_ratio_family_ball hδ (by positivity : 0 ≤ 2*κ) hW1 hW1
        (neg_ne_zero.mpr hbne) (by simpa only [abs_neg] using hEbound b hb)
        E E (Finset.Subset.refl _) (by simp : (E.card:ℝ) ≤ 1*(E.card:ℝ)) hEball u r hr
      have hp : W^(2*κ) ≤ W^2 := by
        have hh := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith : 2*κ ≤ 2)
        simpa only [Real.rpow_two] using hh
      have hc : 1*W*W^(2*κ) ≤ WF := by
        calc
          _ ≤ W*W^2 := by nlinarith
          _ = W^3 := by ring
          _ ≤ WF := hpower 3 (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg F.card))
      change scalarBallMass F u r ≤ (1*W*W^(2*κ))*r^(2*κ)*(F.card:ℝ) at hh
      exact hh.trans (by nlinarith)
    obtain ⟨a,ha,hgain⟩ := hprojection N ((le_max_left _ _).trans hN)
      X hX hXbound hsep hsize hdF hpointF F hF hFbound hFball
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    have hXc : (scalarCells δ X).card = X.card :=
      Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
    have hp (a : ℝ) (ha : a ∈ E) :
        ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤ W*(scalarCells δ X).card := by
      rw [hXc]
      exact hn a ha
    have hh := scalar_max_ratio_projection hδ hW1 X hX (hEbound x hx)
      (lt_of_not_ge hb1).le (by simpa only [hXc] using hd) (hp x hx) (hp b hb)
    have hupper := hh.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))
    rw [hXc] at hupper
    simp only [neg_div_neg_eq] at hgain
    exact (not_lt_of_ge hupper) hgain

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarWeakReference
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-set obstruction uniform in a weakly growing ratio radius. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_weak_reference_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ)^2 ≤ W →
      ∀ (X I J : Finset ℝ) (c A K : ℝ),
      X.Nonempty → J.Nonempty → J ⊆ I → c ≠ 0 → |c| ≤ M → |c⁻¹| ≤ M →
      1 ≤ K → (I.card:ℝ) ≤ A*(J.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ a ∈ I, |a| ≤ M) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^(2*κ)*(I.card:ℝ)) →
      A*K*(M:ℝ)^(2*κ) ≤ W →
      (∀ a ∈ J, ((scalarCells δ (X-X.image (fun x => (a/c)*x))).card:ℝ) ≤ W*(X.card:ℝ)) →
      False := by
  obtain ⟨ε,N0,hε,hN0,hprojection⟩ := Regularization.scalar_weak_radius_projection hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro M hM hMcost X I J c A K hX hJ hJI hc hcM hciM hK hIJ hXbound hsep hIbound hsize hd hball hIball hcost hproj
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let E := J.image (fun a => -a/c)
  have hδ : 0 < δ := by positivity
  have hE : E.Nonempty := hJ.image _
  have hEbound : ∀ a ∈ E, |a| ≤ W := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    rw [div_eq_mul_inv,abs_mul,abs_neg]
    have hh := mul_le_mul (hIbound b (hJI hb)) hciM (abs_nonneg _) (Nat.cast_nonneg M)
    exact hh.trans (by simpa only [pow_two] using hMcost)
  have hEball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr _
    have hh := scalar_ratio_family_ball hδ (by positivity : 0 ≤ 2*κ) hK
      (by exact_mod_cast hM : (1:ℝ) ≤ M) hc hcM I J hJI hIJ hIball u r hr
    have hm := mul_le_mul_of_nonneg_right hcost
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    change scalarBallMass E u r ≤ (A*K*(M:ℝ)^(2*κ))*r^(2*κ)*(E.card:ℝ) at hh
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection N hN X hX hXbound hsep hsize hd hball E hE hEbound hEball
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  have he : X+X.image (fun x => (-b/c)*x) = X-X.image (fun x => (b/c)*x) := by
    rw [neg_div]
    exact scalar_negative_sum X (b/c)
  rw [he] at hgain
  exact (not_lt_of_ge (hproj b hb)) hgain

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_CoordinateGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite planar set is exactly the edge set of its two coordinate
projections. This keeps original point counts in the dense graph reduction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_coordinates (x : Space 2) : rowPoint (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

 theorem coordinate_graph_count (X Y : Finset ℝ) (H : Finset (Space 2))
    (hcoord : ∀ p ∈ H, p 0 ∈ X ∧ p 1 ∈ Y) :
    (∑ x ∈ X, ((Y.filter fun y => rowPoint x y ∈ H).card:ℝ)) = (H.card:ℝ) := by
  classical
  let E := (X ×ˢ Y).filter fun p => rowPoint p.1 p.2 ∈ H
  have himage : E.image (fun p => rowPoint p.1 p.2) = H := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hxy).2
    · intro hp
      refine Finset.mem_image.mpr ⟨(p 0,p 1),?_,rowPoint_coordinates p⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr (hcoord p hp),by rwa [rowPoint_coordinates]⟩
  have hc : H.card = ∑ x ∈ X, (Y.filter fun y => rowPoint x y ∈ H).card := by
    calc
      H.card = (E.image (fun p => rowPoint p.1 p.2)).card := congrArg Finset.card himage.symm
      _ = E.card := Finset.card_image_of_injective _ rowPoint_pair_injective
      _ = _ := by simp only [E,Finset.card_filter,Finset.sum_product]
  rw [hc,Nat.cast_sum]

 theorem coordinate_graph_card_le (X Y : Finset ℝ) (H : Finset (Space 2))
    (hcoord : ∀ p ∈ H, p 0 ∈ X ∧ p 1 ∈ Y) : H.card ≤ X.card*Y.card := by
  have hsub : H ⊆ scalarProductPoints X Y := by
    intro p hp
    exact Finset.mem_image.mpr ⟨(p 0,p 1),Finset.mem_product.mpr (hcoord p hp),rowPoint_coordinates p⟩
  exact (Finset.card_le_card hsub).trans_eq (scalarProductPoints_card X Y)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RegularGraphCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial losses in the refined graph obstruction, specialized to a
single weak scale parameter. -/
namespace Falconer

 theorem regularGraphCost_one_le (M : ℕ) : 1 ≤ regularGraphCost M := by
  have hh : 0 ≤ 1024*(2*(M:ℝ)+3)^2+4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+
      2*(1+4*(M:ℝ))^2+2*(M:ℝ)^2 := by positivity
  unfold regularGraphCost
  linarith

 theorem regular_graph_weak_costs {κ t R : ℝ} (hκ : κ ≤ 1) (ht : t ≤ 2)
    (M : ℕ) (hM : 1 ≤ M) (hR : 1 ≤ R) :
    1024*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^6 ≤ regularGraphCost M*R^20 ∧
    4096*(2*((M*M:ℕ):ℝ)+3)*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^13 ≤ regularGraphCost M*R^20 ∧
    Real.sqrt ((2*(R/R⁻¹)*R*(R/(R⁻¹)^2)/R⁻¹)*(1+4*(M:ℝ))^t) ≤ regularGraphCost M*R^20 ∧
    (2/(R⁻¹)^4)*R*(M:ℝ)^(2*κ) ≤ regularGraphCost M*R^20 := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  have hC := regularGraphCost_one_le M
  have hD : 1024*(2*(M:ℝ)+3)^2 ≤ regularGraphCost M := by
    unfold regularGraphCost
    nlinarith [sq_nonneg (M:ℝ),sq_nonneg (1+4*(M:ℝ))]
  have hQ : 4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2 ≤ regularGraphCost M := by
    unfold regularGraphCost
    nlinarith [sq_nonneg (M:ℝ),sq_nonneg (1+4*(M:ℝ)),sq_nonneg (2*(M:ℝ)+3)]
  have hP : 2*(1+4*(M:ℝ))^2 ≤ regularGraphCost M := by
    have hh : 0 ≤ 1+1024*(2*(M:ℝ)+3)^2+
        4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+2*(M:ℝ)^2 := by positivity
    unfold regularGraphCost
    linarith
  have hI : 2*(M:ℝ)^2 ≤ regularGraphCost M := by
    have hh : 0 ≤ 1+1024*(2*(M:ℝ)+3)^2+
        4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+2*(1+4*(M:ℝ))^2 := by positivity
    unfold regularGraphCost
    linarith
  have hpow (n : ℕ) (hn : n ≤ 20) : R^n ≤ R^20 := pow_le_pow_right₀ hR hn
  have hCR : 1 ≤ regularGraphCost M*R^20 := by
    have hh := one_le_pow₀ hR (n := 20)
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _ = (1024*(2*(M:ℝ)+3)^2)*R^10 := by rw [inv_pow,div_inv_eq_mul]; ring
      _ ≤ regularGraphCost M*R^20 := mul_le_mul hD (hpow 10 (by omega)) (by positivity) (by linarith)
  · calc
      _ = (4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2)*R^17 := by
        rw [inv_pow,div_inv_eq_mul,Nat.cast_mul]; ring
      _ ≤ regularGraphCost M*R^20 := mul_le_mul hQ (hpow 17 (by omega)) (by positivity) (by linarith)
  · have he : 2*(R/R⁻¹)*R*(R/(R⁻¹)^2)/R⁻¹ = 2*R^7 := by
      field_simp
    have hp : (1+4*(M:ℝ))^t ≤ (1+4*(M:ℝ))^2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1+4*(M:ℝ)) ht
      simpa only [Real.rpow_two] using hh
    have hb : (2*R^7)*(1+4*(M:ℝ))^t ≤ regularGraphCost M*R^20 := by
      calc
        _ ≤ (2*R^7)*(1+4*(M:ℝ))^2 := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (2*(1+4*(M:ℝ))^2)*R^7 := by ring
        _ ≤ _ := mul_le_mul hP (hpow 7 (by omega)) (by positivity) (by linarith)
    rw [he]
    exact (Real.sqrt_le_sqrt hb).trans (Real.sqrt_le_self_iff.mpr (Or.inr hCR))
  · have hp : (M:ℝ)^(2*κ) ≤ (M:ℝ)^2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 2*κ ≤ 2)
      simpa only [Real.rpow_two] using hh
    calc
      _ = (2*R^5)*(M:ℝ)^(2*κ) := by rw [inv_pow,div_inv_eq_mul]; ring
      _ ≤ (2*R^5)*(M:ℝ)^2 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (2*(M:ℝ)^2)*R^5 := by ring
      _ ≤ _ := mul_le_mul hI (hpow 5 (by omega)) (by positivity) (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DenseGraphComparableParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additional polynomial room for comparable coordinate counts. -/
namespace Falconer

 theorem dense_graph_comparable_parameters {θ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      let R := Real.exp (θ*(N:ℝ)*Real.log 2)
      1 ≤ S ∧ S ≤ R ∧ 67108864*S^15 ≤ R ∧ R⁻¹ ≤ (S⁻¹)^2/64 := by
  obtain ⟨N0,hN0,hbounds⟩ := scalar_fixed_losses hθ
    (by norm_num : (0:ℝ) < 67108864) (by norm_num : (0:ℝ) < 64)
  let γ := θ/100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let R := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hSpos : 0 < S := Real.exp_pos _
  have hRpos : 0 < R := Real.exp_pos _
  have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
  have hS : 1 ≤ S := Real.one_le_exp_iff.mpr (by positivity)
  have hSR : S ≤ R := by
    apply Real.exp_le_exp.mpr
    dsimp [γ]
    nlinarith
  have hp (n : ℕ) (hn : (n:ℝ) ≤ 25) : S^n ≤ Real.exp ((θ/4)*(N:ℝ)*Real.log 2) := by
    rw [show S = Real.exp (γ*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp [γ]
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hθ.le hlog)
    nlinarith
  have h15 : 67108864*S^15 ≤ R :=
    (mul_le_mul_of_nonneg_left (hp 15 (by norm_num)) (by norm_num)).trans (hbounds N hN).1
  have h2 : 64*S^2 ≤ R :=
    (mul_le_mul_of_nonneg_left (hp 2 (by norm_num)) (by norm_num)).trans (hbounds N hN).2
  refine ⟨hS,hSR,h15,?_⟩
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 64*S^2) h2
  have he : (S⁻¹)^2/64 = 1/(64*S^2) := by field_simp
  change R⁻¹ ≤ (S⁻¹)^2/64
  rw [he]
  simpa only [one_div] using hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RegularGraphRadiusCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed graph loss is polynomial in the coordinate ratio radius. -/
namespace Falconer

 theorem regular_graph_radius_cost {R : ℝ} (hR : 1 ≤ R) (M : ℕ) (hM : (M:ℝ) ≤ R) :
    regularGraphCost M ≤ 1048576*R^4 := by
  have hM0 : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hm2 : (M:ℝ)^2 ≤ R^2 := pow_le_pow_left₀ hM0 hM 2
  have hr2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hr4 : 1 ≤ R^4 := one_le_pow₀ hR
  have hr24 : R^2 ≤ R^4 := pow_le_pow_right₀ hR (by omega)
  have hl : 2*(M:ℝ)+3 ≤ 5*R := by linarith
  have hlsq : (2*(M:ℝ)+3)^2 ≤ 25*R^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(M:ℝ)+3) hl 2
    nlinarith
  have hb : (1+4*(M:ℝ))^2 ≤ 25*R^2 := by
    have hl' : 1+4*(M:ℝ) ≤ 5*R := by linarith
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1+4*(M:ℝ)) hl' 2
    nlinarith
  have ht : 2*(M:ℝ)^2+3 ≤ 5*R^2 := by nlinarith
  have hp : (2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2 ≤ 125*R^4 := by
    have hh := mul_le_mul ht hlsq (sq_nonneg _) (by positivity : 0 ≤ 5*R^2)
    nlinarith
  unfold regularGraphCost
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RegularUnbalancedGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined-graph obstruction with comparable coordinate cardinalities. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem regular_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ)^2 ≤ W →
      ∀ (Q ρ K η t Kreg L KI : ℝ) (I X Y : Finset ℝ) (A B : ℝ → Finset ℝ),
      1 ≤ Q → 0 < ρ → 0 ≤ K → 0 < η → 2*κ ≤ t → 1 ≤ Kreg → 0 ≤ L → 1 ≤ KI →
      I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, A i ⊆ X) → (∀ i ∈ I, B i ⊆ Y) →
      (∀ i ∈ I, ρ*(X.card:ℝ) ≤ ((A i).card:ℝ)) →
      (∀ i ∈ I, ρ*(Y.card:ℝ) ≤ ((B i).card:ℝ)) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => i*y))).card:ℝ) ≤ K*(X.card:ℝ)) →
      ∀ (e : ℝ → ℝ → ℝ → Prop) (G : Finset (Space 2)),
      NormalizedFiniteBallBound δ t Kreg G →
      (∀ i ∈ I, ∀ x ∈ A i, η*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ KI*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      1024*(2*M+3)^2*K^4*Q^2/ρ^6 ≤ W →
      4096*(2*(M*M)+3)*(2*M+3)^2*K^4*Q^2/ρ^13 ≤ W →
      Real.sqrt ((2*(K/ρ)*Kreg*(L/ρ^2)/η)*(1+4*(M:ℝ))^t) ≤ W →
      (2/ρ^4)*KI*(M:ℝ)^(2*κ) ≤ W → False := by
  obtain ⟨ε,N0,hε,hN0,hobstruction⟩ := scalar_weak_reference_obstruction hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro M hM hMcost Q ρ K η t Kreg L KI I X Y A B hQ hρ hK hη ht hKreg hL hKI hI hX hY hXY
    hXbound hXsep hYsep hA hB hsizeA hsizeB hc hproj e G hreg hdegree hgraph hGsize
    hIball hXsize hDcost hQcost hPcost hIcost
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  obtain ⟨i₀,hi₀,J,hJI,hJ,hAi,hd,hq,hpoint⟩ := common_unbalanced_regular_reference hδ hρ hK hQ hη
    (by linarith : 0 ≤ t) hKreg hL I X Y A B id hI hX hY hXY hXsep hYsep
    hA hB hsizeA hsizeB M hc hproj e G hreg hdegree hgraph hGsize
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : 0 < ρ^4*(I.card:ℝ) := mul_pos (pow_pos hρ _)
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hI))
    have : 0 < (J.card:ℝ) := by linarith
    exact_mod_cast this
  have hIJ : (I.card:ℝ) ≤ (2/ρ^4)*(J.card:ℝ) := by
    have hh : (I.card:ℝ) ≤ (2*(J.card:ℝ))/ρ^4 :=
      (le_div_iff₀ (pow_pos hρ 4)).2 (by simpa only [mul_comm] using hJ)
    convert hh using 1 <;> first | rfl | ring
  have hAc : (scalarCells δ (A i₀)).card = (A i₀).card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ
      (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne))
  rw [hAc] at hd hq
  have hd' : ((scalarCells δ (A i₀+A i₀)).card:ℝ) ≤ W*((A i₀).card:ℝ) :=
    hd.trans (mul_le_mul_of_nonneg_right hDcost (Nat.cast_nonneg _))
  have hq' : ∀ a ∈ J, ((scalarCells δ (A i₀-(A i₀).image (fun x => (a/i₀)*x))).card:ℝ) ≤
      W*((A i₀).card:ℝ) := fun a ha =>
    (hq a ha).trans (mul_le_mul_of_nonneg_right hQcost (Nat.cast_nonneg _))
  have hAiSize : Real.log ((A i₀).card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 :=
    (Real.log_le_log (Nat.cast_pos.mpr (Finset.card_pos.mpr hAi))
      (Nat.cast_le.mpr (Finset.card_le_card (hA i₀ hi₀)))).trans hXsize
  have hpoint' : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (A i₀) u r ≤ W*r^κ*((A i₀).card:ℝ) := by
    intro u r hr hr1
    have hp : r^(t/2) ≤ r^κ := Real.rpow_le_rpow_of_exponent_ge
      (hδ.trans_le hr) hr1 (by linarith)
    have hh := mul_le_mul hPcost hp (Real.rpow_nonneg (hδ.le.trans hr) _) (Real.exp_pos _).le
    exact (hpoint u r hr).trans (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _))
  exact hobstruction N hN M hM hMcost (A i₀) I J i₀ (2/ρ^4) KI hAi hJne hJI
    (hc i₀ hi₀).1 (hc i₀ hi₀).2.1 (hc i₀ hi₀).2.2 hKI hIJ
    (fun x hx => hXbound x (hA i₀ hi₀ hx))
    (fun x hx y hy hne => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hne)
    (fun i hi => (hc i hi).2.1) hAiSize hd' hpoint' hIball hIcost hq'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_WeakUnbalancedGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale-absorbed graph obstruction for comparable coordinate sets and
weakly growing coefficient radius. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem weak_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let R := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ R →
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ R →
      ∀ (t : ℝ) (I X Y : Finset ℝ) (A B : ℝ → Finset ℝ),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, A i ⊆ X) → (∀ i ∈ I, B i ⊆ Y) →
      (∀ i ∈ I, R⁻¹*(X.card:ℝ) ≤ ((A i).card:ℝ)) →
      (∀ i ∈ I, R⁻¹*(Y.card:ℝ) ≤ ((B i).card:ℝ)) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => i*y))).card:ℝ) ≤ R*(X.card:ℝ)) →
      ∀ (e : ℝ → ℝ → ℝ → Prop) (G : Finset (Space 2)),
      NormalizedFiniteBallBound δ t R G →
      (∀ i ∈ I, ∀ x ∈ A i, R⁻¹*((B i).card:ℝ) ≤ (((B i).filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ B i, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ R*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ R*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  obtain ⟨ε,N0,hε,hN0,hobs⟩ := regular_unbalanced_graph_obstruction hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hε
    (by norm_num : (0:ℝ) < 1048576) zero_lt_one
  let γ := ε/104
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨γ,max N0 N1,hγ,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro M hM hMR Q hQ1 hQR t I X Y A B ht ht2 hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB
    hc hproj e G hreg hdegree hgraph hGsize hIball hXsize
  let R := Real.exp (γ*(N:ℝ)*Real.log 2)
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hR : 1 ≤ R := Real.one_le_exp_iff.mpr (by positivity)
  have hRpos : 0 < R := Real.exp_pos _
  have hcost : regularGraphCost M*R^22 ≤ W := by
    have hb := mul_le_mul_of_nonneg_right (regular_graph_radius_cost hR M hMR)
      (show 0 ≤ R^22 by positivity)
    have he : R^26 = Real.exp ((ε/4)*(N:ℝ)*Real.log 2) := by
      rw [show R = Real.exp (γ*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
      congr 1
      dsimp [γ]
      ring
    calc
      _ ≤ 1048576*R^4*R^22 := hb
      _ = 1048576*R^26 := by ring
      _ ≤ W := by rw [he]; exact (hloss N ((le_max_right _ _).trans hN)).1
  have hMcost : (M:ℝ)^2 ≤ W := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg M) hMR 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
    dsimp [γ]
    nlinarith
  obtain ⟨hD,hRatio,hP,hC⟩ := regular_graph_weak_costs hκ1 ht2 M hM hR
  have hbase : regularGraphCost M*R^20 ≤ W :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (show 20 ≤ (22:ℕ) by omega))
      (zero_le_one.trans (regularGraphCost_one_le M))).trans hcost
  have hQ2 : Q^2 ≤ R^2 := pow_le_pow_left₀ (zero_le_one.trans hQ1) hQR 2
  have hD' : (1024*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^6)*Q^2 ≤ W := by
    have hh := mul_le_mul hD hQ2 (sq_nonneg Q) (mul_nonneg (zero_le_one.trans (regularGraphCost_one_le M)) (by positivity))
    apply le_trans _ hcost
    convert hh using 1 <;> first | rfl | ring
  have hRatio' : (4096*(2*((M*M:ℕ):ℝ)+3)*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^13)*Q^2 ≤ W := by
    have hh := mul_le_mul hRatio hQ2 (sq_nonneg Q) (mul_nonneg (zero_le_one.trans (regularGraphCost_one_le M)) (by positivity))
    apply le_trans _ hcost
    convert hh using 1 <;> first | rfl | ring
  exact hobs N ((le_max_left _ _).trans hN) M hM hMcost Q R⁻¹ R R⁻¹ t R R R I X Y A B
    hQ1 (inv_pos.mpr hRpos) hRpos.le (inv_pos.mpr hRpos) ht hR hRpos.le hR
    hI hX hY hXY hXbound hXsep hYsep hA hB hsizeA hsizeB hc hproj e G hreg
    hdegree hgraph hGsize hIball hXsize
    (by convert hD' using 1; ring)
    (by
      have hh := hRatio'
      push_cast at hh
      convert hh using 1; ring)
    (hP.trans hbase) (hC.trans hbase)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DenseUnbalancedGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense original graph obstruction for actual, comparable coordinate
sets and a weakly growing coordinate ratio bound. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem dense_unbalanced_graph_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ S →
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ S →
      ∀ (t : ℝ) (I X Y : Finset ℝ) (e : ℝ → ℝ → ℝ → Prop) (D : ℝ → Finset ℤ)
        (G : Finset (Space 2)),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → X.Nonempty → Y.Nonempty → (X.card:ℝ) ≤ Q*(Y.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, ∀ x ∈ Y.image (fun y => i*y), ∀ y ∈ Y.image (fun y => i*y), x ≠ y → δ ≤ |x-y|) →
      (∀ i ∈ I, i ≠ 0 ∧ |i| ≤ M ∧ |i⁻¹| ≤ M) →
      (∀ i ∈ I, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ∑ x ∈ X, ((Y.filter fun y => e i x y).card:ℝ)) →
      (∀ i ∈ I, ∀ x ∈ X, ∀ y ∈ Y, e i x y → ⌊(x+i*y)/δ⌋ ∈ D i) →
      (∀ i ∈ I, ((D i).card:ℝ) ≤ S*(X.card:ℝ)) →
      NormalizedFiniteBallBound δ t S G →
      (∀ i ∈ I, ∀ x ∈ X, ∀ y ∈ Y, e i x y → rowPoint x y ∈ G) →
      (G.card:ℝ) ≤ S*(X.card:ℝ)*(Y.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ S*r^(2*κ)*(I.card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨θ,N0,hθ,hN0,hweak⟩ := weak_unbalanced_graph_obstruction hκ hκ1
  obtain ⟨γ,N1,hγ,hN1,hparameters⟩ := dense_graph_comparable_parameters hθ
  refine ⟨γ,max N0 N1,hγ,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro M hM hMS Q hQ1 hQS t I X Y e D G ht ht2 hI hX hY hXY hXbound hXsep hYsep hcYsep hc hdense hlabels
    hDcard hreg hgraph hGsize hIball hXsize
  let δ := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let R := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  obtain ⟨hS,hSR,hprojcost,hdegreecost⟩ := hparameters N ((le_max_right _ _).trans hN)
  have hprojcost' : 67108864*S^13*Q^2 ≤ R := by
    have hQ2 : Q^2 ≤ S^2 := pow_le_pow_left₀ (zero_le_one.trans hQ1) hQS 2
    calc
      _ ≤ 67108864*S^13*S^2 := mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = 67108864*S^15 := by ring
      _ ≤ R := hprojcost
  have hex : ∀ i : ℝ, ∃ A B : Finset ℝ, i ∈ I →
      A ⊆ X ∧ B ⊆ Y ∧ R⁻¹*(X.card:ℝ) ≤ (A.card:ℝ) ∧
      R⁻¹*(Y.card:ℝ) ≤ (B.card:ℝ) ∧
      ((scalarCells δ (A+B.image (fun y => i*y))).card:ℝ) ≤ R*(X.card:ℝ) ∧
      ∀ x ∈ A, R⁻¹*(B.card:ℝ) ≤ ((B.filter fun y => e i x y).card:ℝ) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨A,hAX,B,hBY,hA,hB,hproj,hdegree⟩ := scalar_dilated_unbalanced_refinement
        hδ hS (hc i hi).1 X Y hX hY hXY hXsep (hcYsep i hi) (e i) (D i)
        (hdense i hi) (hlabels i hi) (hDcard i hi)
      refine ⟨A,B,fun _ => ⟨hAX,hBY,?_,?_,?_,?_⟩⟩
      · exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans hA
      · exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans hB
      · exact hproj.trans (mul_le_mul_of_nonneg_right hprojcost' (Nat.cast_nonneg _))
      · intro x hx
        exact (mul_le_mul_of_nonneg_right hdegreecost (Nat.cast_nonneg _)).trans (hdegree x hx)
    · exact ⟨∅,∅,fun h => (hi h).elim⟩
  choose A B hAB using hex
  have hRreg : NormalizedFiniteBallBound δ t R G := by
    intro z r hr hr1
    have hh := mul_le_mul_of_nonneg_right hSR
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) t) (Nat.cast_nonneg G.card))
    exact (hreg z r hr hr1).trans (by nlinarith)
  have hRball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ R*r^(2*κ)*(I.card:ℝ) := by
    intro u r hr hr1
    have hh := mul_le_mul_of_nonneg_right hSR
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg I.card))
    exact (hIball u r hr hr1).trans (by nlinarith)
  apply hweak N ((le_max_left _ _).trans hN) M hM (hMS.trans hSR) Q hQ1 (hQS.trans hSR) t I X Y A B ht ht2 hI hX hY hXY
    hXbound hXsep hYsep
    (fun i hi => (hAB i hi).1) (fun i hi => (hAB i hi).2.1)
    (fun i hi => (hAB i hi).2.2.1) (fun i hi => (hAB i hi).2.2.2.1) hc
    (fun i hi => (hAB i hi).2.2.2.2.1) e G hRreg
    (fun i hi => (hAB i hi).2.2.2.2.2)
    (fun i hi x hx y hy he => hgraph i hi x ((hAB i hi).1 hx) y ((hAB i hi).2.1 hy) he)
    (hGsize.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSR
      (Nat.cast_nonneg X.card)) (Nat.cast_nonneg Y.card))) hRball hXsize

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_CoordinateGraphObstruction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar obstruction applied to the actual coordinate graph of a
finite planar set. Edge density is exactly retained planar cardinality. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem coordinate_graph_obstruction_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (M : ℕ), 1 ≤ M → (M:ℝ) ≤ S → ∀ Q : ℝ, 1 ≤ Q → Q ≤ S →
      ∀ (t : ℝ) (J : Finset ℝ) (c : ℝ → ℝ) (G : Finset (Space 2))
        (H : ℝ → Finset (Space 2)),
      let X := G.image (fun p => p 0)
      let Y := G.image (fun p => p 1)
      2*κ ≤ t → t ≤ 2 → J.Nonempty → G.Nonempty →
      (X.card:ℝ) ≤ Q*(Y.card:ℝ) → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) →
      (∀ j ∈ J, ∀ x ∈ Y.image (fun y => c j*y),
        ∀ y ∈ Y.image (fun y => c j*y), x ≠ y → δ ≤ |x-y|) →
      (∀ j ∈ J, c j ≠ 0 ∧ |c j| ≤ M ∧ |(c j)⁻¹| ≤ M) →
      (∀ j ∈ J, H j ⊆ G) →
      (∀ j ∈ J, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, ((scalarCells δ ((H j).image (cartesianProjection (c j)))).card:ℝ) ≤ S*(X.card:ℝ)) →
      NormalizedFiniteBallBound δ t S G →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass (J.image c) u r ≤ S*r^(2*κ)*((J.image c).card:ℝ)) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := dense_unbalanced_graph_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro M hM hMS Q hQ hQS t J c G H ht ht2 hJ hG hXY hXbound hXsep hYsep hcYsep
    hc hHG hdense hD hreg hball hlog
  let δ := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let g := Function.invFunOn c (J:Set ℝ)
  have hg : ∀ i ∈ J.image c, g i ∈ J ∧ c (g i) = i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact Function.invFunOn_pos (f := c) (s := (J:Set ℝ)) ⟨j,hj,rfl⟩
  let e := fun i x y => rowPoint x y ∈ H (g i)
  let D := fun i => scalarCells δ ((H (g i)).image (cartesianProjection i))
  have hS : 1 ≤ S := Real.one_le_exp_iff.mpr (by positivity)
  have hcount : ∀ j ∈ J,
      (∑ x ∈ X, ((Y.filter fun y => rowPoint x y ∈ H j).card:ℝ)) = ((H j).card:ℝ) := by
    intro j hj
    apply coordinate_graph_count
    intro p hp
    have hpG := hHG j hj hp
    exact ⟨Finset.mem_image_of_mem _ hpG,Finset.mem_image_of_mem _ hpG⟩
  apply hmain N hN M hM hMS Q hQ hQS t (J.image c) X Y e D G ht ht2
    (hJ.image c) (hG.image _) (hG.image _) hXY hXbound hXsep hYsep
  · intro i hi
    have he := (hg i hi).2
    rw [← he]
    exact hcYsep _ (hg i hi).1
  · intro i hi
    have he := (hg i hi).2
    rw [← he]
    exact hc _ (hg i hi).1
  · intro i hi
    have hh := (hdense _ (hg i hi).1).trans_eq (hcount _ (hg i hi).1).symm
    simpa only [e] using hh
  · intro i hi x hx y hy he
    change ⌊(x+i*y)/δ⌋ ∈ scalarCells δ ((H (g i)).image (cartesianProjection i))
    apply Finset.mem_image.mpr
    refine ⟨x+i*y,?_,rfl⟩
    exact Finset.mem_image.mpr ⟨rowPoint x y,he,by
      simp only [cartesianProjection,rowPoint_zero,rowPoint_one]⟩
  · intro i hi
    simpa only [D,(hg i hi).2] using hD _ (hg i hi).1
  · exact hreg
  · intro i hi x hx y hy he
    exact hHG _ (hg i hi).1 he
  · have hcountG : (G.card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by
      exact_mod_cast coordinate_graph_card_le X Y G (fun p hp =>
        ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩)
    have hm := mul_le_mul_of_nonneg_right hS (mul_nonneg
      (Nat.cast_nonneg X.card) (Nat.cast_nonneg Y.card))
    nlinarith
  · exact hball
  · exact hlog

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.coordinate_graph_obstruction_oai := @OAI.Falconer.coordinate_graph_obstruction_oai
