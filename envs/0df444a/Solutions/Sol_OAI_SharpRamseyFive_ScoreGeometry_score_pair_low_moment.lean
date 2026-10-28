-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:25:25.682366+00:00
-- url     : https://prove2.me/submissions/a03dd118-82b0-4922-9c60-e2ae4b7cc131

import Mathlib
import Definitions.Def_OAIQ060R003

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace RadialLine

lemma finrank_sup [FiniteDimensional K V] {x : ℙ K V}
    {l m : RadialLine x} (hlm : l ≠ m) :
    finrank K (l.val ⊔ m.val : Submodule K V) = 3 := by
  have hn : ¬l.val ≤ m.val := by
    intro h
    apply hlm
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq h
      (l.property.1.trans m.property.1.symm))
  have hi : l.val ⊓ m.val < l.val := lt_of_le_of_ne inf_le_left (by
    intro h
    apply hn
    rw [← h]
    exact inf_le_right)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  have hge := Submodule.finrank_mono (le_inf l.property.2 m.property.2)
  have he := Submodule.finrank_sup_add_finrank_inf_eq l.val m.val
  rw [x.finrank_submodule] at hge
  rw [l.property.1] at hlt
  rw [l.property.1, m.property.1] at he
  omega

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

lemma through_le_iff {x y : ℙ K V} (hxy : x ≠ y) (W : Submodule K V) :
    (through x y hxy).val ≤ W ↔ x.submodule ≤ W ∧ y.submodule ≤ W :=
  sup_le_iff

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma trainingOnLine_eq_fiber (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) :
    trainingOnLine X l = X.filter (fun y => through x y.val y.property = l) := by
  classical
  ext y
  simp only [trainingOnLine, Finset.mem_filter, through_eq_iff]

lemma sum_trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, (trainingOnLine X l).card =
      (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp_rw [trainingOnLine_eq_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter X (inFlat W)
    (fun y => through x y.val y.property)]
  congr 1
  ext y
  simp [inFlat, through_le_iff, hx]

omit [FiniteDimensional K V] in
lemma inFlat_inf (W U : Submodule K V) :
    (inFlat (x := x) W) ∩ inFlat U = inFlat (W ⊓ U) := by
  classical
  ext l
  simp [inFlat]

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_OffFiberPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

section Finite
variable {I D : Type*} [DecidableEq I] [DecidableEq D]

omit [DecidableEq I] in
lemma card_offFiberPairs (f : I → D) (X : Finset I) :
    (offFiberPairs f X).card = ∑ y ∈ X, (X.filter fun z => f y ≠ f z).card := by
  simp only [offFiberPairs,Finset.card_filter,Finset.sum_product]

omit [DecidableEq I] in
lemma offFiberPairs_many (f : I → D) (X : Finset I)
    (h : ∀ y ∈ X, 2*(X.filter fun z => f y = f z).card ≤ X.card) :
    X.card^2 ≤ 2*(offFiberPairs f X).card := by
  have hrow (y : I) (hy : y ∈ X) : X.card ≤ 2*(X.filter fun z => f y ≠ f z).card := by
    have hp := Finset.card_filter_add_card_filter_not (s := X) (fun z => f y = f z)
    change (X.filter fun z => f y = f z).card + (X.filter fun z => f y ≠ f z).card = X.card at hp
    have hh := h y hy
    omega
  have hs := Finset.sum_le_sum hrow
  simpa only [Finset.sum_const_nat,← Finset.mul_sum,← card_offFiberPairs,pow_two] using hs
end Finite

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V)

lemma planePairs_disjoint (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B) (hne : A ≠ B) :
    Disjoint (planePairs x X A) (planePairs x X B) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨y,z⟩ hpa hpb
  obtain ⟨hya,hza⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpa).1
  obtain ⟨hyb,hzb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpb).1
  have hrad := (Finset.mem_filter.mp hpa).2
  let l := RadialLine.through x y.val y.property
  let m := RadialLine.through x z.val z.property
  have hr : finrank K (l.val ⊔ m.val : Submodule K V) = 3 := RadialLine.finrank_sup hrad
  have hlA : l.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hya).2⟩
  have hmA : m.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hza).2⟩
  have hlB : l.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hyb).2⟩
  have hmB : m.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hzb).2⟩
  have hEA := Submodule.eq_of_le_of_finrank_eq (sup_le hlA hmA) (hr.trans hA.symm)
  have hEB := Submodule.eq_of_le_of_finrank_eq (sup_le hlB hmB) (hr.trans hB.symm)
  exact hne (hEA.symm.trans hEB)

theorem rich_nondominant_plane_count (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (onPlane x X A).card)
    (hnd : ∀ A ∈ F, ∀ l : RadialLine x,
      2*((onPlane x X A).filter fun y => y.val.submodule ≤ l.val).card ≤ (onPlane x X A).card) :
    F.card*M^2 ≤ 2*X.card^2 := by
  have hm (A : Submodule K V) (hA : A ∈ F) : M^2 ≤ 2*(planePairs x X A).card := by
    have hh := offFiberPairs_many (fun y : {y : ℙ K V // x ≠ y} => RadialLine.through x y.val y.property)
      (onPlane x X A) (by
        intro y _
        have hr := hnd A hA (RadialLine.through x y.val y.property)
        have he : ((onPlane x X A).filter fun z =>
            RadialLine.through x y.val y.property = RadialLine.through x z.val z.property) =
            ((onPlane x X A).filter fun z => z.val.submodule ≤ (RadialLine.through x y.val y.property).val) := by
          ext z
          simp only [Finset.mem_filter,eq_comm (a := RadialLine.through x y.val y.property),RadialLine.through_eq_iff]
        rwa [he])
    exact (Nat.pow_le_pow_left (hM A hA) 2).trans hh
  have hdisj : (F : Set (Submodule K V)).PairwiseDisjoint (planePairs x X) := by
    intro A hA B hB hne
    exact planePairs_disjoint x X A B (hF A hA) (hF B hB) (hxF A hA) (hxF B hB) hne
  have hsub : F.biUnion (planePairs x X) ⊆ X ×ˢ X := by
    intro p hp
    obtain ⟨A,_,hpA⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hy,hz⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpA).1
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hz).1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj,Finset.card_product] at hc
  have hs := Finset.sum_le_sum hm
  simp only [Finset.sum_const_nat,← Finset.mul_sum] at hs
  exact hs.trans (by nlinarith)

end SharpRamseyFive.NondominantOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardFilterContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

end SharpRamseyFive.RichPlaneGeometry

namespace SharpRamseyFive.HyperplaneOverlap
open Module ProjectiveIncidence RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma hyperplane_intersection_rank {d : ℕ} (hdim : finrank K V = d+1)
    (A B : Submodule K V) (hA : finrank K A = d) (hB : finrank K B = d) (hne : A ≠ B) :
    finrank K (A ⊓ B : Submodule K V) = d-1 := by
  have hn : ¬A ≤ B := fun h => hne (Submodule.eq_of_le_of_finrank_eq h (hA.trans hB.symm))
  have hlt := finrank_inf_lt_of_not_le A B hn
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_le (A ⊔ B : Submodule K V)
  rw [hA] at hlt
  rw [hA,hB] at hs
  rw [hdim] at hle
  omega

lemma card_hyperplanes_containing [Finite K] {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) (W : Submodule K V) :
    (F.filter fun A => W ≤ A).card ≤
      ∑ i ∈ Finset.range (d+1-finrank K W), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let G := F.filter fun A => W ≤ A
  let f (A : G) : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} :=
    ⟨dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1), by
      rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
      intro w hw
      have hk := (Finset.mem_filter.mp A.property).2 hw
      rw [← ker_dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1)] at hk
      exact hk⟩
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hv := congrArg (fun b : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} =>
      LinearMap.ker b.val.rep) he
    simpa only [f,ker_dualOfHyperplane] using hv
  have hc := Fintype.card_le_of_injective f hf
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hr : finrank K W.dualAnnihilator = d+1-finrank K W := by omega
  rw [Fintype.card_coe,← Nat.card_eq_fintype_card,card_subspacePoints,hr] at hc
  exact hc

lemma pair_count_by_intersection {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V × Submodule K V))
    (hE : E ⊆ F ×ˢ F) (hEL : ∀ p ∈ E, p.1 ⊓ p.2 ∈ L) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
  let C (W : Submodule K V) := F.filter fun H => W ≤ H
  have hsub : E ⊆ L.biUnion (fun W => C W ×ˢ C W) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
    exact Finset.mem_biUnion.mpr ⟨p.1 ⊓ p.2,hEL p hp,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,inf_le_left⟩,Finset.mem_filter.mpr ⟨hb,inf_le_right⟩⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (C W ×ˢ C W).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
    have hc := card_hyperplanes_containing hdim F hF W
    rw [hL W hW] at hc
    simpa only [Finset.card_product,pow_two] using Nat.pow_le_pow_left hc 2
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma pair_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V × Submodule K V))
    (hE : E ⊆ F ×ˢ F) (hEL : ∀ p ∈ E, ∃ W ∈ L, W ≤ p.1 ⊓ p.2) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
  let C (W : Submodule K V) := F.filter fun H => W ≤ H
  have hsub : E ⊆ L.biUnion (fun W => C W ×ˢ C W) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
    obtain ⟨W,hW,hWp⟩ := hEL p hp
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,hWp.trans inf_le_left⟩,
       Finset.mem_filter.mpr ⟨hb,hWp.trans inf_le_right⟩⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (C W ×ˢ C W).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
    have hc := card_hyperplanes_containing hdim F hF W
    rw [hL W hW] at hc
    simpa only [Finset.card_product,pow_two] using Nat.pow_le_pow_left hc 2
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

end SharpRamseyFive.HyperplaneOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PairPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ActualOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

theorem nondominant_pair_count (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F)
    (hne : ∀ p ∈ E, p.1 ≠ p.2) (M : ℕ)
    (hM : ∀ p ∈ E, M ≤ (pairPoints x X p.1 p.2).card)
    (hnd : ∀ p ∈ E, ∀ l : RadialLine x,
      2*((pairPoints x X p.1 p.2).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X p.1 p.2).card) :
    E.card*M^2 ≤ 2*X.card^2*(Nat.card K+1)^2 := by
  let L := E.image fun p => p.1 ⊓ p.2
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 3 := by
    obtain ⟨⟨A,B⟩,hAB,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp (hE hAB)
    exact hyperplane_intersection_rank (d := 4) hdim A B (hF A hA) (hF B hB) (hne _ hAB)
  have hxL (W : Submodule K V) (hW : W ∈ L) : x.submodule ≤ W := by
    obtain ⟨⟨A,B⟩,hAB,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp (hE hAB)
    exact le_inf (hxF A hA) (hxF B hB)
  have hplanes := rich_nondominant_plane_count x X L hL hxL M (by
    intro W hW
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hW
    exact hM p hp) (by
    intro W hW l
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hW
    exact hnd p hp l)
  have hpairs := pair_count_by_intersection (d := 4) hdim F hF L 3 hL E hE (by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hQ : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [hQ] at hpairs
  calc
    E.card*M^2 ≤ (L.card*(Nat.card K+1)^2)*M^2 := Nat.mul_le_mul_right _ hpairs
    _ = (L.card*M^2)*(Nat.card K+1)^2 := by ring
    _ ≤ (2*X.card^2)*(Nat.card K+1)^2 := Nat.mul_le_mul_right _ hplanes

theorem dominant_pair_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F) (M : ℕ)
    (hdom : ∀ p ∈ E, ∃ l : RadialLine x, l.val ≤ p.1 ⊓ p.2 ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card ≤ (richRadials x X ⊤ M).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i)^2 := by
  let R := richRadials x X ⊤ M
  let L := R.image Subtype.val
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := pair_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro p hp
    obtain ⟨l,hl,hM⟩ := hdom p hp
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, le_top⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  simpa only [he] using hN

end SharpRamseyFive.ActualOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MomentWeightedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Pairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

omit [Finite K] in
lemma dominant_witness (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    {δ a : ℝ} (hδ : 0 < δ) (ha : a ≤ δ*(pairPoints x X A B).card)
    (hnd : ¬∀ l : RadialLine x,
      2*((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X A B).card) :
    ∃ l : RadialLine x, l.val ≤ A ⊓ B ∧
      ⌈a/(2*δ)⌉₊ ≤ (RadialLine.trainingOnLine X l).card := by
  classical
  push Not at hnd
  obtain ⟨l,hl⟩ := hnd
  have hp : 0 < ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card := by omega
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hp
  obtain ⟨hyP,hyl⟩ := Finset.mem_filter.mp hy
  have hyAB : y.val.submodule ≤ A ⊓ B := (Finset.mem_filter.mp hyP).2
  have he : RadialLine.through x y.val y.property = l :=
    (RadialLine.through_eq_iff y.property l).mpr hyl
  refine ⟨l,?_,?_⟩
  · rw [←he]
    exact (RadialLine.through_le_iff _ _).mpr ⟨le_inf hxA hxB,hyAB⟩
  · have hs : ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val) ⊆
        RadialLine.trainingOnLine X l := by
      intro z hz
      obtain ⟨hzP,hzl⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzP).1,hzl⟩
    have hc := Finset.card_le_card hs
    have hcr : (pairPoints x X A B).card < 2*((RadialLine.trainingOnLine X l).card:ℝ) := by
      exact_mod_cast (by omega : (pairPoints x X A B).card < 2*(RadialLine.trainingOnLine X l).card)
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hδ)).mpr
    nlinarith

theorem pair_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ((pairs x X F δ a).card:ℝ)*a^2 ≤
      (richRadials x X ⊤ ⌈a/(2*δ)⌉₊).card * ((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2 +
      2*δ^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
  classical
  let E := pairs x X F δ a
  let nd (p : Submodule K V × Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X p.1 p.2).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X p.1 p.2).card
  let N := E.filter nd
  let D := E.filter (fun p => ¬nd p)
  have hE : E ⊆ F ×ˢ F := Finset.filter_subset _ _
  have hne (p) (hp : p ∈ E) : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.1
  have hM (p) (hp : p ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X p.1 p.2).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hp).2.2))
  have hN := nondominant_pair_count x hdim X F hF hxF N
    ((Finset.filter_subset _ _).trans hE) (fun p hp => hne p (Finset.mem_filter.mp hp).1)
    ⌈a/δ⌉₊ (fun p hp => hM p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hD := dominant_pair_count x (d := 4) hdim X F hF D
    ((Finset.filter_subset _ _).trans hE) ⌈a/(2*δ)⌉₊ (by
      intro p hp
      obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hE hp)
      exact dominant_witness x X p.1 p.2 (hxF _ h1) (hxF _ h2) hδ
        (Finset.mem_filter.mp hp).2.2 hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have hcD : (D.card:ℝ) ≤ (richRadials x X ⊤ ⌈a/(2*δ)⌉₊).card *
      ((Nat.card K:ℝ)^2+Nat.card K+1)^2 := by exact_mod_cast hD
  have hcN : (N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤ 2*(X.card:ℝ)^2*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) := (div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ)) |>.trans_eq (mul_comm _ _)
  have ha2 := pow_le_pow_left₀ ha hceil 2
  have hN' : (N.card:ℝ)*a^2 ≤ 2*δ^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
    calc
      _ ≤ (N.card:ℝ)*(δ*⌈a/δ⌉₊)^2 := mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ = δ^2*((N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
      _ ≤ δ^2*(2*(X.card:ℝ)^2*((Nat.card K:ℝ)+1)^2) :=
        mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
      _ = _ := by ring
  have he : N.card+D.card=E.card := Finset.card_filter_add_card_filter_not nd
  have her : (N.card:ℝ)+(D.card:ℝ)=E.card := by exact_mod_cast he
  change (E.card:ℝ)*a^2 ≤ _
  rw [←her,add_mul]
  exact (add_le_add hN' (mul_le_mul_of_nonneg_right hcD (sq_nonneg a))).trans_eq (by ring)

end SharpRamseyFive.WeightedOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators
open SharpRamseyFive.DyadicMoments

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma strength_nonneg (a : D → ℝ≥0) (p : DistinctPairs H) :
    0 ≤ strength lines a p := by unfold strength; positivity

end SharpRamseyFive.WeightedPrograms

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_inFlat (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    PoissonScore.mass (radialWeight x X δ) (RadialLine.inFlat W) =
      (δ:ℝ) * (X.filter fun y => y.val.submodule ≤ W).card := by
  unfold PoissonScore.mass radialWeight
  simp only [NNReal.coe_mul, NNReal.coe_natCast, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [RadialLine.sum_trainingOnLine X W hx]

lemma mass_overlap (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
  unfold pencilLines
  rw [RadialLine.inFlat_inf, mass_inFlat x X δ _ (le_inf (hF H.val H.property)
    (hF H'.val H'.property))]
  simp only [Incident, le_inf_iff]
  rfl

lemma overlap_pos_lower (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F)
    (h : 0 < PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) :
    (δ:ℝ) ≤ PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') := by
  rw [mass_overlap x X δ F hF] at h ⊢
  have hc : 0 < (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    by_contra hn
    have := Nat.eq_zero_of_not_pos hn
    simp [this] at h
  have hcast : (1:ℝ) ≤ (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    exact_mod_cast hc
  exact (mul_one (δ:ℝ)).symm.trans_le (mul_le_mul_of_nonneg_left hcast δ.coe_nonneg)

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma submodule_eq_ker_annihilator (b : ℙ K (Module.Dual K V)) :
    b.submodule = (LinearMap.ker b.rep).dualAnnihilator := by
  have hle : b.submodule ≤ (LinearMap.ker b.rep).dualAnnihilator := by
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
    intro v hv
    exact hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker b.rep)
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  rw [Projectivization.finrank_submodule]
  omega

lemma kernel_injective : Function.Injective (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) := by
  intro b c h
  apply Projectivization.submodule_injective
  simp only [submodule_eq_ker_annihilator,h]

variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_pairPoints (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ)*(ActualOverlap.pairPoints x X (LinearMap.ker H.val.rep)
        (LinearMap.ker H'.val.rep)).card := by
  rw [mass_overlap x X δ F hF]
  simp only [ActualOverlap.pairPoints, NondominantOverlap.onPlane, Incident, le_inf_iff]
  rfl

lemma distinctPairs_ext {H : Type*} {p q : WeightedPrograms.DistinctPairs H}
    (h₁ : p.1=q.1) (h₂ : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨p,p',hp⟩
  rcases q with ⟨q,q',hq⟩
  cases h₁
  cases h₂
  rfl

lemma pair_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (a : ℝ) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card ≤
    (WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a).card := by
  let E := Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)
  let G := WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a
  let f (p : E) : G := ⟨(LinearMap.ker p.val.1.val.rep,LinearMap.ker p.val.2.val.val.rep),by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.1.property,rfl⟩,
      Finset.mem_image.mpr ⟨_,p.val.2.val.property,rfl⟩⟩,?_,?_⟩
    · intro h
      exact p.val.2.property (Subtype.ext (kernel_injective h).symm)
    · have hp := (Finset.mem_filter.mp p.property).2
      change a ≤ PoissonScore.mass (radialWeight x X δ)
        (pencilLines x F p.val.1 ∩ pencilLines x F p.val.2.val) at hp
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply distinctPairs_ext
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.1) he
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.2) he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [Finite K]

theorem score_pair_count_four (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card:ℝ)*a^2 ≤
      (ActualOverlap.richRadials x X ⊤ ⌈a/(2*(δ:ℝ))⌉₊).card *
        ((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2 +
      2*(δ:ℝ)^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdimG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A : Submodule K V) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hc : ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card:ℝ) ≤
      (WeightedOverlap.pairs x X G δ a).card := by
    exact_mod_cast pair_strength_count_le x X δ F hF a
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.pair_count_four x hdim X G hdimG hxG (by exact_mod_cast hδ) ha)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

lemma richRadials_le_localLines (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (hδ : 0<δ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) :
    (ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊).card ≤
      (localLines S O δ a L x).card := by
  let E := ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊
  let G := localLines S O δ a L x
  let f (l : E) : G := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hL l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      have hr' : a/δ ≤ ((RadialLine.trainingOnLine (outsideAt x S (O x)) l.val).card:ℝ) :=
        Nat.ceil_le.mp hr
      have hh := (div_le_iff₀ hδ).mp hr'
      rw [mul_comm] at hh
      change a ≤ δ*((((outsideAt x S (O x)).filter
        fun y => y.val.submodule ≤ l.val.val)).card:ℝ) at hh
      rwa [outsideAt_filter_card] at hh⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : G => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

theorem score_pairs_off_radial_exception (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H)
    (a D : ℝ) (ha : 0≤a) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) L Q D) :
    ((Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F => a≤
      WeightedPrograms.strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ)*a^2 ≤
      D*((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2+
      2*(δ:ℝ)^2*((outsideAt x S (O x)).card:ℝ)^2*((Nat.card K:ℝ)+1)^2 := by
  have hlocal : ((localLines S O δ (a/2) L x).card:ℝ)<D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  have he : a/(2*(δ:ℝ))=(a/2)/(δ:ℝ) := by ring
  have hr := richRadials_le_localLines x S O δ (a/2) (by exact_mod_cast hδ) L hL
  have hr' : ((ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/(2*(δ:ℝ))⌉₊).card:ℝ) ≤ D := by
    rw [he]
    have hrR : ((ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈(a/2)/(δ:ℝ)⌉₊).card:ℝ) ≤
        (localLines S O δ (a/2) L x).card := by exact_mod_cast hr
    exact hrR.trans hlocal.le
  have hh := score_pair_count_four x hdim (outsideAt x S (O x)) δ hδ F hF a ha
  apply hh.trans
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OverlapDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in

lemma score_dyadic_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  change ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ mass (radialWeight x X δ)
    (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ∧
    mass (radialWeight x X δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤ 2*((δ:ℝ)*2^i)
  rw [mass_overlap x X δ F hF]
  unfold overlapDyads
  apply dyadic_cover δ _ (by positivity)
  · have hl:=overlap_pos_lower x X δ F hF p.1 p.2.val hp
    rwa [mass_overlap x X δ F hF] at hl
  · have hc : ((X.filter fun y => Incident y.val p.1.val ∧ Incident y.val p.2.val.val).card:ℝ) ≤
        (2:ℝ)^Nat.clog 2 X.card := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (Nat.le_pow_clog (by omega : 1<2) X.card)
    exact mul_le_mul_of_nonneg_left hc (by positivity)

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem pow_sum_from_lower (x : α → ℝ) (m A : ℝ) (K R : ℕ) (hm0 : 0 ≤ m) (hKR : K ≤ R)
    (hx : ∀ v,0 ≤ x v) (hm : ∀ v,x v ≤ m) (hA : (∑ v,x v^K) ≤ A) :
    (∑ v,x v^R) ≤ m^(R-K)*A := by
  have hpow (v : α) : x v^R ≤ m^(R-K)*x v^K := by
    have he : R=(R-K)+K := by omega
    calc
      _ = x v^(R-K)*x v^K := by rw [←pow_add,←he]
      _  ≤  _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx v) (hm v) _) (pow_nonneg (hx v) _)
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpow v)).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (pow_nonneg hm0 _)

end SharpRamseyFive.DyadicMoments
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma boundedOverlapDyads_card (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (m : ℝ) :
    (boundedOverlapDyads x X δ m).card ≤ Nat.clog 2 X.card+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

omit [FiniteDimensional K V] [Finite K] in
lemma strength_le_typical_cap (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) : strength (pencilLines x F) (radialWeight x X δ) p ≤ m := by
  apply le_trans _ (hm p.1)
  change mass _ (_ ∩ _) ≤ mass _ _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
  intro d _ _
  exact NNReal.coe_nonneg _

omit [Finite K] in
lemma bounded_overlap_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈boundedOverlapDyads x X δ m,
      (δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  obtain ⟨i,hi,hlo,hhi⟩ := score_dyadic_cover x X δ hδ F hF p hp
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (strength_le_typical_cap x X δ F m hm p)⟩,hlo,hhi⟩

omit [Finite K] in

theorem score_polynomial_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (m A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : k≠0)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (hcount : ∀ i∈boundedOverlapDyads x X δ m,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^k) ≤
      2^k*(Nat.clog 2 X.card+1)*A := by
  apply (moment_polynomial_tail _ _ (boundedOverlapDyads x X δ m) k hk A
    (strength_nonneg _ _) (by intro i _; positivity)
    (bounded_overlap_cover x X δ hδ F hF m hm) hcount).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast boundedOverlapDyads_card x X δ m) (by positivity)) hA

omit [Finite K] in

theorem score_higher_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (A : ℝ) (hA : 0 ≤ A) (k R : ℕ) (hk : k≠0) (hkR : k ≤ R)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcount : ∀ i∈boundedOverlapDyads x X δ 2,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^R) ≤
      2^R*(Nat.clog 2 X.card+1)*A := by
  have hh := pow_sum_from_lower _ 2 _ k R (by norm_num) hkR
    (strength_nonneg (pencilLines x F) (radialWeight x X δ))
    (strength_le_typical_cap x X δ F 2 hm)
    (score_polynomial_power x X δ hδ F hF 2 A hA k hk hm hcount)
  apply hh.trans_eq
  rw [←mul_assoc,←mul_assoc,←pow_add,Nat.sub_add_cancel hkR]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_ScaleAgainstB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma scale_against_B {q n r s : ℝ} (hn : 0<n)
    (h : n^2*r ≤ q^4*s) : q^4*r ≤ (q^4/n)^2*s := by
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp
  calc
    _ = q^4*(n^2*r) := by ring
    _ ≤ q^4*(q^4*s) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

theorem normalized_pair_low {q n a χ E : ℝ} (hn : 0<n) (ha : 0≤a) (ha2 : a≤2)
    (hlow : n ≤ q^2*Real.exp (χ/2)) (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (hpower : E*a^200 ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198) :
    E*a^200 ≤ (q^4/n)^2*Real.exp (2*χ) := by
  have hx : (Real.exp (χ/2))^2=Real.exp χ := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hs : n^2 ≤ q^4*Real.exp χ := by
    have hh := pow_le_pow_left₀ hn.le hlow 2
    rw [mul_pow,hx] at hh
    norm_num only [← pow_mul] at hh
    exact hh
  have hB : q^4 ≤ (q^4/n)^2*Real.exp χ := by
    simpa only [mul_one] using scale_against_B hn (r := 1) (by simpa using hs)
  have he := mul_le_mul hB (pow_le_pow_left₀ ha ha2 198)
    (pow_nonneg ha 198) (by positivity : 0 ≤ (q^4/n)^2*Real.exp χ)
  have hsum : 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 ≤
      11*2^200*(q^4/n)^2*Real.exp χ := by
    calc
      _ ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*((q^4/n)^2*Real.exp χ*2^198) := by
        apply add_le_add_right
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤8)
      _ = _ := by ring
  apply (hpower.trans hsum).trans
  calc
    _ ≤ Real.exp χ*(q^4/n)^2*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchi (sq_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add];ring

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PencilFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma pencil_factor {q : ℝ} (hq : 1  ≤  q) :
    (q^2+q+1)^2  ≤  9*q^4 ∧ (q+1)^2  ≤  4*q^2 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hq2 : q  ≤  q^2 := by nlinarith
  have hp : q^2+q+1  ≤  3*q^2 := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q^2+q+1) hp 2
  have ht := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q+1) (by linarith : q+1 ≤ 2*q) 2
  constructor <;> nlinarith

theorem pair_power_two_hundred {q n δ N a χ E : ℝ}
    (hq : 1 ≤ q) (hn : 0<n) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : δ*N ≤ q)
    (hgeom : E*a^2  ≤  (q^4/n^2*Real.exp χ/(a/2)^100)*(q^2+q+1)^2*a^2+
      2*δ^2*N^2*(q+1)^2) :
    E*a^200  ≤  9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 := by
  obtain ⟨hpoly,htwo⟩ := pencil_factor hq
  have hm2 : δ^2*N^2 ≤ q^2 := by
    have := pow_le_pow_left₀ (mul_nonneg hδ hN) hmass 2
    nlinarith
  have hnoise : 2*δ^2*N^2*(q+1)^2  ≤  8*q^4 := by
    calc
      _ = 2*(δ^2*N^2)*(q+1)^2 := by ring
      _ ≤ 2*q^2*(4*q^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hm2 (by norm_num)) htwo
        (sq_nonneg (q+1)) (by positivity)
      _ = _ := by ring
  have hmain : (q^4/n^2*Real.exp χ/(a/2)^100)*(q^2+q+1)^2*a^2  ≤
      (q^4/n^2*Real.exp χ/(a/2)^100)*(9*q^4)*a^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg a)
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hh := mul_le_mul_of_nonneg_right (hgeom.trans (add_le_add hmain hnoise))
    (pow_nonneg ha.le 198)
  have he : ((q^4/n^2*Real.exp χ/(a/2)^100)*(9*q^4)*a^2)*a^198 =
      9*2^100*(q^4/n)^2*Real.exp χ*a^100 := by
    field_simp
  have hp : a^2*a^198=a^200 := by rw [←pow_add]
  rw [add_mul,mul_assoc E (a^2),hp,he] at hh
  apply hh.trans
  apply add_le_add_left
  calc
    _  ≤  9*2^100*(q^4/n)^2*Real.exp χ*2^100 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le ha2 100) (by positivity)
    _ = 9*2^200*(q^4/n)^2*Real.exp χ := by ring

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OutsideCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_card_le (S O : Finset (ℙ K V)) : (outsideAt x S O).card ≤ S.card := by
  unfold outsideAt
  rw [Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.sdiff_subset)

theorem score_pair_low_normalized (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) L Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)) :
    ((Finset.univ.filter fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0<Nat.card K)
  have hN : (δ:ℝ)*(outsideAt x S (O x)).card ≤ Nat.card K := by
    apply le_trans _ hmass
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast outsideAt_card_le x S (O x)) δ.coe_nonneg
  apply ScoreScalars.normalized_pair_low hn ha.le ha2 hlow hchi
  exact ScoreScalars.pair_power_two_hundred hq hn δ.coe_nonneg (Nat.cast_nonneg _) ha ha2 hN
    (score_pairs_off_radial_exception x hdim S O δ hδ F hF _ _ ha.le L hL Q hx hgood)

theorem score_pair_low_moment_oai (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ : ℝ) (hn : 0<n) (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) L Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ)) := by
  apply score_higher_power x _ δ hδ F hF _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  exact score_pair_low_normalized x hdim S O δ hδ F hF n _ χ hn (by positivity)
    (Finset.mem_filter.mp hi).2 hmass hlow hchi L hL Q hx (hgood i hi)

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment_oai := @OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment_oai
