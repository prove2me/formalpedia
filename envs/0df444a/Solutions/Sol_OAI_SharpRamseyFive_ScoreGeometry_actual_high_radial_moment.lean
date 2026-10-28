-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:13.049816+00:00
-- url     : https://prove2.me/submissions/36a25a30-8f3c-4299-a002-3e88330be517

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_AmbientEnumeration_ambient_refined_truncated_moment

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

theorem card_hyperplanes [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} (l : RadialLine x) :
    Nat.card {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ↔ b.submodule ≤ l.val.dualAnnihilator := by
    rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq l.val
  rw [l.property.1] at h
  congr 2
  omega

theorem card_hyperplanes_pair [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} {l m : RadialLine x} (hlm : l ≠ m) :
    Nat.card {b : ℙ K (Module.Dual K V) //
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 3), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep ↔
        b.submodule ≤ (l.val ⊔ m.val).dualAnnihilator := by
    rw [← sup_le_iff, Projectivization.submodule_eq b,
      Submodule.span_singleton_le_iff_mem, Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (l.val ⊔ m.val)
  rw [finrank_sup hlm] at h
  congr 2
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

lemma neighbor_count_by_intersection {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (H : Submodule K V) (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, H ⊓ A ∈ L) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    exact Finset.mem_biUnion.mpr ⟨H ⊓ A,hEL A hA,Finset.mem_filter.mpr ⟨hE hA,inf_le_right⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma neighbor_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, ∃ W ∈ L, W ≤ A) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    obtain ⟨W,hW,hWA⟩ := hEL A hA
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_filter.mpr ⟨hE hA,hWA⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma rich_radial_count {x : ℙ K V} [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (W : Submodule K V) (hx : x.submodule ≤ W)
    (L : Finset (RadialLine x)) (hL : L ⊆ RadialLine.inFlat W) (M : ℕ)
    (hM : ∀ l ∈ L, M ≤ (RadialLine.trainingOnLine X l).card) :
    L.card*M ≤ (X.filter fun y => y.val.submodule ≤ W).card := by
  have h := Finset.sum_le_sum hM
  simp only [Finset.sum_const_nat] at h
  apply h.trans
  rw [← RadialLine.sum_trainingOnLine X W hx]
  exact Finset.sum_le_sum_of_subset hL

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

theorem nondominant_degree_count (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F)
    (hne : ∀ A ∈ E, H ≠ A) (M : ℕ)
    (hM : ∀ A ∈ E, M ≤ (pairPoints x X H A).card)
    (hnd : ∀ A ∈ E, ∀ l : RadialLine x,
      2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X H A).card) :
    E.card*M^2 ≤ 2*(onPlane x X H).card^2*(Nat.card K+1) := by
  let L := E.image fun A => H ⊓ A
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 3 := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact hyperplane_intersection_rank (d := 4) hdim H A hH (hF A (hE hA)) (hne A hA)
  have hxL (W : Submodule K V) (hW : W ∈ L) : x.submodule ≤ W := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact le_inf hxH (hxF A (hE hA))
  have hpoints (A : Submodule K V) :
      onPlane x (onPlane x X H) (H ⊓ A) = pairPoints x X H A := by
    ext y
    simp only [onPlane,pairPoints,Finset.mem_filter,le_inf_iff]
    tauto
  have hplanes := rich_nondominant_plane_count x (onPlane x X H) L hL hxL M (by
    intro W hW
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hM A hA) (by
    intro W hW l
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hnd A hA l)
  have hpairs := neighbor_count_by_intersection (d := 4) hdim F hF L 3 hL H E hE (by
    intro A hA
    exact Finset.mem_image.mpr ⟨A,hA,rfl⟩)
  have hQ : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [hQ] at hpairs
  calc
    E.card*M^2 ≤ (L.card*(Nat.card K+1))*M^2 := Nat.mul_le_mul_right _ hpairs
    _ = (L.card*M^2)*(Nat.card K+1) := by ring
    _ ≤ (2*(onPlane x X H).card^2)*(Nat.card K+1) := Nat.mul_le_mul_right _ hplanes

theorem dominant_degree_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (H : Submodule K V) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F) (M : ℕ)
    (hdom : ∀ A ∈ E, ∃ l : RadialLine x, l.val ≤ H ⊓ A ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card*M ≤ (onPlane x X H).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i) := by
  let R := richRadials x X H M
  let L := R.image Subtype.val
  have hcR : R.card*M ≤ (onPlane x X H).card :=
    rich_radial_count X H hxH R (Finset.filter_subset _ _) M (by
      intro l hl
      exact (Finset.mem_filter.mp hl).2)
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := neighbor_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro A hA
    obtain ⟨l,hl,hM⟩ := hdom A hA
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl.trans inf_le_right⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, hl.trans inf_le_left⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  rw [he] at hN
  calc
    E.card*M ≤ (R.card*(∑ i ∈ Finset.range (d-1), Nat.card K^i))*M := Nat.mul_le_mul_right _ hN
    _ = (R.card*M)*(∑ i ∈ Finset.range (d-1), Nat.card K^i) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcR

end SharpRamseyFive.ActualOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma scale_nonneg (d : ℕ) (n : ℝ) (hn : 0≤n) : 0≤ scale (K:=K) d n := by
  unfold scale
  positivity

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma clippedWeight_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option (Option J)) (H : ℙ K (Dual K V)) :
    0 ≤ clippedWeight S C j H ∧ clippedWeight S C j H≤1 := by
  cases j with
  | none => simp only [clippedWeight]; split <;> norm_num
  | some j => exact ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

end SharpRamseyFive.ScoreRegularity

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

end SharpRamseyFive.WeightedOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DegreeCountFour
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

theorem degree_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  let nd (A : Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X H A).card
  let N := E.filter nd
  let D := E.filter (fun A => ¬nd A)
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hne (A) (hA : A ∈ E) : H ≠ A := (Finset.mem_filter.mp hA).2.1
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH N
    ((Finset.filter_subset _ _).trans hE) (fun A hA => hne A (Finset.mem_filter.mp hA).1)
    ⌈a/δ⌉₊ (fun A hA => hM A (Finset.mem_filter.mp hA).1)
    (fun A hA => (Finset.mem_filter.mp hA).2)
  have hD := dominant_degree_count x (d := 4) hdim X F hF H hxH D
    ((Finset.filter_subset _ _).trans hE) ⌈a/(2*δ)⌉₊ (by
      intro A hA
      obtain ⟨hA,hn⟩ := Finset.mem_filter.mp hA
      exact dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have hcD : (D.card:ℝ)*⌈a/(2*δ)⌉₊ ≤ (onPlane x X H).card *
      ((Nat.card K:ℝ)^2+Nat.card K+1) := by exact_mod_cast hD
  have hcN : (N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  have hceil₂ : a ≤ 2*δ*(⌈a/(2*δ)⌉₊:ℝ) :=
    ((div_le_iff₀ (mul_pos (by norm_num) hδ)).mp (Nat.le_ceil (a/(2*δ)))).trans_eq (mul_comm _ _)
  have hD' : (D.card:ℝ)*a ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1) := by
    calc
      _ ≤ (D.card:ℝ)*(2*δ*⌈a/(2*δ)⌉₊) := mul_le_mul_of_nonneg_left hceil₂ (by positivity)
      _ = 2*δ*((D.card:ℝ)*⌈a/(2*δ)⌉₊) := by ring
      _ ≤ 2*δ*((onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)) :=
        mul_le_mul_of_nonneg_left hcD (by positivity)
      _ = _ := by ring
  have hN' : (N.card:ℝ)*a^2 ≤ 2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
    calc
      _ ≤ (N.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
      _ = δ^2*((N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
      _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
      _ = _ := by ring
  have he : N.card+D.card=E.card := Finset.card_filter_add_card_filter_not nd
  have her : (N.card:ℝ)+(D.card:ℝ)=E.card := by exact_mod_cast he
  change (E.card:ℝ)*a^2 ≤ _
  rw [←her,add_mul]
  have hDa := mul_le_mul_of_nonneg_right hD' ha
  nlinarith

theorem nondominant_weighted_degree (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a)
    (hline : ∀ l : RadialLine x, δ*(RadialLine.trainingOnLine X l).card < a/2) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH E hE
    (fun A hA => (Finset.mem_filter.mp hA).2.1) ⌈a/δ⌉₊ hM (by
      intro A hA
      by_contra hn
      obtain ⟨l,_,hl⟩ := dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn
      have hlg : a/(2*δ) ≤ ((RadialLine.trainingOnLine X l).card:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hl)
      have hh := (div_le_iff₀ (mul_pos (by norm_num) hδ)).mp hlg
      have hh' := hline l
      nlinarith)
  have hcN : (E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  calc
    _ ≤ (E.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
    _ = δ^2*((E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
    _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
    _ = _ := by ring

end SharpRamseyFive.WeightedOverlap

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

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
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LabelledFilterCard
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

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma shiftKernel_range (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : shiftKernel weight lines p K x y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold shiftKernel
  exact ⟨le_min zero_le_one (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (mass_nonneg _ _)) _),
    min_le_left _ _⟩

end SharpRamseyFive.SingletonEnumeration
end

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

namespace SharpRamseyFive.SingletonEnumeration
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments
open SharpRamseyFive.WeightedPrograms
open Classical
variable {D H V I B : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq I]

lemma sum_split_diagonal (F : H → ℝ) (y : H) :
    (∑ x : H, F x) = F y + ∑ x : {x : H // x ≠ y}, F x := by
  rw [← Finset.sum_erase_add _ F (Finset.mem_univ y), add_comm]
  congr 1
  exact Finset.sum_subtype _ (by intro x; simp) F

lemma sum_pairs_split_diagonal (F : H → H → ℝ) :
    (∑ x : H, ∑ y : H, F x y) =
      (∑ x : H, F x x) + ∑ z : DistinctPairs H, F z.1 z.2 := by
  change _ = _ + ∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => sum_split_diagonal (F x) x)

omit [Fintype D] [DecidableEq B] in

theorem pairMoment_labelled_le (lines : H → Finset D) (rate : D → ℝ≥0)
    (K : ℕ) (mass : ℝ) (_hm : 0 ≤ mass)
    (hmass : ∀ x, ∑ d ∈ lines x, (rate d : ℝ) ≤ mass) :
    pairMoment (B := B) (fun x : H × V => lines x.1) rate K ≤
      (Fintype.card V : ℝ) ^ 2 *
        (pairMoment (B := B) lines rate K +
          Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K) := by
  let F : H → H → ℝ := fun x y =>
    ((Fintype.card B : ℝ) * ∑ d ∈ lines x ∩ lines y, (rate d : ℝ)) ^ K
  have hF : ∀ x y, 0 ≤ F x y := by intro x y; dsimp [F]; positivity
  have he : pairMoment (B := B) lines rate K = ∑ x : H, ∑ y : {y : H // y ≠ x}, F x y := rfl
  have hdiag : (∑ x : H, F x x) ≤
      Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    apply (Finset.sum_le_sum (fun x _ => show F x x ≤
      ((Fintype.card B : ℝ) * mass) ^ K from ?_)).trans_eq (by simp)
    dsimp [F]
    simp only [Finset.inter_self]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hmass x) (Nat.cast_nonneg _)) K
  have hfull : (∑ x : H, ∑ y : H, F x y) ≤
      pairMoment (B := B) lines rate K + Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    rw [sum_pairs_split_diagonal, add_comm]
    change (∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2) + _ ≤ _
    rw [Fintype.sum_sigma, ← he]
    exact add_le_add le_rfl hdiag
  calc
    _ ≤ ∑ x : H × V, ∑ y : H × V, F x.1 y.1 := by
      unfold pairMoment
      apply Finset.sum_le_sum
      intro x _
      rw [sum_split_diagonal _ x]
      apply le_add_of_nonneg_left (hF _ _)
    _ = (Fintype.card V : ℝ) ^ 2 * (∑ x : H, ∑ y : H, F x y) := by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfull (by positivity)

end SharpRamseyFive.SingletonEnumeration

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

lemma mass_pencil (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val).card :=
  mass_inFlat x X δ _ (hF H.val H.property)

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

variable [Finite K]

lemma one_anchor_count (F : Finset (ℙ K (Module.Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-2), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} := fun H =>
    ⟨H.val.val, (Finset.mem_filter.mp H.property).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} => b.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes l, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

lemma two_anchor_count (F : Finset (ℙ K (Module.Dual K V)))
    (l m : RadialLine x) (hlm : l ≠ m) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-3), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} :=
    fun H => ⟨H.val.val, (Finset.mem_filter.mp H.property.1).2,
      (Finset.mem_filter.mp H.property.2).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} => b.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes_pair hlm, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

omit [Fintype (RadialLine x)] in
lemma pencil_size (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) :
    F.card ≤ ∑ i ∈ Finset.range (finrank K V-1), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : F → {b : ℙ K (Module.Dual K V) // Incident x b} := fun H => ⟨H.val,hF H.val H.property⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // Incident x b} => b.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [card_hyperplanes_through_point, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

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

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DegreeStrengthCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma degree_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) :
    (Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card ≤
    (WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a).card := by
  let E := Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))
  let G := WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a
  let f (p : E) : G := ⟨LinearMap.ker p.val.val.rep,by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.property,rfl⟩,?_,?_⟩
    · intro h
      exact (Finset.mem_filter.mp p.property).2.1 (Subtype.ext (kernel_injective h))
    · have hp := (Finset.mem_filter.mp p.property).2.2
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply Subtype.ext
    exact kernel_injective (congrArg (fun z : G => z.val) he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [Finite K]

theorem score_degree_four (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*PoissonScore.mass (radialWeight x X δ) (pencilLines x F H)*
        ((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.degree_count_four x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha)
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

theorem score_degree_truncated (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a)
    (hline : ∀ l : RadialLine x, (radialWeight x X δ l:ℝ) < a/2) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.nondominant_weighted_degree x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha (by
        intro l
        simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hline l))
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in
lemma offRow_nonneg (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H H' : F) : 0 ≤ offRow x X δ F H H' := by
  unfold offRow
  split_ifs
  · rfl
  · exact mass_nonneg _ _

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

end SharpRamseyFive.ScoreGeometry

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

theorem degree_power_two_hundred {q m a D : ℝ} (hq : 1 ≤ q)
    (hm : 0 ≤ m) (hm2 : m ≤ 2) (ha : 0 ≤ a)
    (hgeom : D*a^2 ≤ 2*m*(q^2+q+1)*a+2*m^2*(q+1)) :
    D*a^200  ≤  12*q^2*a^199+16*q*a^198 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hq2 : q ≤ q^2 := by nlinarith
  have hpoly : q^2+q+1 ≤ 3*q^2 := by nlinarith
  have hm4 : m^2 ≤ 4 := by nlinarith
  have hfirst : 2*m*(q^2+q+1)*a ≤ 12*q^2*a := by
    apply mul_le_mul_of_nonneg_right _ ha
    calc
      _  ≤  4*(3*q^2) := mul_le_mul (by linarith) hpoly (by positivity) (by norm_num)
      _ = _ := by ring
  have hsecond : 2*m^2*(q+1) ≤ 16*q := by
    calc
      _  ≤  8*(2*q) := mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right (hgeom.trans (add_le_add hfirst hsecond)) (pow_nonneg ha 198)
  have heL : D*a^2*a^198=D*a^200 := by ring
  have heR : (12*q^2*a+16*q)*a^198=12*q^2*a^199+16*q*a^198 := by ring
  rwa [heL,heR] at hh

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_QB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma q_le_B {q n : ℝ} (hq : 0<q) (hn : 0<n) (hcap : n≤q^3) :
    q ≤ q^4/n := by
  apply (le_div_iff₀ hn).mpr
  calc q*n ≤ q*q^3 := mul_le_mul_of_nonneg_left hcap hq.le
       _ = q^4 := by ring

theorem normalized_degree_small {q n a χ D C : ℝ} (hq : 0<q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3) (hsmall : n*a≤C*q^2)
    (hexp : (12*C+16)*2^198≤Real.exp (2*χ))
    (hpower : D*a^200 ≤ 12*q^2*a^199+16*q*a^198) :
    D*a^200 ≤ (q^4/n)*Real.exp (2*χ) := by
  have hqa : q^2*a≤C*(q^4/n) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    calc
      _ = q^2*(n*a) := by ring
      _ ≤ q^2*(C*q^2) := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by field_simp
  have hfirst : q^2*a^199≤C*(q^4/n)*a^198 := by
    calc _ = (q^2*a)*a^198 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hqa (pow_nonneg ha 198)
  have hsecond := mul_le_mul_of_nonneg_right (q_le_B hq hn hcap) (pow_nonneg ha 198)
  have hC : 0≤C := by
    have := mul_nonneg hn.le ha
    nlinarith [sq_pos_of_pos hq]
  apply hpower.trans
  calc
    _ = 12*(q^2*a^199)+16*(q*a^198) := by ring
    _ ≤ 12*(C*(q^4/n)*a^198)+16*(q^4/n*a^198) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = (q^4/n)*((12*C+16)*a^198) := by ring
    _ ≤ (q^4/n)*((12*C+16)*2^198) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha ha2 198) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

theorem normalized_degree_truncated {q n a χ D : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3)
    (hexp : (16*2^198:ℝ)≤Real.exp (2*χ))
    (hpower : D*a^2≤8*(q+1)) : D*a^200≤(q^4/n)*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hh := mul_le_mul_of_nonneg_right hpower (pow_nonneg ha 198)
  have he : D*a^2*a^198=D*a^200 := by ring
  rw [he] at hh
  apply hh.trans
  calc
    _ ≤ 16*q*a^198 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha 198)
      linarith
    _ ≤ 16*(q^4/n)*2^198 := mul_le_mul
      (mul_le_mul_of_nonneg_left (q_le_B hq0 hn hcap) (by norm_num))
      (pow_le_pow_left₀ ha ha2 198) (pow_nonneg ha 198) (by positivity)
    _ = (q^4/n)*(16*2^198) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoreDegreeLowNormalized
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
lemma offRow_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H)≤ m) (H H' : F)
    (hp : 0<offRow x X δ F H H') :
    ∃ i∈boundedOverlapDyads x X δ m,(δ:ℝ)*2^i≤offRow x X δ F H H' ∧
      offRow x X δ F H H'≤2*((δ:ℝ)*2^i) := by
  have hn : H≠H' := by intro he; simp only [offRow,ite_eq_left he] at hp; linarith
  have hp' : 0 < strength (pencilLines x F) (radialWeight x X δ) ⟨H,⟨H',Ne.symm hn⟩⟩ := by
    simpa only [offRow,ite_eq_right hn,strength,mass] using hp
  simpa only [offRow,ite_eq_right hn,strength,mass] using
    bounded_overlap_cover x X δ hδ F hF m hm ⟨H,⟨H',Ne.symm hn⟩⟩ hp'

omit [FiniteDimensional K V] [Finite K] in

theorem shift_row_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (p k : ℕ) (hk : k≠0)
    (A : ℝ) (hA : (∑ H',offRow x X δ F H H'^k)≤A) :
    (∑ H',SingletonEnumeration.shiftKernel (radialWeight x X δ) (pencilLines x F) p k H' H)≤
      1+(p:ℝ)^k*A := by
  have hs : (∑ H' : F,if H=H' then (1:ℝ) else 0)=1 := by simp
  calc
    _ ≤ ∑ H' : F,((if H=H' then (1:ℝ) else 0)+((p:ℝ)*offRow x X δ F H H')^k) := by
      apply Finset.sum_le_sum
      intro H' _
      by_cases he : H=H'
      · simp only [ite_eq_left he,offRow,mul_zero,zero_pow hk,add_zero]
        exact (SingletonEnumeration.shiftKernel_range _ _ p k H' H).2
      · simp only [ite_eq_right he,offRow,zero_add]
        unfold SingletonEnumeration.shiftKernel
        rw [Finset.inter_comm]
        exact min_le_right _ _
    _ = 1+(p:ℝ)^k*(∑ H',offRow x X δ F H H'^k) := by
      rw [Finset.sum_add_distrib,hs]
      simp only [mul_pow,Finset.mul_sum]
    _ ≤ 1+(p:ℝ)^k*A := add_le_add_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (Nat.cast_nonneg p) k)) 1

omit [FiniteDimensional K V] [Finite K] in

theorem shift_pair_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p k : ℕ) (A : ℝ)
    (hA : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k)≤A) :
    (∑ H : F,∑ H' : F,SingletonEnumeration.shiftKernel (radialWeight x X δ)
      (pencilLines x F) p k H H') ≤ F.card+(p:ℝ)^k*A := by
  rw [SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · have hh:=Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      (SingletonEnumeration.shiftKernel_range (radialWeight x X δ) (pencilLines x F) p k H H).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe] using hh
  · calc
      _ ≤ ∑ z : DistinctPairs F,((p:ℝ)*strength (pencilLines x F) (radialWeight x X δ) z)^k :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p:ℝ)^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
        simp only [mul_pow,Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

omit [FiniteDimensional K V] [Finite K] in

theorem certificate_pair_eq_power (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (R k : ℕ) :
    WeightedPrograms.pairMoment (B := Fin R) (pencilLines x F)
      (fun l => L*radialWeight x X δ l) k=
      ((R:ℝ)*(L:ℝ))^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
  unfold WeightedPrograms.pairMoment
  change _ = _ * ∑ z : (Σ h : F, {h' : F // h' ≠ h}), _
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H' _
  simp only [Fintype.card_fin,NNReal.coe_mul,←Finset.mul_sum,WeightedPrograms.strength]
  rw [←mul_assoc,mul_pow]

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_card {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀ z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑ z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ) ≤ M/t^k := by
  apply (le_div_iff₀ (pow_pos ht k)).mpr
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => t ≤ f z),t^k := by simp
    _ ≤ ∑ z∈Finset.univ.filter (fun z => t ≤ f z),f z^k := by
      apply Finset.sum_le_sum
      intro z hz
      exact pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hz).2 k
    _ ≤ ∑ z,f z^k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro z _ _; exact pow_nonneg (hf z) k)
    _ ≤ M := hM

end SharpRamseyFive.ScoreGeometry

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

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialOffException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in

lemma radial_lt_off_exception (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a L Q 1) (l : RadialLine x) :
    (radialWeight x (outsideAt x S (O x)) δ l:ℝ)< a := by
  by_contra hn
  have hw : a≤(δ:ℝ)*((RadialLine.trainingOnLine (outsideAt x S (O x)) l).card:ℝ) := by
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using le_of_not_gt hn
  have hl : l.val∈localLines S O δ a L x := by
    refine Finset.mem_filter.mpr ⟨hL l,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.property.2
    · change a≤(δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule≤ l.val).card:ℝ) at hw
      rwa [outsideAt_filter_card] at hw
  have hc : (1:ℝ)≤(localLines S O δ a L x).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨l.val,hl⟩
  exact hgood (Finset.mem_filter.mpr ⟨hx,hc⟩)

omit [FiniteDimensional K V] [Finite K] in

lemma strong_degree_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (t : ℝ) :
    Fintype.card {H' : F // AmbientEnumeration.overlapRelation (radialWeight x X δ)
      (pencilLines x F) t H H'} ≤
      1+(Finset.univ.filter fun H' : F => H≠H' ∧ t≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card := by
  rw [Fintype.card_subtype]
  apply le_trans (Finset.card_le_card (t := insert H (Finset.univ.filter fun H' : F => H≠H' ∧ t≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))) ?_) ?_
  · intro H' hH'
    by_cases he : H=H'
    · simpa only [he] using Finset.mem_insert_self H' _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,he,(Finset.mem_filter.mp hH').2.le⟩)
  · simpa only [add_comm] using Finset.card_insert_le H _

omit [FiniteDimensional K V] [Finite K] in

lemma strong_pairs_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (t : ℝ) :
    (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)≤
      F.card+(Finset.univ.filter fun p : DistinctPairs F =>
        t≤ strength (pencilLines x F) (radialWeight x X δ) p).card := by
  have he : (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)=
      ∑ H : F,∑ H' : F,if t< mass (radialWeight x X δ)
        (pencilLines x F H ∩ pencilLines x F H') then (1:ℝ) else 0 := by
    have hsigma {T : Type} [Fintype T] (R : T→T→Prop) :
        (Fintype.card ((h : T) × {h' : T // R h h'}) : ℝ)=
          ∑ h,∑ h',if R h h' then (1:ℝ) else 0 := by
      simp [Fintype.card_sigma,Fintype.card_subtype]
    exact hsigma (T := ↥F) (fun H H' => t < mass (radialWeight x X δ)
      (pencilLines x F H ∩ pencilLines x F H'))
  rw [he,SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · apply (Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      show (if t< mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H)
        then (1:ℝ) else 0)≤1 by split_ifs <;> norm_num)).trans_eq
    simp
  · calc
      _ ≤ ∑ p : DistinctPairs F,if t≤ strength (pencilLines x F) (radialWeight x X δ) p
          then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p _
        change (if t< strength (pencilLines x F) (radialWeight x X δ) p then (1:ℝ) else 0)≤_
        by_cases hp : t< strength (pencilLines x F) (radialWeight x X δ) p
        · simp [hp,hp.le]
        · simp only [hp,ite_false]; split_ifs <;> norm_num
      _ = _ := by simp

theorem ambient_degree_off_exception (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)≤2)
    (t A : ℝ) (ht : 0< t) (hA : 2≤ A)
    (hscale : 16*((Nat.card K:ℝ)+1)≤ A*t^2)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (t/2) L Q 1) (H : F) :
    (Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F) t H H'}:ℝ)≤ A := by
  let D : ℝ := (Finset.univ.filter fun H' : F => H≠H' ∧ t≤
    mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H ∩ pencilLines x F H')).card
  have hd := score_degree_truncated x hdim (outsideAt x S (O x)) δ hδ F hF H t ht.le
    (radial_lt_off_exception x S O δ (t/2) L hL Q hx hgood)
  have hsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
    calc
      _ ≤ (2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hm H) 2
      _ = 4 := by norm_num
  have hraw : D*t^2≤8*((Nat.card K:ℝ)+1) := hd.trans (by
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hD : D≤ A/2 := (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp (by nlinarith [hscale])
  have hcard : (Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F) t H H'}:ℝ)≤1+D := by
    dsimp only [D]
    exact_mod_cast strong_degree_le x (outsideAt x S (O x)) δ F H t
  linarith

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TrainingLineCard
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

omit [Fintype (RadialLine x)] in
lemma training_line_card (X : Finset {y : ℙ K V // x≠y}) (l : RadialLine x) :
    (RadialLine.trainingOnLine X l).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let f (y : RadialLine.trainingOnLine X l) : {p : ℙ K V // p.submodule ≤ l.val} :=
    ⟨y.val.val,(Finset.mem_filter.mp y.property).2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {p : ℙ K V // p.submodule ≤ l.val} => u.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [card_subspacePoints,l.property.1,Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  simpa [Finset.sum_range_succ,Nat.add_comm] using hc

theorem score_degree_uniform_normalized (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n a χ : ℝ) (hn : 0 < n) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hm : mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcap : n ≤ (Nat.card K:ℝ)^3) (hscale : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ)) :
    ((Finset.univ.filter fun H' : F => H≠H' ∧ a ≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K)
  by_cases hsmall : a ≤ 2*(δ:ℝ)*((Nat.card K:ℝ)+1)
  · apply ScoreScalars.normalized_degree_small (C := 16) (zero_lt_one.trans_le hq) hn ha ha2 hcap ?_ (by convert hchi using 1; norm_num)
      (ScoreScalars.degree_power_two_hundred hq (mass_nonneg _ _) hm ha
        (score_degree_four x hdim X δ hδ F hF H a ha))
    · calc
        n*a ≤ n*(2*(δ:ℝ)*((Nat.card K:ℝ)+1)) := mul_le_mul_of_nonneg_left hsmall hn.le
        _ = 2*(n*(δ:ℝ))*((Nat.card K:ℝ)+1) := by ring
        _ ≤ 2*(4*Nat.card K)*(2*Nat.card K) := mul_le_mul
          (mul_le_mul_of_nonneg_left hscale (by norm_num)) (by linarith) (by positivity) (by positivity)
        _ = 16*(Nat.card K:ℝ)^2 := by ring
  · apply ScoreScalars.normalized_degree_truncated hq hn ha ha2 hcap
        (le_trans (by norm_num) hchi)
    have hline (l : RadialLine x) : (radialWeight x X δ l:ℝ) < a/2 := by
      have hc := mul_le_mul_of_nonneg_left (show ((RadialLine.trainingOnLine X l).card:ℝ) ≤
        (Nat.card K:ℝ)+1 by exact_mod_cast training_line_card x X l) δ.coe_nonneg
      have hh : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*((Nat.card K:ℝ)+1) := by
        simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hc
      linarith
    have hd := score_degree_truncated x hdim X δ hδ F hF H a ha hline
    have hs : (mass (radialWeight x X δ) (pencilLines x F H))^2 ≤ 4 := by
      have h0 := mass_nonneg (radialWeight x X δ) (pencilLines x F H)
      nlinarith
    apply hd.trans
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem score_row_uniform_moment (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n χ : ℝ) (hn : 0 < n)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcap : n ≤ (Nat.card K:ℝ)^3) (hscale : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ)) :
    (∑ H',offRow x X δ F H H'^200) ≤
      2^200*(Nat.clog 2 X.card+1)*(((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) := by
  apply (moment_polynomial_tail _ (fun i : ℕ => (δ:ℝ)*2^i)
    (boundedOverlapDyads x X δ 2) 200 (by norm_num)
    (((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) (offRow_nonneg x X δ F H)
    (by intro i _; positivity) (offRow_bounded_cover x X δ hδ F hF 2 hm H) ?_).trans
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast boundedOverlapDyads_card x X δ 2) (by positivity)) (by positivity)
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have he : (Finset.univ.filter (fun H' : F => (δ:ℝ)*2^i ≤ offRow x X δ F H H'))=
      Finset.univ.filter (fun H' : F => H≠H' ∧ (δ:ℝ)*2^i ≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) := by
    apply Finset.filter_congr
    intro H' _
    by_cases h : H=H'
    · simp [offRow,h,not_le.mpr ha]
    · simp [offRow,h]
  rw [he]
  exact score_degree_uniform_normalized x hdim X δ hδ F hF H n _ χ hn ha.le
    (Finset.mem_filter.mp hi).2 (hm H) hcap hscale hchi

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma highCertificateMajorant_nonneg (Q M B b L : ℝ) (p R k N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hB : 0 ≤ B) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ highCertificateMajorant Q M B b L p R k N₂ := by
  unfold highCertificateMajorant
  positivity

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in

theorem score_high_certificate_majorant (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p R k N₂ : ℕ) (Q M B b : ℝ)
    (hB : 0 < B) (_hb : 0 ≤ b) (hQ : (F.card:ℝ) ≤ Q) (_hM : 0 ≤ M)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : F × Fin p => pencilLines x F z.1) (fun l => L*radialWeight x X δ l)
      B b (2*(L:ℝ)) k 0 (N₂*p) false) ≤
      highCertificateMajorant Q M B b L p R k N₂ := by
  have hmass (H : F) : (∑ l∈pencilLines x F H,((L*radialWeight x X δ l:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using hh
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg F.card).trans hQ
  have hpair := SingletonEnumeration.pairMoment_labelled_le (V := Fin p) (B := Fin R)
    (pencilLines x F) (fun l => L*radialWeight x X δ l) k (2*(L:ℝ)) (by positivity) hmass
  simp only [Fintype.card_fin,Fintype.card_coe] at hpair
  rw [certificate_pair_eq_power] at hpair
  have hpair' : pairMoment (B := Fin R) (fun z : F × Fin p => pencilLines x F z.1)
      (fun l => L*radialWeight x X δ l) k ≤
      (p:ℝ)^2*(((R:ℝ)*(L:ℝ))^k*M+Q*((R:ℝ)*(2*(L:ℝ)))^k) := by
    apply hpair.trans
    gcongr
  unfold highCertificateMajorant
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply add_le_add_right
  unfold branchingBound uniformAnchorBudget
  simp only [Bool.false_eq_true,ite_false,add_zero,Fintype.card_fin,Fintype.card_prod,Fintype.card_coe,
    Nat.cast_mul]
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma highMomentBudget_bounds (Q M A B b L : ℝ) (p R N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 < B)
    (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ highMomentBudget Q M A B b L p R N₂ ∧
    highCertificateMajorant Q M B b L p R 200 N₂ ≤ highMomentBudget Q M A B b L p R N₂ ∧
    1+(p:ℝ)^200*A ≤ highMomentBudget Q M A B b L p R N₂ ∧
    Q+(p:ℝ)^200*M ≤ (highMomentBudget Q M A B b L p R N₂)^2 := by
  have hc := highCertificateMajorant_nonneg Q M B b L p R 200 N₂ hQ hM hB.le hb hL
  have hrow : 0 ≤ 1+(p:ℝ)^200*A := by positivity
  have hx : 0 ≤ Q/B+(p:ℝ)^200*(M/B) := by positivity
  have hCB : B ≤ highMomentBudget Q M A B b L p R N₂ := by
    unfold highMomentBudget; linarith
  have hCx : Q/B+(p:ℝ)^200*(M/B) ≤ highMomentBudget Q M A B b L p R N₂ := by
    unfold highMomentBudget; linarith
  have hC := hB.le.trans hCB
  refine ⟨hC,?_,?_,?_⟩
  · unfold highMomentBudget; linarith
  · unfold highMomentBudget; linarith
  · calc
      _ = B*(Q/B+(p:ℝ)^200*(M/B)) := by field_simp
      _ ≤ highMomentBudget Q M A B b L p R N₂ *
          highMomentBudget Q M A B b L p R N₂ := mul_le_mul hCB hCx hx hC
      _ = _ := (sq _).symm

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem projective_high_moment_from_pairs (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ L : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ b base D₀ : ℝ) (hn : 0 < n) (hb : 1 ≤ b) (hD : 0 ≤ D₀)
    (hL : 10000 ≤ (L:ℝ)) (hbase : (23/25:ℝ) ≤ base)
    (hcap : n ≤ (Nat.card K:ℝ)^3)
    (hscaleDensity : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ))
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hlower : ∀ H : F,(3/4:ℝ) ≤ mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))
    (hdelta : ∀ H : F,|mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)-base| ≤ 17/100)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) δ) z^200) ≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) n)^2)
    {p : ℕ} (hp : 0 < p) (R h : ℕ) (hKR : 200 ≤ R/2) (hh : 0 < h)
    (hsize : h ≤ (R/2-5000)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1) < 1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑ H : F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (O x)) δ) (fun d => L*radialWeight x (outsideAt x S (O x)) δ d)
      (pencilLines x F) R 5000 base H) ≤ D₀)
    (hcost : D₀+2*((p+1:ℝ)*pencilHighBudget (Nat.card K) (outsideAt x S (O x)).card n χ b L p R) ≤
      geometryScale (Nat.card K) n*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hA : 2 ≤ geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1) ≤
      (geometryScale (Nat.card K) n*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S O δ ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) n)^2)/(1/(100*(p:ℝ)))^200 ≤
      (geometryScale (Nat.card K) n)^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ ω, HighMoment.allTrunc R 5000 ω*(∑ H : F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S (O x)) δ i.2)) ≤
      (geometryScale (Nat.card K) n)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let X := outsideAt x S (O x)
  let q := Nat.card K
  let B := geometryScale q n
  let M := dyadFactor X.card χ*B^2
  let A := dyadFactor X.card χ*B
  let C := pencilHighBudget q X.card n χ b L p R
  have hq : 0 < q := Nat.card_pos
  have hB : 0 < B := by dsimp [B,geometryScale]; positivity
  have hM : 0 ≤ M := by dsimp [M,dyadFactor]; positivity
  have hRow : 0 ≤ A := by dsimp [A,dyadFactor]; positivity
  have hQ : 0 ≤ (pencilAlphabet q 4:ℝ) := Nat.cast_nonneg _
  have hC := highMomentBudget_bounds (pencilAlphabet q 4) M A B b L p R
    (pencilAlphabet q 2) hQ hM hRow hB (zero_le_one.trans hb) L.coe_nonneg
  have hrows (H : F) : (∑ H',offRow x X δ F H H'^200) ≤ A := by
    simpa only [A,B,dyadFactor,geometryScale,mul_assoc,mul_left_comm,mul_comm] using
      score_row_uniform_moment x hdim X δ hδ F hF H n χ hn hm hcap hscaleDensity hchi
  have hQsize : (F.card:ℝ) ≤ (pencilAlphabet q 4:ℝ) := by
    exact_mod_cast (by simpa only [hdim,Nat.reduceSub,pencilAlphabet] using pencil_size x F hF)
  have hN₁ (d : RadialLine x) : (Finset.univ.filter fun H : F => d∈pencilLines x F H).card ≤ pencilAlphabet q 3 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using one_anchor_count x F d
  have hN₂ (d e : RadialLine x) (hde : d≠e) :
      (Finset.univ.filter fun H : F => d∈pencilLines x F H ∧ e∈pencilLines x F H).card ≤ pencilAlphabet q 2 := by
    simpa only [hdim,Nat.reduceSub,pencilAlphabet] using two_anchor_count x F d e hde
  have hmassL (H : F) : (∑ d∈pencilLines x F H,((L*radialWeight x X δ d:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have ht : 0 < 1/(100*(p:ℝ)) := by positivity
  let Δ := ⌊B*Real.exp (-((L:ℝ)*R))⌋₊
  have hΔ (H : F) : Fintype.card {H' : F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'} ≤ Δ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact ambient_degree_off_exception x hdim S O δ hδ F hF hm _ _ ht hA hscale Lines hLines Q hx hstrong H
  have hdeg : (Δ:ℝ) ≤ B*Real.exp (-((L:ℝ)*R)) := Nat.floor_le (by positivity)
  have hRelPairs : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ) ≤ B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    apply le_trans (add_le_add hQsize (power_tail_card _ (fun z => by unfold strength; positivity) 200 _ M ht hPow))
    exact hpairScalar
  apply AmbientEnumeration.ambient_refined_truncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 5000 h (pencilAlphabet q 3) (pencilAlphabet q 2) (by norm_num)
    hKR hh false hsize herr hN₁ hN₂ ?_ ?_ ?_ hDsum hcost hp2 Δ hΔ hdeg hRelPairs
  · exact (score_high_certificate_majorant x X δ L F p R 200 _ _ M B b hB (zero_le_one.trans hb) hQsize hM hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) A (hrows H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 M hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PencilLineSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

lemma pencil_line_sum_le (hdim : finrank K V=5)
    (F : Finset (ℙ K (Dual K V))) (f : RadialLine x→ℝ) (hf : ∀ d,0 ≤ f d) :
    (∑ H : F,∑ d∈pencilLines x F H,f d) ≤
      (pencilAlphabet (Nat.card K) 3:ℝ)*∑ d,f d := by
  have he : (∑ H : F,∑ d∈pencilLines x F H,f d) =
      ∑ d : RadialLine x,((Finset.univ.filter fun H : F => d∈pencilLines x F H).card:ℝ)*f d := by
    calc
      _ = ∑ H : F,∑ d : RadialLine x,if d∈pencilLines x F H then f d else 0 := by
        apply Finset.sum_congr rfl
        intro H _
        simp only [←Finset.sum_filter]
        congr 1
        ext d
        simp
      _ = ∑ d : RadialLine x,∑ H : F,if d∈pencilLines x F H then f d else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_right _ (hf d)
  exact Nat.cast_le.mpr (by simpa only [hdim,Nat.reduceSub,pencilAlphabet] using one_anchor_count x F d)

lemma independent_sum_le (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (base D A : ℝ) (R J : ℕ) (hR : 2 ≤ R/2)
    (hdev : ∀ H : F,|mass (radialWeight x X δ) (pencilLines x F H)-base| ≤ 1)
    (hvar : (∑ H : F,(mass (radialWeight x X δ) (pencilLines x F H)-base)^2) ≤ D)
    (hpow : (∑ d : RadialLine x,(radialWeight x X δ d:ℝ)^J) ≤ A)
    (hA : 0 ≤ A) :
    (∑ H : F,SingletonEnumeration.independentWeight (radialWeight x X δ)
      (fun d => L*radialWeight x X δ d) (pencilLines x F) R J base H) ≤
      D+(pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^J*A := by
  have hv : (∑ H : F,|mass (radialWeight x X δ) (pencilLines x F H)-base|^(R/2)) ≤ D := by
    apply le_trans (Finset.sum_le_sum fun H _ => ?_) hvar
    simpa only [sq_abs] using pow_le_pow_of_le_one (abs_nonneg _) (hdev H) hR
  simp only [SingletonEnumeration.independentWeight,Finset.sum_add_distrib]
  apply add_le_add hv
  by_cases hRJ : R < J
  · simp only [ite_eq_left hRJ,Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _)) hA
  · simp only [ite_eq_right hRJ]
    have he (d : RadialLine x) : ((R:ℝ)*((L*radialWeight x X δ d:ℝ≥0):ℝ))^J =
        ((R:ℝ)*(L:ℝ))^J*(radialWeight x X δ d:ℝ)^J := by
      simp only [NNReal.coe_mul,←mul_assoc,mul_pow]
    simp_rw [he]
    calc
      _ ≤ (pencilAlphabet (Nat.card K) 3:ℝ)*
          ∑ d : RadialLine x,((R:ℝ)*(L:ℝ))^J*(radialWeight x X δ d:ℝ)^J :=
        pencil_line_sum_le x hdim F _ (fun d => mul_nonneg
          (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _) (pow_nonneg (NNReal.coe_nonneg _) _))
      _ = (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^J*
          ∑ d : RadialLine x,(radialWeight x X δ d:ℝ)^J := by rw [←Finset.mul_sum,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

section
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma cellMass_mono {A B : Finset (ℙ K V)} (hAB : A ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) : cellMass A δ H ≤ cellMass B δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hAB))

lemma cellMass_union (A B : Finset (ℙ K V)) (δ : ℝ) (H : ℙ K (Dual K V)) :
    cellMass (A∪B) δ H = cellMass A δ H+cellMass B δ H-cellMass (A∩B) δ H := by
  have he := Finset.card_union_add_card_inter
    (A.filter fun y => Incident y H) (B.filter fun y => Incident y H)
  have he' : (((A∪B).filter fun y => Incident y H).card:ℝ)+
      ((A∩B).filter fun y => Incident y H).card =
        (A.filter fun y => Incident y H).card+(B.filter fun y => Incident y H).card := by
    rw [Finset.filter_union,Finset.filter_inter_distrib]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma filter_sdiff_eq {α : Type*} [DecidableEq α] (S O : Finset α)
    (p : α→Prop) [DecidablePred p] : (S\O).filter p = S.filter p\O.filter p := by
  ext y
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

lemma cellMass_sdiff {S O : Finset (ℙ K V)} (hOS : O ⊆ S) (δ : ℝ)
    (H : ℙ K (Dual K V)) : cellMass (S\O) δ H = cellMass S δ H-cellMass O δ H := by
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (fun y => Incident y H) hOS)
  have he' : (((S\O).filter fun y => Incident y H).card:ℝ)+
      (O.filter fun y => Incident y H).card = (S.filter fun y => Incident y H).card := by
    rw [filter_sdiff_eq]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma cellMass_erase (S : Finset (ℙ K V)) (x : ℙ K V) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) :
    0 ≤ cellMass S δ H-cellMass (S\{x}) δ H ∧
      cellMass S δ H-cellMass (S\{x}) δ H ≤ δ := by
  have hl := cellMass_mono (Finset.sdiff_subset : S\{x} ⊆ S) hδ H
  have hc : (S.filter fun y => Incident y H).card ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by
    rw [filter_sdiff_eq]
    have h := Finset.card_le_card_sdiff_add_card (s:=S.filter fun y => Incident y H)
      (t:=({x}:Finset (ℙ K V)).filter fun y => Incident y H)
    have h1 : (({x}:Finset (ℙ K V)).filter fun y => Incident y H).card ≤ 1 :=
      (Finset.card_filter_le ..).trans_eq (Finset.card_singleton x)
    omega
  have hc' : ((S.filter fun y => Incident y H).card:ℝ) ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by exact_mod_cast hc
  constructor
  · exact sub_nonneg.mpr hl
  · have hm := mul_le_mul_of_nonneg_left hc' hδ
    unfold cellMass
    nlinarith only [hm]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma typical_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (j : Option J) : |deviation S C j H| ≤ threshold j := by
  by_contra hn
  exact hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,lt_of_not_ge hn⟩)

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma queryLoss_bounds (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) :
    0 ≤ queryLoss S O x H ∧ queryLoss S O x H ≤ (Nat.card K:ℝ)/S.card := by
  have h := cellMass_erase (S\O) x (show 0 ≤ (Nat.card K:ℝ)/S.card by positivity) H
  have he : (S\O)\{x}=S\(O∪{x}) := by
    ext y
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  simpa only [queryLoss,outsideMass,he] using h

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma outsideMass_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) (H : ℙ K (Dual K V)) :
    outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b)) =
      deviation S C none H-deviation S C (some a) H-deviation S C (some b) H+
        deviation S C (some c) H-queryLoss S (C a∪C b) x H := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
  have hmass := cellMass_sdiff (Finset.union_subset ha hb) ((Nat.card K:ℝ)/S.card) H
  rw [cellMass_union] at hmass
  have hcard : ((C a∪C b).card:ℝ)+((C a∩C b).card:ℝ)=(C a).card+(C b).card := by
    exact_mod_cast Finset.card_union_add_card_inter (C a) (C b)
  simp only [deviation,familyCell,queryLoss,ownFraction,div_self hn,hc]
  rw [hmass]
  have hs := congrArg (fun z : ℝ => z/(S.card:ℝ)) hcard
  simp only [add_div] at hs
  linarith only [hs]

omit [Finite K] in

theorem typical_mass_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (hf : ownFraction S (C a) (C b) ≤ 2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1/100) :
    3/4 ≤ outsideMass S (C a∪C b) x H ∧
    |outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b))| ≤ 17/100 ∧
    outsideMass S (C a∪C b) x H ≤ 11/10 := by
  have h0 := typical_deviation S C hH none
  have h1 := typical_deviation S C hH (some a)
  have h2 := typical_deviation S C hH (some b)
  have h3 := typical_deviation S C hH (some c)
  simp only [threshold,abs_le] at h0 h1 h2 h3
  have hl := queryLoss_bounds S (C a∪C b) x H
  have he := outsideMass_deviation S C hS a b c ha hb hc x H
  have hmass : outsideMass S (C a∪C b) x H ≤ cellMass S ((Nat.card K:ℝ)/S.card) H :=
    cellMass_mono Finset.sdiff_subset (by positivity) H
  have hbase : deviation S C none H=cellMass S ((Nat.card K:ℝ)/S.card) H-1 := by
    simp only [deviation,familyCell,div_self (show (S.card:ℝ)≠0 by exact_mod_cast hS.card_pos.ne')]
  rw [hbase] at h0
  refine ⟨?_,⟨?_,?_⟩⟩
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith

end

open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma typical_variance_component {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C) {ξ : ℝ}
    (hx : x∉irregular (d:=d) S C ξ) (j : Option J) :
    (∑ H : F,(deviation S C j H.val)^2) ≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hr : weightOnPencil (clippedWeight S C (some j)) x ≤ scale (K:=K) d S.card*Real.exp ξ := by
    by_contra hn
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,some j,lt_of_not_ge hn⟩)
  have he : (∑ H : F,(deviation S C j H.val)^2)=
      ∑ H∈F,incidenceEntry x H*clippedWeight S C (some j) H := by
    rw [Finset.sum_coe_sort F (fun H => (deviation S C j H)^2)]
    apply Finset.sum_congr rfl
    intro H hH
    have hd := typical_deviation S C (hF H hH).2 j
    have ht : threshold j ≤ 1 := by cases j <;> norm_num [threshold]
    have hs : (deviation S C j H)^2 ≤ 1 := by
      have ha := abs_nonneg (deviation S C j H)
      have hb := hd.trans ht
      nlinarith [sq_abs (deviation S C j H)]
    simp only [incidenceEntry,ite_eq_left (hF H hH).1,clippedWeight,min_eq_right hs,one_mul]
  rw [he]
  apply le_trans _ hr
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro H _ _
  have hw := (clippedWeight_bounds S C (some j) H).1
  by_cases h : Incident x H <;> simp [incidenceEntry,h,hw]

lemma Q_le_two_pow (q k : ℕ) (hq : 2≤q) : (Q q k:ℝ) ≤ 2*(q:ℝ)^k-1 := by
  induction k with
  | zero => norm_num [Q]
  | succ k ih =>
    have he : (Q q (k+1):ℝ)=(Q q k:ℝ)+(q:ℝ)^(k+1) := by
      unfold Q
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_pow]
    rw [he,pow_succ]
    have hq' : (2:ℝ)≤q := by exact_mod_cast hq
    have hp := pow_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) k
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

omit [Fintype (ℙ K V)] in
lemma typical_pencil_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H) : (F.card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-1) := by
  have hf : F ⊆ Finset.univ.filter (Incident x) := fun H hH =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF H hH⟩
  have he : (Finset.univ.filter (Incident x)).card=Q (Nat.card K) (d-1) := by
    rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card,card_hyperplanes_through_point,hdim]
    unfold Q
    congr 1
    congr 1
    omega
  have hc : (F.card:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast (Finset.card_le_card hf).trans_eq he
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  linarith [Q_le_two_pow (Nat.card K) (d-1) hq]

omit [Fintype (ℙ K V)] in
lemma queryLoss_square_sum {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (S O : Finset (ℙ K V)) (hS : S.Nonempty) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(queryLoss S O x H.val)^2) ≤ 2*scale (K:=K) d S.card := by
  have hn0 : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hδ : 0≤(Nat.card K:ℝ)/S.card := by positivity
  have hc := typical_pencil_card hdim hd x F hF
  have he : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  calc
    _ ≤ ∑ H : F,((Nat.card K:ℝ)/S.card)^2 := by
      apply Finset.sum_le_sum
      intro H _
      exact pow_le_pow_left₀ (queryLoss_bounds S O x H.val).1 (queryLoss_bounds S O x H.val).2 2
    _ = (F.card:ℝ)*((Nat.card K:ℝ)/S.card)^2 := by simp
    _ ≤ (2*(Nat.card K:ℝ)^(d-1))*((Nat.card K:ℝ)/S.card)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2*scale (K:=K) d S.card*((Nat.card K:ℝ)/S.card) := by
      unfold scale
      rw [←he]
      ring
    _ ≤ 2*scale (K:=K) d S.card := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (scale_nonneg _ _ hn0.le))

lemma four_sq (a b c d : ℝ) : (a-b-c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b),sq_nonneg (c+d),sq_nonneg ((a-b)+(c-d))]

theorem typical_mass_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      40*scale (K:=K) d S.card*Real.exp ξ := by
  have hv (j : Option J) := typical_variance_component S C x F hF hx j
  have hl := queryLoss_square_sum hdim hd S (C a∪C b) hS x F (fun H hH => (hF H hH).1) hn
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  have he : 1≤Real.exp ξ := Real.one_le_exp_iff.mpr hξ
  have hs : (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      8*((∑ H : F,(deviation S C none H.val)^2)+
        (∑ H : F,(deviation S C (some a) H.val)^2)+
        (∑ H : F,(deviation S C (some b) H.val)^2)+
        (∑ H : F,(deviation S C (some c) H.val)^2))+
      2*∑ H : F,(queryLoss S (C a∪C b) x H.val)^2 := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    rw [outsideMass_deviation S C hS a b c ha hb hc x H.val]
    have h4 := four_sq (deviation S C none H.val) (deviation S C (some a) H.val)
      (deviation S C (some b) H.val) (deviation S C (some c) H.val)
    nlinarith [sq_nonneg (deviation S C none H.val-deviation S C (some a) H.val-
      deviation S C (some b) H.val+deviation S C (some c) H.val+
      queryLoss S (C a∪C b) x H.val)]
  have hb' := mul_le_mul_of_nonneg_left he hB
  nlinarith only [hs,hv none,hv (some a),hv (some b),hv (some c),hl,hb',hB]

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PointStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma coe_pointStrength (S : Finset (ℙ K V)) :
    (pointStrength (K:=K) S:ℝ)=(Nat.card K:ℝ)/S.card := by
  simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_outside_pencil (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) :
    mass (radialWeight x (outsideAt x S O) (pointStrength S)) (pencilLines x F H) =
      outsideMass S O x H.val := by
  rw [mass_pencil x (outsideAt x S O) (pointStrength S) F hF H]
  change _*(((outsideAt x S O).filter fun y => y.val.submodule≤LinearMap.ker H.val.rep).card:ℝ)=_
  rw [outsideAt_filter_card,coe_pointStrength]
  rfl

omit [Finite K] [Fintype (ℙ K V)] in
theorem actual_radial_mass_bounds {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100) (H : F) :
    3/4 ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) ∧
    |mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)-
      (1-ownFraction S (C a) (C b))|≤17/100 ∧
    mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)≤11/10 := by
  rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1)]
  exact typical_mass_bounds S C hS a b c ha hb hc x (hF H.val H.property).2 hf hn

theorem actual_radial_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤1) :
    (∑ H : F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^2)≤
        40*scale (K:=K) d S.card*Real.exp ξ := by
  simp_rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1),sq_abs]
  exact typical_mass_variance hdim hd S C hS a b c ha hb hc x F hF hξ hx hn

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveHighCapturedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

lemma radial_tail_off_exception (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a D : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀ l : RadialLine x,l.val∈Lines) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q D) :
    ((Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)).card:ℝ) < D := by
  let A := Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)
  let E := localLines S O δ a Lines x
  let f (l : A) : E := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hLines l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      change a ≤ (δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule ≤ l.val.val).card:ℝ) at hr
      rwa [outsideAt_filter_card] at hr⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : E => z.val) he))
  have hc : A.card ≤ E.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi
  have he : (E.card:ℝ) < D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  exact lt_of_le_of_lt (by exact_mod_cast hc) he

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma radial_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (M : ℝ) (hmax : ∀ l : RadialLine x,(radialWeight x X δ l:ℝ) ≤ M)
    (l : RadialLine x) (hp : 0 < (radialWeight x X δ l:ℝ)) :
    ∃ i∈boundedOverlapDyads x X δ M,
      (δ:ℝ)*2^i ≤ (radialWeight x X δ l:ℝ) ∧
      (radialWeight x X δ l:ℝ) ≤ 2*((δ:ℝ)*2^i) := by
  have hc : 0 < (RadialLine.trainingOnLine X l).card := by
    by_contra hn
    have hz : (RadialLine.trainingOnLine X l).card=0 := by omega
    simp [radialWeight,hz] at hp
  have hfloor : (δ:ℝ) ≤ (radialWeight x X δ l:ℝ) := by
    have hh : (1:ℝ) ≤ (RadialLine.trainingOnLine X l).card := by exact_mod_cast hc
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast,mul_one] using
      mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hbound : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*2^Nat.clog 2 X.card := by
    have hh : (RadialLine.trainingOnLine X l).card ≤ 2^Nat.clog 2 X.card :=
      (Finset.card_filter_le _ _).trans (Nat.le_pow_clog (by norm_num) X.card)
    change (δ:ℝ)*((RadialLine.trainingOnLine X l).card:ℝ) ≤ (δ:ℝ)*(2:ℝ)^Nat.clog 2 X.card
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) δ.coe_nonneg
  obtain ⟨i,hi,hlo,hhi⟩ := dyadic_cover δ _ δ.coe_nonneg hfloor _ hbound
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (hmax l)⟩,hlo,hhi⟩

theorem radial_high_moment (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0 < δ) (n χ : ℝ) (hn : 0 < n)
    (hmax : (δ:ℝ)*((Nat.card K:ℝ)+1) ≤ 2)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (J : ℕ) (hJ : 100 ≤ J) :
    (∑ l : RadialLine x,(radialWeight x (outsideAt x S (O x)) δ l:ℝ)^J) ≤
      ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-100)*
        (2^200*(Nat.clog 2 (outsideAt x S (O x)).card+1)*((Nat.card K:ℝ)^4/n^2*Real.exp χ)) := by
  let X := outsideAt x S (O x)
  let A := (Nat.card K:ℝ)^4/n^2*Real.exp χ
  have hm (l : RadialLine x) : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*((Nat.card K:ℝ)+1) := by
    have hh : ((RadialLine.trainingOnLine X l).card:ℝ) ≤ (Nat.card K:ℝ)+1 := by
      exact_mod_cast training_line_card x X l
    exact mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hpoly : (∑ l : RadialLine x,(radialWeight x X δ l:ℝ)^100) ≤
      2^200*(Nat.clog 2 X.card+1)*A := by
    have hh := moment_polynomial_tail (fun l : RadialLine x => (radialWeight x X δ l:ℝ))
      (fun i : ℕ => (δ:ℝ)*2^i) (boundedOverlapDyads x X δ 2) 100 (by norm_num) (2^100*A)
      (fun l => NNReal.coe_nonneg _) (by intro i _; positivity)
      (radial_bounded_cover x X δ 2 (fun l => (hm l).trans hmax)) ?_
    · apply hh.trans
      have hc : ((boundedOverlapDyads x X δ 2).card:ℝ) ≤ Nat.clog 2 X.card+1 := by
        exact_mod_cast boundedOverlapDyads_card x X δ 2
      have hA : 0 ≤ A := by dsimp [A]; positivity
      calc
        _ ≤ (2:ℝ)^100*(Nat.clog 2 X.card+1)*(2^100*A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num) 100)) (mul_nonneg (pow_nonneg (by norm_num) 100) hA)
        _ = _ := by ring
    · intro i hi
      let a : ℝ := (δ:ℝ)*2^i
      have ha : 0 < a := by dsimp [a]; positivity
      have ht := radial_tail_off_exception x S O δ (a/2) (A/(a/2)^100) Lines hLines Q hx (hgood i hi)
      have hcard : ((Finset.univ.filter fun l : RadialLine x => a ≤ (radialWeight x X δ l:ℝ)).card:ℝ) ≤
          ((Finset.univ.filter fun l : RadialLine x => a/2 ≤ (radialWeight x X δ l:ℝ)).card:ℝ) := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(by linarith : a/2 ≤ a).trans (Finset.mem_filter.mp hl).2⟩
      calc
        _ ≤ (A/(a/2)^100)*a^100 := mul_le_mul_of_nonneg_right (hcard.trans ht.le) (pow_nonneg ha.le _)
        _ = 2^100*A := by field_simp
  exact pow_sum_from_lower _ _ _ 100 J (by positivity) hJ (fun l => NNReal.coe_nonneg _) hm hpoly

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_High
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open ProjectiveTraining GlobalRadial WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_high_independent {J : Type} [Fintype J]
    (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (R : ℕ) (hR : 2≤R/2)
    (hx : x∉irregular (d:=4) S C ((L:ℝ)/100))
    (χ : ℝ) (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
      x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((((pointStrength S:ℝ)*2^i)/2)) Lines Q
        ((Nat.card K:ℝ)^4/S.card^2*Real.exp χ/(((pointStrength S:ℝ)*2^i)/2)^100)) :
    (∑H:F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (fun e => L*radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) e)
      (pencilLines x F) R 5000 (1-ownFraction S (C a) (C b)) H)≤
      40*scale (K:=K) 4 S.card*Real.exp ((L:ℝ)/100)+
      (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
        (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
            ((Nat.card K:ℝ)^4/S.card^2*Real.exp χ))) := by
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim (by norm_num) S C hS a b c ha hb hc F hF
    (by positivity : 0≤(L:ℝ)/100) hx (hn.trans (by norm_num))
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hpow := radial_high_moment x S (fun _ => C a∪C b) (pointStrength S) hδ S.card χ
    (Nat.cast_pos.mpr hS.card_pos) hmax Lines hLines Q hxQ hgood 5000 (by norm_num)
  exact independent_sum_le x hdim _ _ L F _ _ _ R 5000 hR
    (fun H => (hm H).2.1.trans (by norm_num)) (by simpa only [sq_abs] using hv)
    hpow ((Finset.sum_nonneg fun _ _ => pow_nonneg (NNReal.coe_nonneg _) _).trans hpow)

theorem actual_high_radial_moment_oai {J : Type} [Fintype J]
    (hdim : finrank K V=5) (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p)
    (hKR : 200≤R/2) (hh : 0<h) (hsize : h≤(R/2-5000)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=4) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
    (hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hchi : (208*2^198:ℝ)≤Real.exp (2*(((L:ℝ)*R)/100)))
    (hmax : (pointStrength S:ℝ)*((Nat.card K:ℝ)+1)≤2)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hgood : ∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
      x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
        (((pointStrength S:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100)/
          (((pointStrength S:ℝ)*2^i)/2)^100))
    (hPow : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)
    (hlocal : (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^5000*
        (((pointStrength S:ℝ)*((Nat.card K:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 (outsideAt x S (C a∪C b)).card:ℝ)+1)*
            ((Nat.card K:ℝ)^4/S.card^2*Real.exp (((L:ℝ)*R)/100))))≤
      geometryScale (Nat.card K) S.card)
    (hcost : (40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
      geometryScale (Nat.card K) S.card)+2*((p+1:ℝ)*
        pencilHighBudget (Nat.card K) (outsideAt x S (C a∪C b)).card S.card
          (((L:ℝ)*R)/100) cut L p R)≤
      geometryScale (Nat.card K) S.card*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hA : 2≤geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))
    (hscale : 16*((Nat.card K:ℝ)+1)≤
      (geometryScale (Nat.card K) S.card*Real.exp (-((L:ℝ)*R)))*(1/(100*(p:ℝ)))^2)
    (hstrong : x∉badCenters S (fun _ => C a∪C b) (pointStrength S)
      ((1/(100*(p:ℝ)))/2) Lines Q 1)
    (hpairScalar : (pencilAlphabet (Nat.card K) 4:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (geometryScale (Nat.card K) S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (geometryScale (Nat.card K) S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (own : F→Fin R→Bool) :
    (∫ω,HighMoment.allTrunc R 5000 ω*(∑H:F,scoreTerm (pencilLines x F H)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*
        radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
      (geometryScale (Nat.card K) S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hD := actual_high_independent x hdim S C hS a b c ha hb hc F hF hf hn L R
    (by omega) hx (((L:ℝ)*R)/100) hmax Lines hLines Q hxQ hgood
  have hD' : (∑H:F,SingletonEnumeration.independentWeight
      (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (fun e => L*radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) e)
      (pencilLines x F) R 5000 (1-ownFraction S (C a) (C b)) H)≤
      40*geometryScale (Nat.card K) S.card*Real.exp ((L:ℝ)/100)+
      geometryScale (Nat.card K) S.card := by
    exact hD.trans (add_le_add (by simp [scale,geometryScale]) hlocal)
  apply projective_high_moment_from_pairs x hdim S (fun _ => C a∪C b)
    (pointStrength S) L hδ F (fun H hH => (hF H hH).1) S.card (((L:ℝ)*R)/100)
    cut (1-ownFraction S (C a) (C b)) _ (Nat.cast_pos.mpr hS.card_pos) hcut
    (by unfold geometryScale;positivity) hL (by linarith only [hf]) hcap ?_ hchi
    (fun H => (hm H).2.2.trans (by norm_num)) (fun H => (hm H).1)
    (fun H => (hm H).2.1) Lines hLines Q hxQ hPow hp R h hKR hh hsize herr
    own hD' hcost hp2 hA hscale hstrong hpairScalar
  rw [coe_pointStrength,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hS.card_pos))]
  nlinarith only [Nat.cast_nonneg (α:=ℝ) (Nat.card K)]

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment_oai := @OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment_oai
