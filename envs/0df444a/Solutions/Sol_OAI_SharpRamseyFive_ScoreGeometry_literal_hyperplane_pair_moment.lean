-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:25:24.353705+00:00
-- url     : https://prove2.me/submissions/a2f2263f-e94c-4984-98bf-da022845a20d

import Mathlib
import Definitions.Def_OAIQ060R003

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma prefix_length_bound (k threshold : ℕ)
    (hlarge : ∀ j < k, threshold ≤ (cell F hF shape X j).card) :
    k*threshold ≤ X.card := by
  have hs := Finset.sum_le_sum (s := Finset.range k) (fun j hj => hlarge j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hh := sum_card_add_remaining F hF shape X k
  omega

lemma before_head (J cap : ℕ) {j : ℕ} (hj : j < headIndex F hF shape X J cap) :
    cap < (cell F hF shape X j).card := by
  have hn := Nat.find_min (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩) hj
  exact lt_of_not_ge (fun hh => hn (Or.inr hh))

lemma head_length_bound (J cap : ℕ) : headIndex F hF shape X J cap * cap ≤ X.card :=
  prefix_length_bound F hF shape X _ _ (fun _ hj => (before_head F hF shape X J cap hj).le)

end SharpRamseyFive.GreedyTraining

end OAI
end

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

lemma card_filter_containment_le (X : Finset (ℙ K V)) (A : Submodule K V) :
    (X.filter fun x => x.submodule ≤ A).card ≤ ∑ i ∈ Finset.range (finrank K A), Nat.card K^i := by
  let : Finite V := Module.finite_of_finite K
  let Y := X.filter fun x => x.submodule ≤ A
  have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
      {p : ℙ K V // p.submodule ≤ A})) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints] at hc
  exact hc

lemma card_filter_finrank_le_two (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 2) :
    (X.filter fun x => x.submodule ≤ A).card ≤ Nat.card K+1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa [Finset.sum_range_succ,add_comm] using hc

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

lemma plane_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 3) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ Nat.card K+1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_two X (A ⊓ H) (by omega)

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
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighParameters
open scoped BigOperators

lemma threshold_bounds {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a) (ha2 : a≤2)
    (hhigh : 2097152*q^2≤n*a^2) :
    n*a/(128*q) ≤ (threshold q n a:ℝ) ∧
    (threshold q n a:ℝ) ≤ n*a/(64*q) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hna : 1048576*q^2≤n*a := by
    have haa : a^2≤2*a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left haa hn.le]
  have hx : 2≤n*a/(64*q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q-1)]
  have hf := Nat.lt_floor_add_one (n*a/(64*q))
  have hfloor : n*a/(128*q)≤(threshold q n a:ℝ) := by
    dsimp [threshold]
    have he : n*a/(128*q)=(n*a/(64*q))/2 := by ring
    rw [he]
    linarith
  exact ⟨hfloor,Nat.floor_le (by positivity)⟩

lemma cap_bounds {q a : ℝ} (hq : 1≤q) (ha : 0<a) (ha2 : a≤2) :
    1024*q^2/a ≤ (cap q a:ℝ) ∧ (cap q a:ℝ) ≤ 2048*q^2/a := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hb : 1≤1024*q^2/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [sq_nonneg (q-1)]
  refine ⟨Nat.le_ceil _,?_⟩
  have hc := Nat.ceil_lt_add_one (show 0≤1024*q^2/a by positivity)
  have he : 2048*q^2/a=2*(1024*q^2/a) := by ring
  rw [he]
  dsimp [cap,multiplicity]
  linarith

lemma head_length_condition {q n a j : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (hj : 0≤j)
    (hjn : j*(cap q a:ℝ)≤n) : j*(q+1)≤(threshold q n a:ℝ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hM := (threshold_bounds hq hn ha ha2 hhigh).1
  have hc := (cap_bounds hq ha ha2).1
  have hjn' : j*(1024*q^2/a)≤n := (mul_le_mul_of_nonneg_left hc hj).trans hjn
  calc
    _ ≤ j*(2*q) := mul_le_mul_of_nonneg_left (by linarith) hj
    _ = (j*(1024*q^2/a))*(a/(512*q)) := by field_simp; ring
    _ ≤ n*(a/(512*q)) := mul_le_mul_of_nonneg_right hjn' (by positivity)
    _ ≤ n*a/(128*q) := by
      have he : n*(a/(512*q))=(n*a/(128*q))/4 := by ring
      rw [he]
      have : 0≤n*a/(128*q) := by positivity
      linarith
    _ ≤ _ := hM

end SharpRamseyFive.HighParameters

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

end SharpRamseyFive.GreedyTraining

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

lemma plane_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 3) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card*(Nat.card K+1) := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (Nat.card K+1) :=
    Finset.sum_le_sum (fun i hi => plane_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma captured_cover (J : ℕ) (x : ℙ K V)
    (hx : x ∈ X \ remaining F hF (fun i => flatPoints (P i)) X J) :
    ∃ j ∈ Finset.range J, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  rw [remaining_eq_sdiff_union] at hx
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxX := (Finset.mem_sdiff.mp hx).1
  have hm : x ∈ (Finset.range J).biUnion (fun j => flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X j))) := by
    by_contra hn
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxX,hn⟩)
  obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hm
  exact ⟨j,hj,(mem_flatPoints _ _).mp hxj⟩

lemma head_plane_points (J cap : ℕ) (A : Submodule K V) (hA : finrank K A = 3)
    (hn : ∀ j < headIndex F hF (fun i => flatPoints (P i)) X J cap,
      ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) :
    ((X \ remaining F hF (fun i => flatPoints (P i)) X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap)).filter
      fun x => x.submodule ≤ A).card ≤
        headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) := by
  have hh := plane_covered_cap (Finset.range (headIndex F hF (fun i => flatPoints (P i)) X J cap))
    (fun j => P (chosen F hF (fun i => flatPoints (P i)) X j))
    (X \ remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap)) A hA
    (fun j hj => hn j (Finset.mem_range.mp hj))
    (fun x hx _ => captured_cover F hF P X _ x hx)
  simpa only [Finset.card_range] using hh

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma rich_planes_split (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (x : ℙ K V)
    (hx : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c) :
    richAt F hF P X L J M x ⊆ headAt F hF P X L J cap M c x ∪
      (tailPlanes F hF P X L J cap M).filter (fun A => x.submodule ≤ A) := by
  intro A hA
  obtain ⟨hAL,hxA,hAr⟩ := Finset.mem_filter.mp hA
  by_cases hc : ∃ j < headIndex F hF (fun i => flatPoints (P i)) X J cap,
      A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hAL,Finset.mem_filter.mpr ⟨(mem_flatPoints A x).mpr hxA,hc,?_,hx⟩⟩
    apply hAr.trans
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy
    obtain ⟨hy,hyn⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,hyn⟩
  · have hhead := head_plane_points F hF P X J cap A (hL A hAL) (by
      intro j hj hAj
      exact hc ⟨j,hj,hAj⟩)
    have hsub : (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A) ⊆
        ((X \ remaining F hF (fun i => flatPoints (P i)) X
          (headIndex F hF (fun i => flatPoints (P i)) X J cap)).filter fun y => y.submodule ≤ A) ∪
        ((tail F hF P X J cap).filter fun y => y.submodule ≤ A) := by
      intro y hy
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,tail] at *
      tauto
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hAL,by omega⟩,hxA⟩

theorem rich_count_outside_exceptions
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (D₁ D₂ : ℕ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxL : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c)
    (hxH : x ∉ Y.filter fun x => D₁ ≤ (headAt F hF P X L J cap M c x).card)
    (hxT : x ∉ Y.filter fun x => D₂ ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card) :
    (richAt F hF P X L J M x).card < D₁+D₂ := by
  have hcard := (Finset.card_le_card (rich_planes_split F hF P X L hL J cap M hHM c x hxL)).trans
    (Finset.card_union_le _ _)
  have hh : (headAt F hF P X L J cap M c x).card < D₁ := by
    by_contra hn
    exact hxH (Finset.mem_filter.mpr ⟨hxY,by omega⟩)
  have ht : ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card < D₂ := by
    by_contra hn
    exact hxT (Finset.mem_filter.mpr ⟨hxY,by omega⟩)
  omega

end

open Module GreedyTraining ProjectiveTraining RichPlaneGeometry HyperplaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

theorem captured_pair_count (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J M : ℕ) (x : ℙ K V) (hxG : ∀ A ∈ G,x.submodule ≤ A) :
    (capturedPairs F hF P X G J M x).card ≤
      (richAt F hF P X L J M x).card*(Nat.card K+1)^2 := by
  have hh := pair_count_by_intersection (d := 4) hdim G hG
    (richAt F hF P X L J M x) 3 (fun A hA => hL A (Finset.mem_filter.mp hA).1)
    (capturedPairs F hF P X G J M x) (Finset.filter_subset _ _) (by
      intro p hp
      obtain ⟨hp,hne,hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hcomplete _ (hyperplane_intersection_rank (d := 4) hdim p.1 p.2
        (hG _ h1) (hG _ h2) hne),le_inf (hxG _ h1) (hxG _ h2),hpc⟩)
  have he : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ,Nat.add_comm]
  simpa only [he] using hh

theorem captured_pairs_outside_exceptions (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (D₁ D₂ : ℕ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxG : ∀ A ∈ G,x.submodule ≤ A)
    (hxL : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c)
    (hxH : x ∉ Y.filter fun x => D₁ ≤ (headAt F hF P X L J cap M c x).card)
    (hxT : x ∉ Y.filter fun x => D₂ ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card) :
    (capturedPairs F hF P X G J M x).card ≤ (D₁+D₂)*(Nat.card K+1)^2 := by
  exact (captured_pair_count F hF P X hdim G hG L hL hcomplete J M x hxG).trans
    (Nat.mul_le_mul_right _ (rich_count_outside_exceptions F hF P X L hL J cap M hHM c D₁ D₂
      Y x hxY hxL hxH hxT).le)

end SharpRamseyFive.HighPlaneBudget

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

theorem high_pairs (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J : ℕ) (a χ : ℝ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxG : ∀ A ∈ G,x.submodule ≤ A)
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2)
    (hx : x ∉ highExceptions F hF P X L J a χ Y) :
    (capturedPairs F hF P X G J (threshold (Nat.card K) X.card a) x).card ≤
      2*degree (Nat.card K) X.card a χ*(Nat.card K+1)^2 := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : (0:ℝ)<X.card := by exact_mod_cast hn
  have hHC : ((headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)):ℝ)*
      HighParameters.cap (Nat.card K) a ≤ X.card := by
    exact_mod_cast head_length_bound F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)
  have hHM := head_length_condition hq hn' ha ha2 hhigh
    (Nat.cast_nonneg (headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a))) hHC
  have hHM' : headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)*
      (Nat.card K+1) ≤ threshold (Nat.card K) X.card a := by exact_mod_cast hHM
  simp only [highExceptions,Finset.mem_union,not_or] at hx
  have hh := captured_pairs_outside_exceptions F hF P X hdim G hG L hL hcomplete J
    (HighParameters.cap (Nat.card K) a) (threshold (Nat.card K) X.card a) hHM'
    (X.card*a/1024) (degree (Nat.card K) X.card a χ) (degree (Nat.card K) X.card a χ)
    Y x hxY hxG hx.1.1 hx.1.2 hx.2
  simpa only [two_mul] using hh

end

open Module RichPlaneGeometry HighParameters HyperplaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem residual_pairs (hdim : finrank K V=5)
    (G : Finset (Submodule K V)) (hG : ∀ A∈G,finrank K A=4)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (X Y : Finset (ℙ K V)) (a χ : ℝ) (x : ℙ K V) (hxY : x∈Y)
    (hxG : ∀ A∈G,x.submodule≤A) (hx : x∉residualExceptions L X Y a χ) :
    (residualPairs G X (threshold (Nat.card K) X.card a)).card≤
      degree (Nat.card K) X.card a χ*(Nat.card K+1)^2 := by
  let M := threshold (Nat.card K) X.card a
  let R := (residualPlanes L X M).filter fun A => x.submodule≤A
  have hh := pair_count_by_intersection (d := 4) hdim G hG R 3
    (fun A hA => hL A (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1)
    (residualPairs G X M) (Finset.filter_subset _ _) (by
      intro p hp
      obtain ⟨hp,hne,hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hcomplete _ (hyperplane_intersection_rank (d := 4) hdim
        p.1 p.2 (hG _ h1) (hG _ h2) hne),hpc⟩,le_inf (hxG _ h1) (hxG _ h2)⟩)
  have hc : R.card < degree (Nat.card K) X.card a χ := by
    apply Nat.lt_of_not_ge
    intro he
    exact hx (Finset.mem_filter.mpr ⟨hxY,he⟩)
  have he : (∑ i∈Finset.range (4+1-3),Nat.card K^i)=Nat.card K+1 := by
    norm_num [Finset.sum_range_succ,Nat.add_comm]
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hc.le)
end SharpRamseyFive.HighPlaneBudget

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

end SharpRamseyFive.ScoreScalars

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

theorem normalized_pair_small {q n a χ E : ℝ} (hn : 0<n) (ha : 0≤a)
    (hsmall : n*a^99 ≤ q^2) (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (hpower : E*a^200 ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198) :
    E*a^200 ≤ (q^4/n)^2*Real.exp (2*χ) := by
  have hs : n^2*a^198 ≤ q^4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hn.le (pow_nonneg ha 99)) hsmall 2
    simpa only [mul_pow, ← pow_mul] using hh
  have hB : q^4*a^198 ≤ (q^4/n)^2 := by
    simpa only [mul_one] using scale_against_B hn (s := 1) (by simpa using hs)
  have h1 : 1 ≤ Real.exp χ := by linarith
  have hB' : q^4*a^198 ≤ (q^4/n)^2*Real.exp χ :=
    hB.trans (le_mul_of_one_le_right (sq_nonneg _) h1)
  have hsum : 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 ≤
      11*2^200*(q^4/n)^2*Real.exp χ := by
    have hh := mul_le_mul_of_nonneg_left hB' (by norm_num : (0:ℝ)≤8)
    have hc : (8:ℝ) ≤ 2*2^200 := by norm_num
    have ht := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (q^4/n)^2*Real.exp χ)
    nlinarith
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

theorem score_pair_small_normalized (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K) (hsmall : n*a^99 ≤ (Nat.card K:ℝ)^2)
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
  apply ScoreScalars.normalized_pair_small hn ha.le hsmall hchi
  exact ScoreScalars.pair_power_two_hundred hq hn δ.coe_nonneg (Nat.cast_nonneg _) ha ha2 hN
    (score_pairs_off_radial_exception x hdim S O δ hδ F hF _ _ ha.le L hL Q hx hgood)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OutsidePairCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in

lemma outside_pair_card_le (S T O : Finset (ℙ K V)) (hST : S ⊆ T)
    (A B : Submodule K V) :
    (ActualOverlap.pairPoints x (outsideAt x S O) A B).card ≤
      ((T \ O).filter fun y => y.submodule ≤ A ⊓ B).card := by
  change (((outsideAt x S O).filter fun y => y.val.submodule ≤ A ⊓ B)).card ≤ _
  rw [outsideAt_filter_card]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy,hAB⟩ := Finset.mem_filter.mp hy
  obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
    ⟨hST hyS,fun ho => hyO (Finset.mem_union_left _ ho)⟩,hAB⟩

lemma score_pairs_le_captured {I : Type*} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X S : Finset (ℙ K V))
    (J M : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (a : ℝ) (hscale : (δ:ℝ)*(2*M) ≤ a) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S
          (ownCell F hF (fun i => flatPoints (P i)) X J x)) δ) p)).card ≤
      (capturedPairs F hF P X (G.image fun b => LinearMap.ker b.rep) J M x).card := by
  apply (pair_strength_count_le x _ δ G hG a).trans
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hne,hmass⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,hne,?_⟩
  have hcard := outside_pair_card_le x S
    (X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (ownCell F hF (fun i => flatPoints (P i)) X J x) hS p.1 p.2
  have hδ' : (0:ℝ)<δ := by exact_mod_cast hδ
  have hM : (2*(M:ℝ)) ≤
      (ActualOverlap.pairPoints x (outsideAt x S
        (ownCell F hF (fun i => flatPoints (P i)) X J x)) p.1 p.2).card := by
    apply (mul_le_mul_iff_right₀ hδ').mp
    exact hscale.trans hmass
  exact (by exact_mod_cast hM : 2*M ≤ _).trans hcard

theorem score_high_captured_pairs (hdim : finrank K V=5)
    {I : Type*} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0<X.card) (hb : 0<b) (hb2 : b≤2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*b^2)
    (hscale : (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) X.card b) ≤ a)
    (hx : x∉highExceptions F hF P X L J b χ Y) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S
          (ownCell F hF (fun i => flatPoints (P i)) X J x)) δ) p)).card ≤
      2*HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 := by
  apply (score_pairs_le_captured x F hF P X S J _ hS δ hδ G hG a hscale).trans
  apply high_pairs F hF P X hdim _ _ L hL hcomplete J b χ Y x hxY _ hn hb hb2 hhigh hx
  · intro A hA
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hA
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero H.rep_nonzero
    omega
  · intro A hA
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hA
    exact hG H hH

omit [Finite K] in

lemma score_pairs_le_residual (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (M : ℕ) (δ : ℝ≥0) (hδ : 0<δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H) (a : ℝ) (hscale : (δ:ℝ)*M ≤ a) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs G => a ≤
      WeightedPrograms.strength (pencilLines x G)
        (radialWeight x (outsideAt x S O) δ) p)).card ≤
      (residualPairs (G.image fun b => LinearMap.ker b.rep) X M).card := by
  apply (pair_strength_count_le x _ δ G hG a).trans
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hne,hmass⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,hne,?_⟩
  have hc := (outside_pair_card_le x S X O hS p.1 p.2).trans
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset)))
  have hδ' : (0:ℝ)<δ := by exact_mod_cast hδ
  have hM : (M:ℝ) ≤ (ActualOverlap.pairPoints x (outsideAt x S O) p.1 p.2).card := by
    apply (mul_le_mul_iff_right₀ hδ').mp
    exact hscale.trans hmass
  exact (by exact_mod_cast hM : M ≤ _).trans hc

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
lemma pair_tail_training_mono (S T : Finset {y : ℙ K V // x≠y}) (hST : S ⊆ T)
    (δ : ℝ≥0) (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (a : ℝ) :
    (Finset.univ.filter fun p : DistinctPairs F => a ≤ strength (pencilLines x F) (radialWeight x S δ) p).card ≤
    (Finset.univ.filter fun p : DistinctPairs F => a ≤ strength (pencilLines x F) (radialWeight x T δ) p).card := by
  apply Finset.card_le_card
  intro p hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.trans ?_⟩
  change mass (radialWeight x S δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤
    mass (radialWeight x T δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val)
  rw [mass_overlap x S δ F hF,mass_overlap x T δ F hF]
  apply mul_le_mul_of_nonneg_left _ δ.coe_nonneg
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hST)

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_antitone (S O T : Finset (ℙ K V)) (hOT : O ⊆ T) :
    outsideAt x S T ⊆ outsideAt x S O := by
  intro y hy
  simp only [outsideAt,Finset.mem_subtype,Finset.mem_sdiff] at hy ⊢
  exact ⟨hy.1,fun h => hy.2 (hOT h)⟩

theorem score_high_captured_pairs_of_le (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S O : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (hb : 0 < b) (hb2 : b ≤ 2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2 ≤ X.card*b^2)
    (hscale : (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) X.card b) ≤ a)
    (hx : x∉highExceptions F hF P X L J b χ Y) :
    (Finset.univ.filter (fun p : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) p)).card ≤
      2*HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 :=
  (pair_tail_training_mono x _ _ (outsideAt_antitone x S _ O hO) δ G hG a).trans
    (score_high_captured_pairs x hdim F hF P X S J hS δ hδ G hG L hL hcomplete
      a b χ Y hxY hn hb hb2 hhigh hscale hx)

theorem score_high_residual_pairs (hdim : finrank K V=5)
    (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (a b χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hscale : (δ:ℝ)*HighParameters.threshold (Nat.card K) X.card b ≤ a)
    (hx : x∉residualExceptions L X Y b χ) :
    (Finset.univ.filter (fun p : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) p)).card ≤
      HighParameters.degree (Nat.card K) X.card b χ*(Nat.card K+1)^2 := by
  apply (score_pairs_le_residual x X S O hS _ δ hδ G hG a hscale).trans
  apply residual_pairs hdim _ _ L hL hcomplete X Y b χ x hxY _ hx
  · intro A hA
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hA
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero H.rep_nonzero
    omega
  · intro A hA
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hA
    exact hG H hH

lemma high_threshold_scale (δ : ℝ≥0) (n a : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (hscale : n*(δ:ℝ) ≤ 4*Nat.card K) :
    (δ:ℝ)*(2*HighParameters.threshold (Nat.card K) n a) ≤ a := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
  have ht := Nat.floor_le (show 0 ≤ n*a/(64*Nat.card K) by positivity)
  change (HighParameters.threshold (Nat.card K) n a:ℝ) ≤ _ at ht
  calc
    _ ≤ (δ:ℝ)*(2*(n*a/(64*Nat.card K))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ht (by norm_num)) δ.coe_nonneg
    _ = (n*(δ:ℝ))*a/(32*Nat.card K) := by ring
    _ ≤ (4*Nat.card K)*a/(32*Nat.card K) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale ha) (by positivity)
    _ = a/8 := by field_simp; ring
    _ ≤ a := by linarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_HighOrSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem high_or_small {q n a : ℝ} (_hq : 0 ≤ q) (_hn : 0 < n) (ha : 0 ≤ a)
    (hhigh : 8388608*q^2 ≤ n) :
    2097152*q^2 ≤ n*a^2 ∨ n*a^99 ≤ q^2 := by
  by_cases h : 2097152*q^2 ≤ n*a^2
  · exact Or.inl h
  right
  have hlt : n*a^2 < 2097152*q^2 := lt_of_not_ge h
  have ha2 : a^2 < (1/2:ℝ)^2 := by
    have := mul_le_mul_of_nonneg_right hhigh (sq_nonneg a)
    nlinarith
  have ha' : a ≤ 1/2 := by nlinarith
  have hp := pow_le_pow_left₀ ha ha' 97
  calc
    n*a^99 = (n*a^2)*a^97 := by ring
    _ ≤ (2097152*q^2)*(1/2:ℝ)^97 := mul_le_mul hlt.le hp (pow_nonneg ha 97) (by positivity)
    _ ≤ q^2 := by
      have hc : (2097152:ℝ)*(1/2:ℝ)^97 ≤ 1 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg q)]

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_NormalizedPairHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem normalized_pair_high {q n a χ E : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hcap : n≤q^3)
    (hexp : (34359738369*2^200:ℝ)≤Real.exp χ)
    (hgeom : E≤2*(HighParameters.degree q n a χ:ℝ)*(q+1)^2) :
    E*a^200≤(q^4/n)^2*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hB : 0≤q^4/n := by positivity
  have hceil := Nat.ceil_lt_add_one (show 0≤34359738368*q^6/(n^2*a^4)*Real.exp χ by positivity)
  change (HighParameters.degree q n a χ:ℝ)<_ at hceil
  have hpoly := (pencil_factor hq).2
  have hb := pow_le_pow_left₀ hq0.le (q_le_B hq0 hn hcap) 2
  have hh := mul_le_mul_of_nonneg_right hgeom (pow_nonneg ha.le 200)
  have hbound : 2*(HighParameters.degree q n a χ:ℝ)*(q+1)^2*a^200 ≤
      34359738368*8*(q^4/n)^2*Real.exp χ*a^196+8*q^2*a^200 := by
    calc
      _ ≤ 2*(34359738368*q^6/(n^2*a^4)*Real.exp χ+1)*(4*q^2)*a^200 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha.le 200)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hceil.le (by norm_num)) hpoly
          (sq_nonneg (q+1)) (by positivity)
      _ = _ := by field_simp; ring
  have h1 : 1≤Real.exp χ := by linarith
  have hnoise : 8*q^2*a^200≤8*(q^4/n)^2*Real.exp χ*2^200 := by
    have hb' := hb.trans (le_mul_of_one_le_right (sq_nonneg _) h1)
    have hp := mul_le_mul hb' (pow_le_pow_left₀ ha.le ha2 200)
      (pow_nonneg ha.le 200) (by positivity : 0≤(q^4/n)^2*Real.exp χ)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤8)
  have hmain := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le ha2 196)
    (by positivity : 0≤34359738368*8*(q^4/n)^2*Real.exp χ)
  apply (hh.trans hbound).trans
  calc
    _ ≤ 34359738368*8*(q^4/n)^2*Real.exp χ*2^196+
        8*(q^4/n)^2*Real.exp χ*2^200 := add_le_add hmain hnoise
    _ ≤ (34359738369*2^200)*(q^4/n)^2*Real.exp χ := by
      have hcoef : (34359738368*8*2^196+8*2^200:ℝ)≤34359738369*2^200 := by norm_num
      calc
        _ = (34359738368*8*2^196+8*2^200)*((q^4/n)^2*Real.exp χ) := by ring
        _ ≤ (34359738369*2^200)*((q^4/n)^2*Real.exp χ) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = _ := by ring
    _ ≤ Real.exp χ*(q^4/n)^2*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add];ring

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScorePairCapturedNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_captured_normalized (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S O : Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (a χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (ha : 0 < a) (ha2 : a ≤ 2)
    (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 2097152*(Nat.card K:ℝ)^2 ≤ X.card*a^2)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hx : x∉highExceptions F hF P X Planes J a χ Y) :
    ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K))
  apply ScoreScalars.normalized_pair_high hq hn' ha ha2 hcap hchi
  have hh := score_high_captured_pairs_of_le x hdim F hF P X S O J hS hO δ hδ G hG
    Planes hPlanes hcomplete a a χ Y hxY hn ha ha2 hhigh
    (high_threshold_scale (K := K) δ X.card a hn' ha.le hscale) hx
  have hh' : ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ) ≤
      (2*HighParameters.degree (Nat.card K) X.card a χ*(Nat.card K+1)^2:ℕ) := Nat.cast_le.mpr hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh'

theorem score_pair_residual_normalized (hdim : finrank K V=5)
    (X S O : Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V)))
    (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (a χ : ℝ) (Y : Finset (ℙ K V)) (hxY : x∈Y)
    (hn : 0 < X.card) (ha : 0 < a) (ha2 : a ≤ 2)
    (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hx : x∉residualExceptions Planes X Y a χ) :
    ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
      (radialWeight x (outsideAt x S O) δ) z).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K))
  apply ScoreScalars.normalized_pair_high hq hn' ha ha2 hcap hchi
  have ht := high_threshold_scale (K := K) δ X.card a hn' ha.le hscale
  have ht' : (δ:ℝ)*HighParameters.threshold (Nat.card K) X.card a ≤ a := by
    have h0 : 0 ≤ (δ:ℝ)*(HighParameters.threshold (Nat.card K) X.card a:ℝ) := by positivity
    linarith
  have hh := score_high_residual_pairs x hdim X S O hS δ hδ G hG Planes hPlanes hcomplete
    a a χ Y hxY ht' hx
  have hh' : ((Finset.univ.filter fun z : DistinctPairs G => a ≤ strength (pencilLines x G)
    (radialWeight x (outsideAt x S O) δ) z).card:ℝ) ≤
    (HighParameters.degree (Nat.card K) X.card a χ*(Nat.card K+1)^2:ℕ) := Nat.cast_le.mpr hh
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] at hh'
  apply hh'.trans
  have h0 : 0 ≤ (HighParameters.degree (Nat.card K) X.card a χ:ℝ)*(Nat.card K+1)^2 := by positivity
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighGeometryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_captured_moment_sharp (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (J : ℕ) (hS : S ⊆ X \ remaining F hF (fun i => flatPoints (P i)) X J)
    (hO : ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hcaptured : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2 < (X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉highExceptions F hF P X Planes J ((δ:ℝ)*2^i) χ Q)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hn' : (0:ℝ) < X.card := by exact_mod_cast hn
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  by_cases hsmall : (X.card:ℝ)*((δ:ℝ)*2^i)^99≤(Nat.card K:ℝ)^2
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)
  · have hlarge := (ScoreScalars.high_or_small (q := (Nat.card K:ℝ)) (n := X.card)
        (by positivity) hn' ha.le hhigh).resolve_right hsmall
    exact score_pair_captured_normalized x hdim F hF P X S (O x) J hS hO δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hlarge hchi
      (hcaptured i hi (lt_of_not_ge hsmall))

theorem score_pair_residual_moment_sharp (hdim : finrank K V=5)
    (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (hS : S ⊆ X)
    (δ : ℝ≥0) (hδ : 0 < δ) (G : Finset (ℙ K (Dual K V))) (hG : ∀ H∈G,Incident x H)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀ A∈Planes,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈Planes)
    (χ : ℝ) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hn : 0 < X.card) (hcap : (X.card:ℝ) ≤ (Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(δ:ℝ) ≤ 4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2 ≤ X.card)
    (hchi : (34359738369*2^200:ℝ) ≤ Real.exp χ)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀ l : RadialLine x,l.val∈Lines)
    (hm : ∀ H : G,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x G H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        ((Nat.card K:ℝ)^4/X.card^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (hresidual : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2 < (X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉residualExceptions Planes X Q ((δ:ℝ)*2^i) χ)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/X.card)^2*Real.exp (2*χ)) := by
  have hqpos : (0:ℝ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
  have hn' : (0:ℝ) < X.card :=
    (mul_pos (by norm_num : (0:ℝ) < 8388608) (sq_pos_of_pos hqpos)).trans_le hhigh
  apply score_higher_power x _ δ hδ G hG _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have ha2 := (Finset.mem_filter.mp hi).2
  by_cases hsmall : (X.card:ℝ)*((δ:ℝ)*2^i)^99≤(Nat.card K:ℝ)^2
  · exact score_pair_small_normalized x hdim S O δ hδ G hG X.card _ χ hn' ha ha2 hmass hsmall
      (le_trans (by norm_num) hchi) Lines hLines Q hx (hgood i hi)
  · exact score_pair_residual_normalized x hdim X S (O x) hS δ hδ G hG
      Planes hPlanes hcomplete _ χ Q hx hn ha ha2 hcap hscale hchi (hresidual i hi (lt_of_not_ge hsmall))

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma boundedOverlapDyads_subset (x : ℙ K V) (S O : Finset (ℙ K V)) (δ : ℝ≥0) :
    boundedOverlapDyads x (outsideAt x S O) δ 2⊆strengthDyads S.card δ := by
  intro i hi
  obtain ⟨hi,hcap⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨?_,hcap⟩
  apply Finset.mem_range.mpr
  exact (Finset.mem_range.mp hi).trans_le
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (outsideAt_card_le x S O)) 1)

lemma off_radialExceptions (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ)
    (x : ℙ K V) (hx : x∉radialExceptions S O δ Lines Q q n χ) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100) := by
  intro i hi hh
  exact hx (Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,hh⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PeelingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial TrainingCells
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma badCenters_threshold_mono (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) {D E : ℝ} (hDE : D≤E) :
    badCenters S O δ a Lines Q E⊆badCenters S O δ a Lines Q D := by
  intro x hx
  obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,hDE.trans he⟩

lemma radialExceptions_normalization (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q χ m n : ℝ) (hm : 0 < m) (hmn : m ≤ n) :
    radialExceptions S O δ Lines Q q m χ⊆radialExceptions S O δ Lines Q q n χ := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,badCenters_threshold_mono S O δ _ Lines Q ?_ hx⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm) ((sq_le_sq₀ hm.le (hm.le.trans hmn)).mpr hmn)

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type} [LinearOrder I]

lemma off_highPlaneExceptions (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V))
    (x : ℙ K V) (hx : x∉highPlaneExceptions F hF Flat X S Planes j δ χ Q) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q := by
  intro i hi hlarge hh
  apply hx
  exact Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,by simpa only [ite_eq_left hlarge] using hh⟩

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Peeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma off_residualPlaneExceptions (Planes : Finset (Submodule K V))
    (X S Q : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (χ : ℝ)
    (x : ℙ K V) [Fintype (RadialLine x)]
    (hx : x∉residualPlaneExceptions Planes X S Q δ χ) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉residualExceptions Planes X Q ((δ:ℝ)*2^i) χ := by
  intro i hi hlarge hh
  apply hx
  exact Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,by simpa only [ite_eq_left hlarge] using hh⟩

end SharpRamseyFive.ScoreGeometry

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

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HyperplaneHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [LinearOrder J]

theorem literal_hyperplane_pair_moment_oai [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (hdim : finrank K V=5)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X XH S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
    (hcomplete : ∀A : Submodule K V,finrank K A=3 → A∈Planes)
    (e : Prop) (_he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (x : ℙ K V) [Fintype (RadialLine x)]
    (hO : ownCell F hF (fun i=>flatPoints (Flat i)) X
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) x⊆O x)
    (G : Finset (ℙ K (Dual K V))) (hG : ∀H∈G,Incident x H)
    (χ : ℝ) (hχ : (34359738369*2^200:ℝ)≤Real.exp χ)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(pointStrength (K:=K) S:ℝ)≤4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hm : ∀H : G,mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x G H)≤2)
    (hgood : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ)
    (hpair : x∉hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) (pointStrength S) χ Q) :
    (∑z : DistinctPairs G,strength (pencilLines x G)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2 := by
  have hHX : XH⊆X := hXH▸peel_subset e F hF (fun i=>flatPoints (Flat i)) X _ _
  have hSH : (S.card:ℝ)≤XH.card := Nat.cast_le.mpr (Finset.card_le_card hS)
  have hHXn : (XH.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card hHX)
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hS0 : (0:ℝ)<S.card := (by positivity : 0<8388608*(Nat.card K:ℝ)^2).trans_le hhigh
  have hH0 : (0:ℝ)<XH.card := hS0.trans_le hSH
  have hX0 : (0:ℝ)<X.card := hH0.trans_le hHXn
  have hδ : 0<pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength];positivity
  have hmass : (pointStrength (K:=K) S:ℝ)*S.card≤Nat.card K := by
    rw [coe_pointStrength,div_mul_cancel₀ _ hS0.ne']
  have hgoodH : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) XH.card χ := by
    exact fun hx=>hgood (radialExceptions_normalization S O (pointStrength S) Lines Q (Nat.card K) χ XH.card X.card hH0 hHXn hx)
  have hfin (N : ℕ) (hSN : S.card≤N) (hh :
      (∑z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      2^200*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/N)^2*Real.exp (2*χ))) :
      (∑z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2 := by
    apply hh.trans
    unfold dyadFactor geometryScale
    rw [show 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*(((Nat.card K:ℝ)^4/N)^2*Real.exp (2*χ))=
      (2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*Real.exp (2*χ))*((Nat.card K:ℝ)^4/N)^2 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    gcongr
  unfold hyperplanePeelExceptions at hpair
  split_ifs at hpair with hc
  · apply hfin X.card (Finset.card_le_card (hS.trans hHX))
    apply score_pair_captured_moment_sharp x hdim F hF Flat X S O _ (hc▸hS) hO (pointStrength S) hδ G hG
      Planes hPlanes hcomplete χ Q hxQ (by exact_mod_cast hX0) hcap hscale (hhigh.trans (hSH.trans hHXn)) hχ hmass
      Lines hLines hm
      (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ x hgood)
      (off_highPlaneExceptions F hF Flat X S O Planes _ (pointStrength S) χ Q x hpair) 200 (le_refl _)
  · apply hfin XH.card (Finset.card_le_card hS)
    apply score_pair_residual_moment_sharp x hdim XH S O hS (pointStrength S) hδ G hG Planes hPlanes hcomplete
      χ Q hxQ (by exact_mod_cast hH0) (hHXn.trans hcap)
      ((mul_le_mul_of_nonneg_right hHXn (pointStrength (K:=K) S).coe_nonneg).trans hscale)
      (hhigh.trans hSH) hχ hmass Lines hLines hm
      (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) XH.card χ x hgoodH)
      (off_residualPlaneExceptions Planes XH S Q O (pointStrength S) χ x hpair) 200 (le_refl _)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment_oai := @OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment_oai
