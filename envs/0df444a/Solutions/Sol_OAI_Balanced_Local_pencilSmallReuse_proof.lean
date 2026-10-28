-- Prove2me | solution 1 for OAI.Balanced.Local.pencilSmallReuse_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:21:10.941998+00:00
-- url     : https://prove2.me/submissions/3ec995bb-c5ac-4b1f-85e5-b5625bf009c4

import Mathlib
import Definitions.Def_OAIQ63Br002

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_RootChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

theorem exists_maximal_roots (A : ι → Finset α) (s : Finset ι) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R → (A i ∩ R.biUnion A).Nonempty := by
  classical
  let candidates := s.powerset.filter (DisjointRoots A)
  have hempty : ∅ ∈ candidates := by simp [candidates, DisjointRoots]
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  obtain ⟨hRs, hdisj⟩ := Finset.mem_filter.mp hR
  have hsub : R ⊆ s := Finset.mem_powerset.mp hRs
  refine ⟨R, hsub, hdisj, ?_⟩
  intro i hi hin
  by_contra hnone
  have hdisjnew : DisjointRoots A (insert i R) := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hjk.symm
      apply Finset.disjoint_left.mpr
      intro a hai hak
      exact hnone ⟨a, Finset.mem_inter.mpr
        ⟨hai, Finset.mem_biUnion.mpr ⟨k, hkR, hak⟩⟩⟩
    · have hjR : j ∈ R := (Finset.mem_insert.mp hj).resolve_left hji
      by_cases hki : k = i
      · subst k
        apply Finset.disjoint_left.mpr
        intro a haj hai
        exact hnone ⟨a, Finset.mem_inter.mpr
          ⟨hai, Finset.mem_biUnion.mpr ⟨j, hjR, haj⟩⟩⟩
      · have hkR : k ∈ R := (Finset.mem_insert.mp hk).resolve_left hki
        exact hdisj j hjR k hkR hjk
  have hnew : insert i R ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), hdisjnew⟩
  have hc := hmax (insert i R) hnew
  rw [Finset.card_insert_of_notMem hin] at hc
  omega

theorem exists_roots_of_small_shared (A : ι → Finset α) (s : Finset ι)
    (hsmall : ∀ i ∈ s, (A i ∩ (s.erase i).biUnion A).card ≤ 1) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  obtain ⟨R, hRs, hdisj, hmeet⟩ := exists_maximal_roots A s
  refine ⟨R, hRs, hdisj, ?_⟩
  intro i hi hin
  have hRerase : R ⊆ s.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji => hin (hji ▸ hj), hRs hj⟩
  have hinter : A i ∩ R.biUnion A ⊆ A i ∩ (s.erase i).biUnion A := by
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hcard : (A i ∩ R.biUnion A).card = 1 := by
    have hpos := Finset.card_pos.mpr (hmeet i hi hin)
    have hle := (Finset.card_le_card hinter).trans (hsmall i hi)
    omega
  refine ⟨hcard, ?_⟩
  obtain ⟨a, ha⟩ := hmeet i hi hin
  intro x hx
  have hxa : x = a := Finset.card_le_one.mp (hsmall i hi) x hx a (hinter ha)
  exact hxa ▸ (Finset.mem_inter.mp ha).2

theorem disjointRoots_of_zero_reuse (A : ι → Finset α) (s : Finset ι)
    (hz : (∑ i ∈ s, (A i).card) - (s.biUnion A).card = 0) :
    DisjointRoots A s := by
  intro i hi j hj hij
  have hd := Balanced.family_reuse_erase A s i hi
  have hc : (A i ∩ (s.erase i).biUnion A).card = 0 := by omega
  have he := Finset.card_eq_zero.mp hc
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have ha : a ∈ A i ∩ (s.erase i).biUnion A :=
    Finset.mem_inter.mpr ⟨hai, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hij.symm, hj⟩, haj⟩⟩
  simp only [he, Finset.notMem_empty] at ha

theorem exists_roots_of_large_shared (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2)
    (i : ι) (hi : i ∈ s) (hbig : 2 ≤ (A i ∩ (s.erase i).biUnion A).card) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ j ∈ s, j ∉ R →
        (A j ∩ R.biUnion A).card = 1 ∧
        A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
  classical
  have hd := Balanced.family_reuse_erase A s i hi
  have hz : (∑ j ∈ s.erase i, (A j).card) - ((s.erase i).biUnion A).card = 0 := by
    omega
  have hrest := disjointRoots_of_zero_reuse A (s.erase i) hz
  let R := insert i ((s.erase i).filter fun j => Disjoint (A j) (A i))
  have hiR : i ∈ R := Finset.mem_insert_self _ _
  have hRs : R ⊆ s := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
  have hroot : DisjointRoots A R := by
    intro j hj k hk hjk
    by_cases hji : j = i
    · subst j
      have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hjk.symm)
      exact hkf.2.symm
    · have hjf := Finset.mem_filter.mp ((Finset.mem_insert.mp hj).resolve_left hji)
      by_cases hki : k = i
      · subst k
        exact hjf.2
      · have hkf := Finset.mem_filter.mp ((Finset.mem_insert.mp hk).resolve_left hki)
        exact hrest j hjf.1 k hkf.1 hjk
  refine ⟨R, hRs, hroot, ?_⟩
  intro j hj hjR
  have hji : j ≠ i := fun h => hjR (h ▸ hiR)
  have hjrest : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
  have hnD : ¬ Disjoint (A j) (A i) := by
    intro hD
    exact hjR (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hjrest, hD⟩))
  have hshared : A j ∩ (s.erase j).biUnion A = A j ∩ A i := by
    ext a
    constructor
    · intro ha
      obtain ⟨haj, har⟩ := Finset.mem_inter.mp ha
      obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp har
      by_cases hki : k = i
      · exact Finset.mem_inter.mpr ⟨haj, hki ▸ hak⟩
      · have hkrest : k ∈ s.erase i :=
          Finset.mem_erase.mpr ⟨hki, (Finset.mem_erase.mp hk).2⟩
        exact (Finset.disjoint_left.mp
          (hrest j hjrest k hkrest (Finset.mem_erase.mp hk).1.symm) haj hak).elim
    · intro ha
      obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨haj, Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hji.symm, hi⟩, hai⟩⟩
  have hsharedRoots : A j ∩ (s.erase j).biUnion A ⊆ R.biUnion A := by
    rw [hshared]
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, hiR, (Finset.mem_inter.mp ha).2⟩
  refine ⟨?_, hsharedRoots⟩
  have hRerase : R ⊆ s.erase j := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun h => hjR (h ▸ hk), hRs hk⟩
  have hinter : A j ∩ R.biUnion A ⊆ A j ∩ A i := by
    rw [← hshared]
    apply Finset.inter_subset_inter_left
    exact Finset.biUnion_subset_biUnion_of_subset_left A hRerase
  have hle := (Finset.card_le_card hinter).trans (hpair j hj i hi hji)
  have hnon : (A j ∩ A i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hnD (Finset.disjoint_iff_inter_eq_empty.mpr he)
  obtain ⟨a, ha⟩ := hnon
  obtain ⟨haj, hai⟩ := Finset.mem_inter.mp ha
  have hpos : 0 < (A j ∩ R.biUnion A).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr
      ⟨haj, Finset.mem_biUnion.mpr ⟨i, hiR, hai⟩⟩⟩
  omega

theorem exists_root_child_partition (A : ι → Finset α) (s : Finset ι)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hr : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ R ⊆ s, DisjointRoots A R ∧
      ∀ i ∈ s, i ∉ R →
        (A i ∩ R.biUnion A).card = 1 ∧
        A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A := by
  by_cases hbig : ∃ i ∈ s, 2 ≤ (A i ∩ (s.erase i).biUnion A).card
  · obtain ⟨i, hi, hbig⟩ := hbig
    exact exists_roots_of_large_shared A s hpair hr i hi hbig
  · apply exists_roots_of_small_shared A s
    intro i hi
    have hn : ¬ 2 ≤ (A i ∩ (s.erase i).biUnion A).card := fun h => hbig ⟨i, hi, h⟩
    omega

theorem exists_pattern_roots {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b),
      DisjointRoots (fun i => Finset.univ.image (P.classOf i)) R ∧
      ∀ i, i ∉ R →
        ((Finset.univ.image (P.classOf i)) ∩
          R.biUnion (fun j => Finset.univ.image (P.classOf j))).card = 1 ∧
        (Finset.univ.image (P.classOf i)) ∩
          (Finset.univ.erase i).biUnion (fun j => Finset.univ.image (P.classOf j)) ⊆
          R.biUnion (fun j => Finset.univ.image (P.classOf j)) := by
  let A : Fin b → Finset (Fin (4 * b - κ)) := fun i => Finset.univ.image (P.classOf i)
  have hcard (i : Fin b) : (A i).card = 4 := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ (P.withinTuple i)]
    simp
  have hUnion : Finset.univ.biUnion A = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨⟨i, j⟩, h⟩ := P.everyClass c
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩⟩
  have hreuse : (∑ i : Fin b, (A i).card) - (Finset.univ.biUnion A).card ≤ 2 := by
    simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hUnion]
    omega
  obtain ⟨R, hRs, hroots, hchildren⟩ := exists_root_child_partition A Finset.univ
    (fun i _ j _ hij => P.pairOverlap i j hij) hreuse
  exact ⟨R, hroots, fun i hin => hchildren i (Finset.mem_univ _) hin⟩

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_UnusedOffsetIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Balanced.UnusedOffsetIncidence

theorem probability_eq_pmf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    probability E = ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal := by
  classical
  rw [PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp [probability, ENNReal.toReal_div]

theorem probability_mono {Ω : Type*} [Fintype Ω] {E G : Ω → Prop}
    (h : ∀ ω, E ω → G ω) : probability E ≤ probability G := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ω hω
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩

theorem probability_exists_le {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  have heq : Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω) =
      s.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext ω
    simp
  have hb : (Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω)).card ≤
      ∑ i ∈ s, (Finset.univ.filter (E i)).card := by
    rw [heq]
    exact Finset.card_biUnion_le
  unfold probability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hc := (Nat.cast_le (α := ℝ)).mpr hb
  push_cast at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  ext ω
  simp

theorem probability_exists_fintype_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i, E i ω) ≤ ∑ i, probability (E i) := by
  simpa using probability_exists_le (Finset.univ : Finset ι) E

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_EqualityPatternOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.EqualityPattern

open Finset

theorem classSet_reuse_eq {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    (∑ i : Fin b, (P.classSet i).card) -
      (Finset.univ.biUnion P.classSet).card = κ := by
  rw [P.sum_card_classSet, P.card_biUnion_classSet]
  omega

end Balanced.Local.EqualityPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignmentNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

open AlignedListProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem alignmentNormalization_proof : AlignmentNormalizationResult.{u} := by
  intro F _ _ _ b κ _ _ hκ P a ha bits p
  exact alignment_probability P hκ a ha bits p

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformConditionalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformConditionalProduct

open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_product_eq_bind {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).map (fun b => (a, b))) := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv,
    ite_and]

end
end Balanced.UniformConditionalProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedUnused

open UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionedOffsetProbability_eq_alignedLaw {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((alignedLaw P hκ a ha bits p).toOuterMeasure {M | E M}).toReal := by
  let A : MergedPairs F → Prop := Aligned P a bits p
  let : Nonempty {M : MergedPairs F // A M} := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  let : Nonempty ({M : MergedPairs F | A M} : Set (MergedPairs F)) := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  have hcard (H : MergedPairs F → Prop) :
      offsetProbability H = (Fintype.card {M // H M} : ℝ) / Fintype.card (MergedPairs F) := by
    unfold offsetProbability
    rw [← FiniteUniformFibers.probability_eq_sum H,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
    simp [Fintype.card_subtype]
  have hnum : Fintype.card {M : {M : MergedPairs F // A M} // E M} =
      Fintype.card {M : MergedPairs F // A M ∧ E M} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter A E)
  change offsetProbability (fun M => A M ∧ E M) / offsetProbability A = _
  rw [hcard, hcard]
  change _ = (((PMF.uniformOfFintype (MergedPairs F)).filter {M | A M}
    (alignment_supported P hκ a ha bits p)).toOuterMeasure {M | E M}).toReal
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  change _ = (Fintype.card {M : {M : MergedPairs F // A M} // E M} : ℝ) /
    Fintype.card {M : MergedPairs F // A M}
  rw [hnum]
  have htotal : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  have hcardinst (f g : Fintype {M : MergedPairs F // A M ∧ E M}) :
      @Fintype.card _ f = @Fintype.card _ g := by
    cases Subsingleton.elim f g
    rfl
  exact congrArg (Nat.cast : ℕ → ℝ) (hcardinst _ _)

end
end Balanced.Local.AlignedUnused

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootChildCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem reuse_roots_eq_zero (A : ι → Finset α) (R : Finset ι)
    (hroots : DisjointRoots A R) :
    (∑ i ∈ R, (A i).card) - (R.biUnion A).card = 0 := by
  have hc : (R.biUnion A).card = ∑ i ∈ R, (A i).card :=
    Finset.card_biUnion (by intro i hi j hj hij; exact hroots i hi j hj hij)
  rw [hc, Nat.sub_self]

theorem child_overlap_intermediate (A : ι → Finset α) (s R t : Finset ι)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A)
    (i : ι) (hi : i ∈ s) (hin : i ∉ R)
    (hRt : R ⊆ t) (ht : t ⊆ s.erase i) :
    (A i ∩ t.biUnion A).card = 1 := by
  obtain ⟨hc, hs⟩ := hchildren i hi hin
  have he : A i ∩ t.biUnion A = A i ∩ R.biUnion A := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨hai, hat⟩ := Finset.mem_inter.mp ha
      have har : a ∈ (s.erase i).biUnion A :=
        Finset.biUnion_subset_biUnion_of_subset_left A ht hat
      exact Finset.mem_inter.mpr ⟨hai, hs (Finset.mem_inter.mpr ⟨hai, har⟩)⟩
    · apply Finset.inter_subset_inter_left
      exact Finset.biUnion_subset_biUnion_of_subset_left A hRt
  rw [he, hc]

theorem child_card_eq_reuse (A : ι → Finset α) (s R : Finset ι)
    (hRs : R ⊆ s) (hroots : DisjointRoots A R)
    (hchildren : ∀ i ∈ s, i ∉ R →
      (A i ∩ R.biUnion A).card = 1 ∧
      A i ∩ (s.erase i).biUnion A ⊆ R.biUnion A) :
    (s \ R).card = (∑ i ∈ s, (A i).card) - (s.biUnion A).card := by
  have hcount (t : Finset ι) (ht : t ⊆ s \ R) :
      (∑ i ∈ R ∪ t, (A i).card) - ((R ∪ t).biUnion A).card = t.card := by
    induction t using Finset.induction_on with
    | empty => simpa using reuse_roots_eq_zero A R hroots
    | @insert i t hin ih =>
      have his : i ∈ s := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).1
      have hinR : i ∉ R := (Finset.mem_sdiff.mp (ht (Finset.mem_insert_self _ _))).2
      have hts : t ⊆ s \ R := fun j hj => ht (Finset.mem_insert_of_mem hj)
      have hnot : i ∉ R ∪ t := by simp [hinR, hin]
      have hsub : R ∪ t ⊆ s.erase i := by
        intro j hj
        rcases Finset.mem_union.mp hj with hjR | hjt
        · exact Finset.mem_erase.mpr ⟨fun h => hinR (h ▸ hjR), hRs hjR⟩
        · exact Finset.mem_erase.mpr ⟨fun h => hin (h ▸ hjt),
            (Finset.mem_sdiff.mp (hts hjt)).1⟩
      have hoverlap := child_overlap_intermediate A s R (R ∪ t)
        hchildren i his hinR Finset.subset_union_left hsub
      rw [Finset.union_insert, Balanced.family_reuse_insert A (R ∪ t) i hnot,
        ih hts, hoverlap, Finset.card_insert_of_notMem hin]
  have h := hcount (s \ R) (fun _ h => h)
  rw [Finset.union_sdiff_of_subset hRs] at h
  exact h.symm

theorem exists_pattern_roots_exact {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (hκ : κ ≤ 2) (hfit : κ ≤ 4 * b) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet := by
  obtain ⟨R, hroots, hchildren⟩ := exists_pattern_roots P hκ
  have hc := child_card_eq_reuse P.classSet Finset.univ R (Finset.subset_univ _)
    hroots (fun i _ hin => hchildren i hin)
  rw [P.classSet_reuse_eq hfit] at hc
  exact ⟨R, hroots, hc, hchildren⟩

theorem exists_pattern_roots_exact_of_three_le {b κ : ℕ}
    (P : Local.EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (Fin b), DisjointRoots P.classSet R ∧
      (Finset.univ \ R).card = κ ∧
      ∀ i, i ∉ R →
        (P.classSet i ∩ R.biUnion P.classSet).card = 1 ∧
        P.classSet i ∩ (Finset.univ.erase i).biUnion P.classSet ⊆
          R.biUnion P.classSet :=
  exists_pattern_roots_exact P hκ (by omega)

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootChildDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

theorem card_rootGeneratorIndices {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    (rootGeneratorIndices P R i).card = (P.classSet i ∩ R.biUnion P.classSet).card := by
  have he : (rootGeneratorIndices P R i).image (P.classOf i) =
      P.classSet i ∩ R.biUnion P.classSet := by
    ext a
    simp only [rootGeneratorIndices, Local.EqualityPattern.classSet,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hj⟩
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hj, rfl⟩
  rw [← he, Finset.card_image_of_injective _ (P.withinTuple i)]

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_OneReuseDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

theorem touchedPositions_singleton (j : Fin 4) :
    touchedPositions {j} = {j, j - 1} := by
  have h : ∀ j : Fin 4, touchedPositions {j} = {j, j - 1} := by decide
  exact h j

theorem dependentOccurrences_eq_pair {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (child : Fin b) (j : Fin 4)
    (hchildren : Finset.univ \ R = {child})
    (hgen : rootGeneratorIndices P R child = {j}) :
    dependentOccurrences P R = {(child, j), (child, j - 1)} := by
  simp [dependentOccurrences, hchildren, hgen, touchedPositions_singleton]

theorem exists_one_reuse_linked_pair {b : ℕ} (P : Local.EqualityPattern b 1)
    (hb : 3 ≤ b) :
    ∃ R : Finset (Fin b), ∃ root child : Fin b, ∃ r s : Fin 4,
      DisjointRoots P.classSet R ∧
      root ∈ R ∧ child ∉ R ∧ root ≠ child ∧
      Finset.univ \ R = {child} ∧
      rootGeneratorIndices P R child = {s} ∧
      P.classOf root r = P.classOf child s ∧
      dependentOccurrences P R = {(child, s), (child, s - 1)} ∧
      P.classSet child ∩ (Finset.univ.erase child).biUnion P.classSet ⊆
        R.biUnion P.classSet := by
  obtain ⟨R, hroots, hcard, hchildren⟩ :=
    exists_pattern_roots_exact_of_three_le P hb (by omega)
  obtain ⟨child, hchild⟩ := Finset.card_eq_one.mp hcard
  have hcn : child ∉ R := by
    have h : child ∈ Finset.univ \ R := by rw [hchild]; simp
    exact (Finset.mem_sdiff.mp h).2
  obtain ⟨hone, hprivate⟩ := hchildren child hcn
  have hgens : (rootGeneratorIndices P R child).card = 1 := by
    rw [card_rootGeneratorIndices, hone]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hgens
  have hshared : P.classOf child s ∈ R.biUnion P.classSet := by
    have h : s ∈ rootGeneratorIndices P R child := by rw [hs]; simp
    exact (Finset.mem_filter.mp h).2
  obtain ⟨root, hr, hclass⟩ := Finset.mem_biUnion.mp hshared
  obtain ⟨r, _, hrc⟩ := Finset.mem_image.mp hclass
  refine ⟨R, root, child, r, s, hroots, hr, hcn, ?_, hchild, hs, hrc, ?_, hprivate⟩
  · intro h
    exact hcn (h ▸ hr)
  · exact dependentOccurrences_eq_pair P R child s hchild hs

end Balanced.RootChildPartition

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition AlignedUnused
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generated_unused {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (z : (FreeIndex P R → F) × UnusedArray P a)
    (d : {d : Direction F // d ∉ usedDirections P a}) :
    ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 d.1 = z.2 d := by
  exact congrFun (congrArg Prod.snd
    ((coordinateEquiv P hκ R hD a ha bits p).apply_symm_apply z)) d

theorem alignedLaw_eq_uniform_coordinates {b κ : ℕ} (P : EqualityPattern b κ)
    (hκ : κ ≤ 2) (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    alignedLaw P hκ a ha bits p =
      (PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).map
        (fun z => ((coordinateEquiv P hκ R hD a ha bits p).symm z).1) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  let : Nonempty (AlignedOffsets P a bits p) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  let : Nonempty ({M : MergedPairs F | Aligned P a bits p M} : Set (MergedPairs F)) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  unfold alignedLaw
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype (AlignedOffsets P a bits p)).map Subtype.val = _
  have h := uniform_map_equiv e.symm
  rw [← h, PMF.map_comp]
  rfl

theorem conditioned_probability_eq_uniform_coordinates {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).toOuterMeasure
        {z | E ((coordinateEquiv P hκ R hD a ha bits p).symm z).1}).toReal := by
  rw [conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p E,
    alignedLaw_eq_uniform_coordinates P hκ R hD a ha bits p,
    PMF.toOuterMeasure_map_apply]
  rfl

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UnusedOffsetAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Balanced.UnusedOffsetIncidence

theorem pmf_sum_real {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => μ.apply_ne_top a)]
  have h : ∑ a, μ a = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  rw [h]
  simp

theorem pmf_outer_ne_top {α : Type*} (μ : PMF α) (E : Set α) :
    μ.toOuterMeasure E ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact μ.tsum_coe_indicator_ne_top E

theorem bind_probability_le {α β : Type*} [Fintype α]
    (μ : PMF α) (ν : α → PMF β) (E : Set β) (r : ℝ)
    (h : ∀ a, ((ν a).toOuterMeasure E).toReal ≤ r) :
    ((μ.bind ν).toOuterMeasure E).toReal ≤ r := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
      (μ.apply_ne_top a) (pmf_outer_ne_top (ν a) E))]
  simp_rw [ENNReal.toReal_mul]
  calc
    (∑ a, (μ a).toReal * ((ν a).toOuterMeasure E).toReal) ≤
        ∑ a, (μ a).toReal * r :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = r := by rw [← Finset.sum_mul, pmf_sum_real μ, one_mul]

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedCoordinateAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment AlignedUnused UniformConditionalProduct

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionedOffsetProbability_le_of_freeCoordinate_fibers {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) (β : ℝ)
    (h : ∀ u : UnusedArray P a,
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | E ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1}).toReal ≤ β) :
    conditionedOffsetProbability (Aligned P a bits p) E ≤ β := by
  rw [conditioned_probability_eq_uniform_coordinates P hκ R hD a ha bits p E]
  have hs := uniform_map_equiv
    (Equiv.prodComm (UnusedArray P a) (FreeIndex P R → F))
  rw [← hs, PMF.toOuterMeasure_map_apply, uniform_product_eq_bind]
  apply UnusedOffsetIncidence.bind_probability_le
  intro u
  rw [PMF.toOuterMeasure_map_apply]
  exact h u

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAnchorExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AnchorExclusion

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (M : MergedPairs F)

theorem ordinary_line_no_shared_constituent (p : Point F)
    (hA : Admissible P a bits p M) (l : Line F)
    (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    {ij kl : Fin b × Fin 4} (hne : ij ≠ kl) (d : Direction F) (s : Bool)
    (hi : OnLine (prescribedPoint P a bits M ij) (constituent M d s))
    (hk : OnLine (prescribedPoint P a bits M kl) (constituent M d s)) :
    ¬ (OnLine (prescribedPoint P a bits M ij) l ∧
      OnLine (prescribedPoint P a bits M kl) l) := by
  rintro ⟨hil, hkl⟩
  have hpoint : prescribedPoint P a bits M ij ≠ prescribedPoint P a bits M kl :=
    fun h => hne (hA.2.1 h)
  have heq := eq_of_two_common_points _ _ hpoint l (constituent M d s)
    hil hkl hi hk
  apply hl
  rw [heq]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(d, s), Finset.mem_univ _, rfl⟩)

omit [Fintype F] [DecidableEq F] in

theorem class_eq_of_shared_constituents (ha : Eligible P a)
    {x y : Point F} (hxy : x ≠ y) (c e : Fin (4 * b - κ)) (s t : Bool)
    (hxc : OnLine x (constituent M (a.2 c) s))
    (hyc : OnLine y (constituent M (a.2 c) s))
    (hxe : OnLine x (constituent M (a.2 e) t))
    (hye : OnLine y (constituent M (a.2 e) t)) : c = e := by
  apply ha.2.1
  exact congrArg Prod.fst (eq_of_two_common_points x y hxy _ _ hxc hyc hxe hye)

theorem used_pair_no_self_anchor (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) {ij kl : Fin b × Fin 4} (hne : ij ≠ kl)
    (c e : Fin (4 * b - κ)) (s t : Bool)
    (hnc : ¬ Purposeful P c ij) (he : Purposeful P e ij)
    (hie : OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 e) t))
    (hke : OnLine (prescribedPoint P a bits M kl) (constituent M (a.2 e) t)) :
    ¬ (OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s) ∧
      OnLine (prescribedPoint P a bits M kl) (constituent M (a.2 c) s)) := by
  rintro ⟨hic, hkc⟩
  have hpoint : prescribedPoint P a bits M ij ≠ prescribedPoint P a bits M kl :=
    fun h => hne (hA.2.1 h)
  have hce := class_eq_of_shared_constituents P a M ha hpoint c e s t hic hkc hie hke
  exact hnc (hce.symm ▸ he)

end
end Balanced.Local.AnchorExclusion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrescribedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M : MergedPairs F}

omit [Fintype F] [DecidableEq F] in

theorem exists_prescribedPoint_on_constituent (hE : Eligible P a)
    (c : Fin (4 * b - κ)) (s : Bool) :
    ∃ ij : Fin b × Fin 4,
      OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hc⟩ := P.everyClass c
  change P.classOf i j = c at hc
  by_cases hs : s = bits i j
  · refine ⟨(i, j), ?_⟩
    simpa only [hc, hs] using prescribedPoint_on_left (M := M) hE i j
  · have hs' : s = !(bits i j) := by
      cases s <;> cases h : bits i j <;> simp_all
    refine ⟨(i, j + 3), ?_⟩
    have hj : (j + 3) + 1 = j := by fin_cases j <;> decide
    simpa only [hj, hc, hs'] using prescribedPoint_on_right (M := M) hE i (j + 3)

theorem not_onLine_used_constituent (hE : Eligible P a)
    (hA : Admissible P a bits p M) (c : Fin (4 * b - κ)) (s : Bool) :
    ¬ OnLine p (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hpoint⟩ := exists_prescribedPoint_on_constituent hE c s
  intro hp
  have hline : constituent M (a.2 c) s ≠ lineThrough (a.1 i) p := by
    intro heq
    exact hA.2.2.2.1 i (heq ▸
      Finset.mem_image.mpr ⟨(a.2 c, s), Finset.mem_univ _, rfl⟩)
  exact hA.2.2.1 (i, j)
    (common_point_eq_of_lines_ne _ _ hline _ p hpoint (hA.1 (i, j)) hp
      (onLine_lineThrough _ _))

theorem direction_unused_of_onLine (hE : Eligible P a)
    (hA : Admissible P a bits p M) {d : Direction F} {s : Bool}
    (hp : OnLine p (constituent M d s)) :
    d ∉ Finset.univ.image a.2 := by
  intro hd
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
  exact not_onLine_used_constituent hE hA c s hp

theorem mem_prescribedPartners_iff_unused (hE : Eligible P a)
    (hA : Admissible P a bits p M) (x : Point F) :
    x ∈ prescribedPartners P a bits p M ↔
      x ∈ prescribedDesignated P a bits M ∧
      ∃ ds : Direction F × Bool,
        ds.1 ∉ Finset.univ.image a.2 ∧
        OnLine p (constituent M ds.1 ds.2) ∧
        OnLine x (constituent M ds.1 (!ds.2)) := by
  constructor
  · intro hx
    obtain ⟨hF, ds, hp, hx⟩ := Finset.mem_filter.mp hx
    exact ⟨hF, ds, direction_unused_of_onLine hE hA hp, hp, hx⟩
  · rintro ⟨hF, ds, _, hp, hx⟩
    exact Finset.mem_filter.mpr ⟨hF, ds, hp, hx⟩

end
end Balanced.Local.PrescribedGeometry

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalParentMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ParentMap

noncomputable section
open scoped Classical

theorem endpointIndex_injective (r : Fin 4) (σ : Bool) :
    Function.Injective (endpointIndex r σ) := by
  intro t u h
  fin_cases r <;> cases σ <;> cases t <;> cases u <;>
    simp_all [endpointIndex]

theorem endpointIndex_eq_or (r : Fin 4) (σ t : Bool) :
    endpointIndex r σ t = r ∨ endpointIndex r σ t = r - 1 := by
  unfold endpointIndex
  split_ifs <;> simp

variable {b : ℕ}

theorem sub_one_ne (s : Fin 4) : s - 1 ≠ s := by
  fin_cases s <;> decide

theorem underlying_injective_on_dependent (root child : Fin b) (r s : Fin 4)
    (σ τ : Bool) : Set.InjOn (underlying root child r s σ τ) (dependent child s) := by
  intro ij hij kl hkl heq
  simp only [dependent, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hij hkl
  rcases hij with rfl | rfl <;> rcases hkl with rfl | rfl
  · rfl
  · rw [underlying_first, underlying_second] at heq
    have h := endpointIndex_injective r σ (congrArg Prod.snd heq)
    cases τ <;> contradiction
  · rw [underlying_first, underlying_second] at heq
    have h := endpointIndex_injective r σ (congrArg Prod.snd heq)
    cases τ <;> contradiction
  · rfl

theorem two_anchors_not_both_self (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    {v x y : Fin b × Fin 4}
    (hx : x ≠ v) (hy : y ≠ v) (hxy : x ≠ y) :
    underlying root child r s σ τ x ≠ v ∨
      underlying root child r s σ τ y ≠ v := by
  by_contra h
  simp only [not_or, not_not] at h
  have hxd : x ∈ dependent child s := by
    by_contra hxd
    exact hx ((underlying_fixed root child r s σ τ hxd).symm.trans h.1)
  have hyd : y ∈ dependent child s := by
    by_contra hyd
    exact hy ((underlying_fixed root child r s σ τ hyd).symm.trans h.2)
  exact hxy (underlying_injective_on_dependent root child r s σ τ hxd hyd
    (h.1.trans h.2.symm))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)

theorem endpoint_purposeful (i : Fin b) (r : Fin 4) (t : Bool) :
    AnchorExclusion.Purposeful P (P.classOf i r)
      (i, endpointIndex r (bits i r) t) := by
  rcases endpointIndex_eq_or r (bits i r) t with h | h
  · left
    simp only [h]
  · right
    simp only [h, sub_add_cancel]

omit [Fintype F] [DecidableEq F] in

theorem same_underlying_shared_constituent (ha : Eligible P a)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (hm : underlying root child r s (bits root r) (bits child s) x = v) :
    AnchorExclusion.Purposeful P (P.classOf root r) v ∧
      ∃ t : Bool,
        OnLine (prescribedPoint P a bits M v)
          (constituent M (a.2 (P.classOf root r)) t) ∧
        OnLine (prescribedPoint P a bits M x)
          (constituent M (a.2 (P.classOf root r)) t) := by
  have hxd : x ∈ dependent child s := by
    by_contra hxd
    exact hx ((underlying_fixed root child r s (bits root r) (bits child s) hxd).symm.trans hm)
  simp only [dependent, Finset.mem_insert, Finset.mem_singleton] at hxd
  rcases hxd with rfl | rfl
  · rw [underlying_first] at hm
    subst v
    refine ⟨endpoint_purposeful P bits root r (bits child s), bits child s,
      endpoint_on_constituent P a bits M ha root r (bits child s), ?_⟩
    simpa only [hshared] using
      PrescribedGeometry.prescribedPoint_on_left (M := M) ha child s
  · rw [underlying_second] at hm
    subst v
    refine ⟨endpoint_purposeful P bits root r (!(bits child s)), !(bits child s),
      endpoint_on_constituent P a bits M ha root r (!(bits child s)), ?_⟩
    simpa only [sub_add_cancel, hshared] using
      PrescribedGeometry.prescribedPoint_on_right (M := M) ha child (s - 1)

theorem ordinary_anchor_not_self (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (l : Line F) (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    (hvl : OnLine (prescribedPoint P a bits M v) l)
    (hxl : OnLine (prescribedPoint P a bits M x) l) :
    underlying root child r s (bits root r) (bits child s) x ≠ v := by
  intro hm
  obtain ⟨_, t, hvt, hxt⟩ :=
    same_underlying_shared_constituent P a bits M ha root child r s hshared hv hx hm
  exact AnchorExclusion.ordinary_line_no_shared_constituent P a bits M p hA l hl
    hx.symm (a.2 (P.classOf root r)) t hvt hxt ⟨hvl, hxl⟩

theorem used_pair_anchor_not_self (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (c : Fin (4 * b - κ)) (t : Bool)
    (hnc : ¬ AnchorExclusion.Purposeful P c v)
    (hvc : OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t))
    (hxc : OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t)) :
    underlying root child r s (bits root r) (bits child s) x ≠ v := by
  intro hm
  obtain ⟨he, u, hvu, hxu⟩ :=
    same_underlying_shared_constituent P a bits M ha root child r s hshared hv hx hm
  exact AnchorExclusion.used_pair_no_self_anchor P a bits M ha p hA hx.symm
    c (P.classOf root r) t u hnc he hvu hxu ⟨hvc, hxc⟩

end
end Balanced.Local.ParentMap

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedPointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition AlignedUnused

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem PointSystem.generated_points {b κ : ℕ} {P : EqualityPattern b κ}
    {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}
    {R : Finset (Fin b)} (S : PointSystem P a bits p R)
    (hκ : κ ≤ 2) (hD : (dependentOccurrences P R).card = 2*κ) (ha : Eligible P a)
    (z : (FreeIndex P R → F) × UnusedArray P a) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ij =
      S.point ij (z.1 (S.underlying ij)) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  have hcoord := congrFun (congrArg Prod.fst (e.apply_symm_apply z)) (S.underlying ij)
  exact (S.realizes (e.symm z) ij).trans (congrArg (S.point ij) hcoord)

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem classUseCount_pos (P : EqualityPattern b κ) (c : Fin (4 * b - κ)) :
    0 < classUseCount P c := by
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass c
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hij⟩⟩⟩

theorem sum_classUseCount (P : EqualityPattern b κ) :
    ∑ c, classUseCount P c = 4 * b := by
  simp only [classUseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hi (i : Fin b) :
      (∑ c : Fin (4 * b - κ), if ∃ j, P.classOf i j = c then 1 else 0) = 4 := by
    have hs : (Finset.univ.filter (fun c => ∃ j, P.classOf i j = c)) =
        Finset.univ.image (P.classOf i) := by
      ext c
      simp
    have hc := Finset.card_image_of_injective (Finset.univ : Finset (Fin 4))
      (P.withinTuple i)
    rw [← hs] at hc
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  simp_rw [hi]
  simp [Nat.mul_comm]

theorem sum_class_excess (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    ∑ c, (classUseCount P c - 1) = κ := by
  rw [Finset.sum_tsub_distrib]
  · rw [sum_classUseCount]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    omega
  · intro c _
    exact classUseCount_pos P c

omit [Field F] [Fintype F] in
theorem usingTuples_eq_empty_of_not_used (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (d : Direction F)
    (hd : d ∉ usedDirections a) : usingTuples P a d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
  exact hd (Finset.mem_image.mpr ⟨P.classOf i j, Finset.mem_univ _, hj⟩)

omit [Field F] in

theorem sum_direction_excess (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (hκ : κ ≤ 4 * b) :
    ∑ d : Direction F, ((usingTuples P a d).card - 1) = κ := by
  have hrestrict :
      (∑ d : Direction F, ((usingTuples P a d).card - 1)) =
        ∑ d ∈ usedDirections a, ((usingTuples P a d).card - 1) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d _ hd
    simp [usingTuples_eq_empty_of_not_used P a d hd]
  rw [hrestrict, usedDirections, Finset.sum_image]
  · simp_rw [usingTuples_class_card P a ha]
    exact sum_class_excess P hκ
  · intro c _ e _ hce
    exact ha hce

end
end Balanced.Local.FourEvents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

theorem exists_retained_subset {α : Type*} [DecidableEq α]
    (U P : Finset α) (c : ℕ) (hPU : P ⊆ U) (hPc : P.card ≤ c) :
    ∃ R : Finset α, P ⊆ R ∧ R ⊆ U ∧ R.card = min c U.card := by
  exact Finset.exists_subsuperset_card_eq hPU
    (le_min hPc (Finset.card_le_card hPU)) (min_le_right _ _)

theorem exists_retained_fibres {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (A : Finset β) (f : α → Option β)
    (P : β → Finset α) (c : β → ℕ)
    (hP : ∀ a ∈ A, P a ⊆ U.filter (fun x => f x = some a))
    (hPc : ∀ a ∈ A, (P a).card ≤ c a) :
    ∃ R : β → Finset α, ∀ a ∈ A,
      P a ⊆ R a ∧ R a ⊆ U.filter (fun x => f x = some a) ∧
      (R a).card = min (c a) (U.filter (fun x => f x = some a)).card := by
  have h : ∀ a, ∃ R : Finset α, a ∈ A →
      P a ⊆ R ∧ R ⊆ U.filter (fun x => f x = some a) ∧
      R.card = min (c a) (U.filter (fun x => f x = some a)).card := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨R, hR⟩ := exists_retained_subset _ _ _ (hP a ha) (hPc a ha)
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h => False.elim (ha h)⟩
  choose R hR using h
  exact ⟨R, hR⟩

theorem surplus_not_protected {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (P R : β → Finset α)
    (hP : ∀ a ∈ A, P a ⊆ R a) {a : β} (ha : a ∈ A)
    {x : α} (hx : x ∈ U \ A.biUnion R) : x ∉ P a := by
  intro hp
  exact (Finset.mem_sdiff.mp hx).2
    (Finset.mem_biUnion.mpr ⟨a, ha, hP a ha hp⟩)

theorem card_surplus_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (hR : ∀ a ∈ A, (R a).card ≤ c a) :
    U.card - ∑ a ∈ A, c a ≤ (U \ A.biUnion R).card := by
  have hret : (A.biUnion R).card ≤ ∑ a ∈ A, c a :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum hR)
  have hdiff := Finset.card_sdiff_add_card_inter U (A.biUnion R)
  have hinter := Finset.card_le_card (Finset.inter_subset_right :
    U ∩ A.biUnion R ⊆ A.biUnion R)
  omega

theorem source_surplus_card_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (b κ : ℕ) (hb : 1 ≤ b) (hU : U.card = 4 * b)
    (hA : A.card ≤ b - 1) (hR : ∀ a ∈ A, (R a).card ≤ c a)
    (hcap : (∑ a ∈ A, c a) ≤ 2 * A.card + 2 * κ) :
    2 * b + 2 - 2 * κ ≤ (U \ A.biUnion R).card := by
  have h := card_surplus_ge U A R c hR
  omega

theorem source_independent_surplus_card_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (D : Finset α) (b κ : ℕ) (hb : 1 ≤ b) (hU : U.card = 4 * b)
    (hA : A.card ≤ b - 1) (hR : ∀ a ∈ A, (R a).card ≤ c a)
    (hcap : (∑ a ∈ A, c a) ≤ 2 * A.card + 2 * κ)
    (hD : D.card ≤ 2 * κ) :
    2 * b + 2 - 4 * κ ≤ ((U \ A.biUnion R) \ D).card := by
  have h := source_surplus_card_ge U A R c b κ hb hU hA hR hcap
  have hdiff := Finset.card_sdiff_add_card_inter (U \ A.biUnion R) D
  have hinter := Finset.card_le_card (Finset.inter_subset_right :
    (U \ A.biUnion R) ∩ D ⊆ D)
  omega

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PurposefulIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

theorem purposeful_positions_card_le {α : Type*} [DecidableEq α] (f : Fin 4 → α)
    (hf : Function.Injective f) (c : α) :
    (Finset.univ.filter (fun i => f i = c ∨ f (i + 1) = c)).card ≤
      if ∃ i, f i = c then 2 else 0 := by
  by_cases hc : ∃ i, f i = c
  · simp only [hc, ite_true]
    obtain ⟨j, hj⟩ := hc
    have hsub : Finset.univ.filter (fun i => f i = c ∨ f (i + 1) = c) ⊆
        {j, j - 1} := by
      intro i hi
      obtain hi | hi := (Finset.mem_filter.mp hi).2
      · exact Finset.mem_insert.mpr (Or.inl (hf (hi.trans hj.symm)))
      · have hnext : i + 1 = j := hf (hi.trans hj.symm)
        have hprev : i = j - 1 := (eq_sub_iff_add_eq).mpr hnext
        simp [hprev]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp only [hc, ite_false]
    apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain hi | hi := (Finset.mem_filter.mp hi).2
    · exact hc ⟨i, hi⟩
    · exact hc ⟨i + 1, hi⟩

theorem purposefulDirections_card_le {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : Function.Injective a.2) (d : Direction F) :
    (purposefulDirections P a d).card ≤
      2 * (Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)).card := by
  have hsum : (purposefulDirections P a d).card =
      ∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        a.2 (P.classOf i j) = d ∨ a.2 (P.classOf i (j + 1)) = d)).card := by
    simp only [purposefulDirections, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  calc
    (∑ i : Fin b, (Finset.univ.filter (fun j : Fin 4 =>
        a.2 (P.classOf i j) = d ∨ a.2 (P.classOf i (j + 1)) = d)).card) ≤
        ∑ i : Fin b, if ∃ j, a.2 (P.classOf i j) = d then 2 else 0 :=
      Finset.sum_le_sum (fun i _ => purposeful_positions_card_le
        (fun j => a.2 (P.classOf i j)) (ha.comp (P.withinTuple i)) d)
    _ = 2 * (Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalCoverMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
  (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
  (M : MergedPairs F)

theorem badCover_exists_assignment (hbad : BadCover P a bits p M) :
    ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
      (∀ L ∈ A, AllowedPiece a p M L) ∧
      Nonempty (CoverAssignment P a bits p M A) := by
  obtain ⟨A, hA, hallowed, hcover⟩ := hbad
  have hex : ∀ ij : Fin b × Fin 4, ∃ z : Option (LocalPiece F),
      (z = none ↔ prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M) ∧
      (∀ L, z = some L → L ∈ A ∧
        prescribedPoint P a bits M ij ∈ piecePoints M L) := by
    intro ij
    by_cases hp : prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M
    · exact ⟨none, by simp [hp]⟩
    · have hdesignated : prescribedPoint P a bits M ij ∈
          prescribedDesignated P a bits M :=
        Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
      have hmem := Finset.mem_union.mp (hcover hdesignated)
      obtain ⟨L, hLA, hpL⟩ := Finset.mem_biUnion.mp (hmem.resolve_left hp)
      refine ⟨some L, by simp [hp], ?_⟩
      intro L' heq
      have hLL : L = L' := Option.some.inj heq
      subst L'
      exact ⟨hLA, hpL⟩
  choose f hf using hex
  exact ⟨A, hA, hallowed, ⟨⟨f, fun ij => (hf ij).1,
    fun ij L hL => (hf ij).2 L hL⟩⟩⟩

omit [Field F] [DecidableEq F] in

theorem sum_pieceExtra_le (A : Finset (LocalPiece F)) (t : Direction F → ℕ) :
    (∑ L ∈ A, pieceExtra t L) ≤ ∑ d : Direction F, (t d - 1) := by
  calc
    (∑ L ∈ A, pieceExtra t L) ≤ ∑ L : LocalPiece F, pieceExtra t L :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = ∑ d : Direction F, (t d - 1) := by
      simp [pieceExtra, Fintype.sum_sum_type]

omit [Field F] [DecidableEq F] in

theorem sum_pieceCapacity_le (A : Finset (LocalPiece F)) (t : Direction F → ℕ) :
    (∑ L ∈ A, pieceCapacity t L) ≤
      2 * A.card + 2 * ∑ d : Direction F, (t d - 1) := by
  unfold pieceCapacity
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h := Nat.mul_le_mul_left 2 (sum_pieceExtra_le A t)
  simpa [Nat.mul_comm] using Nat.add_le_add_left h (2 * A.card)

theorem protectedFibre_subset {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (L : LocalPiece F) :
    protectedFibre P a bits p M f L ⊆ assignmentFibre P a bits p M f L := by
  rcases L with U | l | d
  · exact Finset.empty_subset _
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

theorem protectedFibre_card_le {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (ha : Function.Injective a.2)
    (L : LocalPiece F) :
    (protectedFibre P a bits p M f L).card ≤
      pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L := by
  rcases L with U | l | d
  · simp [protectedFibre, pieceCapacity, pieceExtra]
  · simp [protectedFibre, pieceCapacity, pieceExtra]
  · have h := purposefulDirections_card_le P a ha d
    have hp := Finset.card_le_card (Finset.inter_subset_right :
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
        purposefulDirections P a d ⊆ purposefulDirections P a d)
    change (assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
      purposefulDirections P a d).card ≤
        2 + 2 * ((FourEvents.usingTuples P a d).card - 1)
    change (purposefulDirections P a d).card ≤
      2 * (FourEvents.usingTuples P a d).card at h
    omega

theorem badCover_exists_marked_surplus (hb : 1 ≤ b) (hκ : κ ≤ 4 * b)
    (ha : Eligible P a) (hbad : BadCover P a bits p M) :
    ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
      (∀ L ∈ A, AllowedPiece a p M L) ∧
      ∃ f : CoverAssignment P a bits p M A,
      ∃ R : LocalPiece F → Finset (Fin b × Fin 4),
        (∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
          R L ⊆ assignmentFibre P a bits p M f L ∧
          (R L).card = min
            (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
            (assignmentFibre P a bits p M f L).card) ∧
        2 * b + 2 - 2 * κ ≤
          ((Finset.univ : Finset (Fin b × Fin 4)) \ A.biUnion R).card ∧
        (∀ D : Finset (Fin b × Fin 4), D.card ≤ 2 * κ →
          2 * b + 2 - 4 * κ ≤ ((Finset.univ \ A.biUnion R) \ D).card) := by
  obtain ⟨A, hA, hallowed, ⟨f⟩⟩ := badCover_exists_assignment P a bits p M hbad
  let t : Direction F → ℕ := fun d => (FourEvents.usingTuples P a d).card
  obtain ⟨R, hR⟩ := exists_retained_fibres Finset.univ A f.piece
    (protectedFibre P a bits p M f) (pieceCapacity t)
    (fun L _ => protectedFibre_subset P a bits p M f L)
    (fun L _ => protectedFibre_card_le P a bits p M f ha.2.1 L)
  have hRcard : ∀ L ∈ A, (R L).card ≤ pieceCapacity t L := by
    intro L hL
    exact (hR L hL).2.2.trans_le (min_le_left _ _)
  have hcap : (∑ L ∈ A, pieceCapacity t L) ≤ 2 * A.card + 2 * κ := by
    have h := sum_pieceCapacity_le A t
    simpa only [t, FourEvents.sum_direction_excess P a ha.2.1 hκ] using h
  have hU : (Finset.univ : Finset (Fin b × Fin 4)).card = 4 * b := by
    simp [Nat.mul_comm]
  refine ⟨A, hA, hallowed, f, R, hR, ?_, ?_⟩
  · exact source_surplus_card_ge Finset.univ A R (pieceCapacity t) b κ hb hU
      hA hRcard hcap
  · intro D hD
    exact source_independent_surplus_card_ge Finset.univ A R (pieceCapacity t)
      D b κ hb hU hA hRcard hcap hD

theorem assigned_merged_surplus_nonpurposeful {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L)
    (d : Direction F) (ij : Fin b × Fin 4)
    (hf : f.piece ij = some (Sum.inr (Sum.inr d)))
    (hij : ij ∈ Finset.univ \ A.biUnion R) :
    ij ∉ purposefulDirections P a d := by
  intro hp
  have hA := (f.covered ij _ hf).1
  apply surplus_not_protected Finset.univ A
    (protectedFibre P a bits p M f) R hR hA hij
  exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hp⟩

theorem assignmentFibre_small_card_le {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (hadm : Admissible P a bits p M)
    (U : Finset (Point F)) (hU : U.card ≤ 2) :
    (assignmentFibre P a bits p M f (Sum.inl U)).card ≤ 2 := by
  have hsub : (assignmentFibre P a bits p M f (Sum.inl U)).image
      (prescribedPoint P a bits M) ⊆ U := by
    intro x hx
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hx
    exact (f.covered ij _ (Finset.mem_filter.mp hij).2).2
  have hc := Finset.card_image_of_injective
    (assignmentFibre P a bits p M f (Sum.inl U)) hadm.2.1
  rw [← hc]
  exact (Finset.card_le_card hsub).trans hU

theorem retained_eq_fibre_of_fits {α : Type*} [DecidableEq α]
    (R U : Finset α) (c : ℕ) (hR : R ⊆ U)
    (hcard : R.card = min c U.card) (hfit : U.card ≤ c) : R = U := by
  apply Finset.eq_of_subset_of_card_le hR
  rw [hcard, min_eq_right hfit]

theorem small_piece_not_surplus {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (hadm : Admissible P a bits p M)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (U : Finset (Point F)) (hU : U.card ≤ 2)
    (hR : R (Sum.inl U) ⊆ assignmentFibre P a bits p M f (Sum.inl U))
    (hcard : (R (Sum.inl U)).card =
      min 2 (assignmentFibre P a bits p M f (Sum.inl U)).card)
    (ij : Fin b × Fin 4) (hf : f.piece ij = some (Sum.inl U)) :
    ij ∉ Finset.univ \ A.biUnion R := by
  intro hij
  have heq := retained_eq_fibre_of_fits _ _ 2 hR hcard
    (assignmentFibre_small_card_le P a bits p M f hadm U hU)
  apply (Finset.mem_sdiff.mp hij).2
  apply Finset.mem_biUnion.mpr
  refine ⟨Sum.inl U, (f.covered ij _ hf).1, ?_⟩
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_LocalMarkedAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.MarkedAnchors

noncomputable section
open scoped Classical
open Surplus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

omit [Field F] [Fintype F] [DecidableEq F] in

theorem marked_not_retained {A : Finset (LocalPiece F)}
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    {L : LocalPiece F} (hL : L ∈ A) {v : Fin b × Fin 4}
    (hv : v ∈ Finset.univ \ A.biUnion R) : v ∉ R L := by
  intro hvr
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨L, hL, hvr⟩)

theorem retained_pair_of_marked {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (L : LocalPiece F)
    (hR : R L ⊆ assignmentFibre P a bits p M f L)
    (hcard : (R L).card = min 2 (assignmentFibre P a bits p M f L).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some L)
    (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ x ∈ R L, ∃ y ∈ R L, x ≠ y ∧ x ≠ v ∧ y ≠ v := by
  have hn := marked_not_retained R (f.covered v L hf).1 hv
  have hfv : v ∈ assignmentFibre P a bits p M f L :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have hbig : 2 < (assignmentFibre P a bits p M f L).card := by
    by_contra h
    have heq := retained_eq_fibre_of_fits _ _ 2 hR hcard (by omega)
    exact hn (heq.symm ▸ hfv)
  have htwo : (R L).card = 2 := by
    rw [hcard, min_eq_left (by omega)]
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < (R L).card by omega)
  exact ⟨x, hx, y, hy, hxy, fun h => hn (h ▸ hx), fun h => hn (h ▸ hy)⟩

theorem retained_mem_piece {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (L : LocalPiece F)
    (hR : R L ⊆ assignmentFibre P a bits p M f L)
    {x : Fin b × Fin 4} (hx : x ∈ R L) :
    prescribedPoint P a bits M x ∈ piecePoints M L :=
  (f.covered x L (Finset.mem_filter.mp (hR hx)).2).2

theorem ordinary_marked_anchors {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (l : Line F) (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    (hR : R (Sum.inr (Sum.inl l)) ⊆
      assignmentFibre P a bits p M f (Sum.inr (Sum.inl l)))
    (hcard : (R (Sum.inr (Sum.inl l))).card =
      min 2 (assignmentFibre P a bits p M f (Sum.inr (Sum.inl l))).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inl l)))
    (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ x ∈ R (Sum.inr (Sum.inl l)), ∃ y ∈ R (Sum.inr (Sum.inl l)),
      x ≠ y ∧ prescribedPoint P a bits M x ≠ prescribedPoint P a bits M y ∧
      OnLine (prescribedPoint P a bits M x) l ∧
      OnLine (prescribedPoint P a bits M y) l ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) y ≠ v := by
  obtain ⟨x, hx, y, hy, hxy, hxv, hyv⟩ :=
    retained_pair_of_marked P a bits p M f R _ hR hcard v hf hv
  have hvl : OnLine (prescribedPoint P a bits M v) l :=
    (Finset.mem_filter.mp (f.covered v _ hf).2).2
  have hxl : OnLine (prescribedPoint P a bits M x) l :=
    (Finset.mem_filter.mp (retained_mem_piece P a bits p M f R _ hR hx)).2
  have hyl : OnLine (prescribedPoint P a bits M y) l :=
    (Finset.mem_filter.mp (retained_mem_piece P a bits p M f R _ hR hy)).2
  exact ⟨x, hx, y, hy, hxy, fun h => hxy (hadm.2.1 h), hxl, hyl,
    ParentMap.ordinary_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hxv l hl hvl hxl,
    ParentMap.ordinary_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hyv l hl hvl hyl⟩

theorem unused_marked_anchor {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (root child : Fin b) (r s : Fin 4)
    (d : Direction F) (hd : d ∉ FourEvents.usedDirections a)
    (hR : R (Sum.inr (Sum.inr d)) ⊆
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)))
    (hcard : (R (Sum.inr (Sum.inr d))).card =
      min (pieceCapacity (fun e => (FourEvents.usingTuples P a e).card)
        (Sum.inr (Sum.inr d)))
        (assignmentFibre P a bits p M f (Sum.inr (Sum.inr d))).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inr d)))
    (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ x ∈ R (Sum.inr (Sum.inr d)), x ≠ v ∧
      prescribedPoint P a bits M x ∈ mergedPoints M d ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v := by
  have hcap : pieceCapacity (fun e => (FourEvents.usingTuples P a e).card)
      (Sum.inr (Sum.inr d)) = 2 := by
    simp [pieceCapacity, pieceExtra, FourEvents.usingTuples_eq_empty_of_not_used P a d hd]
  rw [hcap] at hcard
  obtain ⟨x, hx, y, hy, hxy, hxv, hyv⟩ :=
    retained_pair_of_marked P a bits p M f R _ hR hcard v hf hv
  rcases ParentMap.two_anchors_not_both_self root child r s
      (bits root r) (bits child s) hxv hyv hxy with hnx | hny
  · exact ⟨x, hx, hxv, retained_mem_piece P a bits p M f R _ hR hx, hnx⟩
  · exact ⟨y, hy, hyv, retained_mem_piece P a bits p M f R _ hR hy, hny⟩

omit [Fintype F] [DecidableEq F] in

theorem exists_purposeful_endpoint (ha : Eligible P a)
    (c : Fin (4 * b - κ)) (t : Bool) :
    ∃ x : Fin b × Fin 4, AnchorExclusion.Purposeful P c x ∧
      OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t) := by
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass c
  refine ⟨(i, ParentMap.endpointIndex j (bits i j) t), ?_, ?_⟩
  · simpa only [hij] using ParentMap.endpoint_purposeful P bits i j t
  · simpa only [hij] using ParentMap.endpoint_on_constituent P a bits M ha i j t

theorem used_marked_anchor {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L)
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (c : Fin (4 * b - κ))
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inr (a.2 c))))
    (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ t : Bool, ∃ x : Fin b × Fin 4,
      AnchorExclusion.Purposeful P c x ∧ x ≠ v ∧
      OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t) ∧
      OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t) ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v := by
  have hnp : ¬ AnchorExclusion.Purposeful P c v := by
    intro hp
    exact assigned_merged_surplus_nonpurposeful P a bits p M f R hR (a.2 c) v hf hv
      ((mem_purposefulDirections P a ha.2.1 c v).mpr hp)
  have hvm : prescribedPoint P a bits M v ∈ mergedPoints M (a.2 c) :=
    (f.covered v _ hf).2
  have ht : ∃ t : Bool,
      OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t) := by
    simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.exists_bool] using hvm
  obtain ⟨t, hvt⟩ := ht
  obtain ⟨x, hxp, hxt⟩ := exists_purposeful_endpoint P a bits M ha c t
  have hxv : x ≠ v := fun h => hnp (h ▸ hxp)
  exact ⟨t, x, hxp, hxv, hvt, hxt,
    ParentMap.used_pair_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hxv c t hnp hvt hxt⟩

theorem constituent_ne_target (hadm : Admissible P a bits p M)
    (d : Direction F) (t : Bool) (v : Fin b × Fin 4) :
    constituent M d t ≠ lineThrough (a.1 v.1) p := by
  intro heq
  apply hadm.2.2.2.1 v.1
  rw [← heq]
  exact Finset.mem_image.mpr ⟨(d, t), Finset.mem_univ _, rfl⟩

theorem ordinary_ne_target (l : Line F)
    (hl : AllowedPiece a p M (Sum.inr (Sum.inl l))) (v : Fin b × Fin 4) :
    l ≠ lineThrough (a.1 v.1) p := by
  intro heq
  apply hl
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨v.1, Finset.mem_univ _, heq.symm⟩)

end
end Balanced.Local.MarkedAnchors

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConditionSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open Surplus MarkedAnchors

theorem anchors_card_le_two {b κ : ℕ} (z : Code b κ) : (anchors z).card ≤ 2 := by
  rcases z with _ | xy | x | cx
  · simp [anchors]
  · exact Finset.card_le_two
  · simp [anchors]
  · simp [anchors]

theorem underlyingAnchors_card_le_two {b κ : ℕ} (u : Position b → Position b)
    (z : Code b κ) : (underlyingAnchors u z).card ≤ 2 :=
  Finset.card_image_le.trans (anchors_card_le_two z)

theorem card_code (b κ : ℕ) :
    Fintype.card (Code b κ) = 1 + (4 * b) ^ 2 + 4 * b + (4 * b - κ) * (4 * b) := by
  simp only [Code, Position, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_unit, Fintype.card_fin]
  ring

theorem card_code_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Code b κ) ≤ 37 * b ^ 2 := by
  rw [card_code]
  have hκ : 4 * b - κ ≤ 4 * b := Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_right (4 * b) hκ
  nlinarith [Nat.mul_self_le_mul_self hb]

theorem card_test_code_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Position b × Code b κ) ≤ 148 * b ^ 3 := by
  rw [Fintype.card_prod]
  have h := Nat.mul_le_mul_left (4 * b) (card_code_le b κ hb)
  simpa [Position, Nat.mul_comm, Nat.mul_left_comm, pow_succ, Nat.mul_assoc] using h

theorem card_specifications_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Fin (3 - κ) → Position b × Code b κ) ≤ (148 * b ^ 3) ^ 3 := by
  rw [Fintype.card_fun, Fintype.card_fin]
  apply (Nat.pow_le_pow_left (card_test_code_le b κ hb) (3 - κ)).trans
  exact Nat.pow_le_pow_right (by positivity) (Nat.sub_le _ _)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

theorem marked_exists_spec {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Position b))
    (hallowed : ∀ L ∈ A, AllowedPiece a p M L)
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
      R L ⊆ assignmentFibre P a bits p M f L ∧
      (R L).card = min
        (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
        (assignmentFibre P a bits p M f L).card)
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (v : Position b) (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ z : Code b κ, Holds P a bits p M v z ∧
      v ∉ underlyingAnchors
        (ParentMap.underlying root child r s (bits root r) (bits child s)) z := by
  cases hfv : f.piece v with
  | none =>
      have hp := (f.precovered v).mp hfv
      obtain ⟨_, ⟨d, t⟩, hd, hpt, hvt⟩ :=
        (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm _).mp hp
      refine ⟨Sum.inl (), ?_, by simp [underlyingAnchors, anchors]⟩
      exact ⟨d, hd, t, hpt, hvt, constituent_ne_target P a bits p M hadm d (!t) v⟩
  | some L =>
      have hLA := (f.covered v L hfv).1
      have hret := hR L hLA
      rcases L with U | l | d
      · exact False.elim (small_piece_not_surplus P a bits p M f hadm R U
          (hallowed _ hLA) hret.2.1 hret.2.2 v hfv hv)
      · obtain ⟨x, hx, y, hy, hxy, hpoints, hxl, hyl, hnx, hny⟩ :=
          ordinary_marked_anchors P a bits p M f R ha hadm root child r s hshared
            l (hallowed _ hLA) hret.2.1 hret.2.2 v hfv hv hvd
        have hvl : OnLine (prescribedPoint P a bits M v) l :=
          (Finset.mem_filter.mp (f.covered v _ hfv).2).2
        have heq : joiningLine (prescribedPoint P a bits M x)
            (prescribedPoint P a bits M y) = l :=
          (eq_of_two_common_points _ _ hpoints l _ hxl hyl
            (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)).symm
        refine ⟨Sum.inr (Sum.inl (x, y)), ?_, ?_⟩
        · change _ ∧ _ ∧ _
          rw [heq]
          exact ⟨hpoints, hvl, ordinary_ne_target a p M l (hallowed _ hLA) v⟩
        · simpa [underlyingAnchors, anchors, eq_comm] using And.intro hnx hny
      · by_cases hd : d ∈ FourEvents.usedDirections a
        · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
          obtain ⟨t, x, hxp, hxv, hvt, hxt, hnx⟩ :=
            used_marked_anchor P a bits p M f R (fun L hL => (hR L hL).1)
              ha hadm root child r s hshared c v hfv hv hvd
          have heq : lineThrough (a.2 c) (prescribedPoint P a bits M x) =
              constituent M (a.2 c) t := (line_eq_lineThrough _ _ hxt).symm
          refine ⟨Sum.inr (Sum.inr (Sum.inr (c, x))), ?_, ?_⟩
          · change _ ∧ _
            rw [heq]
            exact ⟨hvt, constituent_ne_target P a bits p M hadm (a.2 c) t v⟩
          · simpa [underlyingAnchors, anchors, eq_comm] using hnx
        · obtain ⟨x, hx, hxv, hxm, hnx⟩ :=
            unused_marked_anchor P a bits p M f R root child r s d hd
              hret.2.1 hret.2.2 v hfv hv
          have hvm : prescribedPoint P a bits M v ∈ mergedPoints M d :=
            (f.covered v _ hfv).2
          have ht : ∃ t : Bool,
              OnLine (prescribedPoint P a bits M v) (constituent M d t) := by
            simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
              Finset.mem_univ, true_and, Bool.exists_bool] using hvm
          obtain ⟨t, hvt⟩ := ht
          refine ⟨Sum.inr (Sum.inr (Sum.inl x)), ?_, ?_⟩
          · exact ⟨d, hd, hxm, t, hvt, constituent_ne_target P a bits p M hadm d t v⟩
          · simpa [underlyingAnchors, anchors, eq_comm] using hnx

theorem underlying_diagonal (i : Fin b) (s : Fin 4) (t : Bool) (x : Position b) :
    ParentMap.underlying i i s s t t x = x := by
  cases t <;> simp only [ParentMap.underlying, ParentMap.endpointIndex,
    Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, Bool.true_eq_false, ite_false]
  all_goals split_ifs <;> simp_all

theorem marked_exists_identity_spec {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Position b))
    (hallowed : ∀ L ∈ A, AllowedPiece a p M L)
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
      R L ⊆ assignmentFibre P a bits p M f L ∧
      (R L).card = min
        (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
        (assignmentFibre P a bits p M f L).card)
    (hb : 3 ≤ b) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (v : Position b) (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ z : Code b κ, Holds P a bits p M v z ∧ v ∉ anchors z := by
  obtain ⟨i, hi, _⟩ := Fin.exists_ne_and_ne_of_two_lt v.1 v.1 (by omega)
  have hvd : v ∉ ParentMap.dependent i 0 := by
    simp [ParentMap.dependent, Prod.ext_iff, hi.symm]
  obtain ⟨z, hz, hn⟩ := marked_exists_spec P a bits p M f R hallowed hR ha hadm
    i i 0 0 rfl v hv hvd
  refine ⟨z, hz, ?_⟩
  simpa [underlyingAnchors, underlying_diagonal] using hn

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ForwardDependencyExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ForwardDependencyExtraction

open Finset

theorem exists_forward_coloring {n k : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ k) :
    ∃ c : Fin n → Fin (k + 1),
      ∀ i j, R i j → c i = c j → i < j := by
  classical
  have aux : ∀ m : ℕ, m ≤ n →
      ∃ c : Fin n → Fin (k + 1),
        ∀ i j, i.val < m → j.val < m → R i j → c i = c j → i < j := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨fun _ => 0, by simp⟩
    | succ m ih =>
        intro hm
        obtain ⟨c, hc⟩ := ih (by omega)
        let v : Fin n := ⟨m, by omega⟩
        let earlier : Finset (Fin n) :=
          Finset.univ.filter (fun j => j.val < m ∧ R v j)
        have hearlier : earlier.card ≤ k := by
          calc
            earlier.card ≤ (Finset.univ.filter (R v)).card := by
              apply Finset.card_le_card
              intro j hj
              simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact hj.2
            _ ≤ k := hdegree v
        have hcolors : (earlier.image c).card <
            (Finset.univ : Finset (Fin (k + 1))).card := by
          simpa using (lt_of_le_of_lt (Finset.card_image_le.trans hearlier)
            (Nat.lt_succ_self k))
        obtain ⟨color, _, hcolor⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hcolors
        refine ⟨Function.update c v color, ?_⟩
        intro i j hi hj hij heq
        by_cases hiv : i = v
        · subst i
          by_cases hjv : j = v
          · subst j
            exact False.elim (hloop v hij)
          · have hjm : j.val < m := by
              have hne : j.val ≠ m := by
                intro h
                apply hjv
                exact Fin.ext h
              omega
            have hjearlier : j ∈ earlier := by
              simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hjm, hij⟩
            have hchosen : color = c j := by
              simpa [Function.update, hjv] using heq
            exact False.elim (hcolor (hchosen ▸ Finset.mem_image_of_mem c hjearlier))
        · by_cases hjv : j = v
          · subst j
            have him : i.val < m := by
              have hne : i.val ≠ m := by
                intro h
                apply hiv
                exact Fin.ext h
              omega
            exact him
          · have him : i.val < m := by
              have hne : i.val ≠ m := by
                intro h
                apply hiv
                exact Fin.ext h
              omega
            have hjm : j.val < m := by
              have hne : j.val ≠ m := by
                intro h
                apply hjv
                exact Fin.ext h
              omega
            apply hc i j him hjm hij
            simpa [Function.update, hiv, hjv] using heq
  obtain ⟨c, hc⟩ := aux n le_rfl
  exact ⟨c, fun i j => hc i j i.isLt j.isLt⟩

theorem exists_forward_subset {n k t : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ k)
    (hsize : (k + 1) * (t - 1) < n) :
    ∃ s : Finset (Fin n), t ≤ s.card ∧
      ∀ i ∈ s, ∀ j ∈ s, R i j → i < j := by
  classical
  obtain ⟨c, hc⟩ := exists_forward_coloring R hloop hdegree
  obtain ⟨color, hcolor⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card c (by simpa using hsize)
  refine ⟨Finset.univ.filter (fun i => c i = color), by omega, ?_⟩
  intro i hi j hj hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hc i j hij (hi.trans hj.symm)

end Balanced.ForwardDependencyExtraction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SurplusAcyclic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped Classical

theorem exists_acyclic_subset_finset {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (k t : ℕ)
    (hloop : ∀ x ∈ S, ¬ R x x)
    (hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ k)
    (hsize : (k + 1) * (t - 1) < S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = t ∧
      WellFounded (fun x y : {x // x ∈ T} => R x.val y.val) := by
  let e := Fintype.equivFin {x // x ∈ S}
  let g : Fin (Fintype.card {x // x ∈ S}) → α := fun j => (e.symm j).val
  have hg : Function.Injective g := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let R' := fun i j => R (g i) (g j)
  have hloop' : ∀ i, ¬ R' i i := fun i => hloop (g i) (e.symm i).property
  have hdegree' : ∀ i, (Finset.univ.filter (R' i)).card ≤ k := by
    intro i
    have hmap : (Finset.univ.filter (R' i)).image g ⊆ S.filter (R (g i)) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨(e.symm j).property, (Finset.mem_filter.mp hj).2⟩
    have hc := Finset.card_image_of_injective (Finset.univ.filter (R' i)) hg
    rw [← hc]
    exact (Finset.card_le_card hmap).trans (hdegree (g i) (e.symm i).property)
  obtain ⟨V, hVcard, hforward⟩ :=
    ForwardDependencyExtraction.exists_forward_subset R' hloop' hdegree'
      (by simpa using hsize)
  obtain ⟨W, hWV, hWcard⟩ := Finset.exists_subset_card_eq hVcard
  let T := W.image g
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact (e.symm j).property
  have hTcard : T.card = t := by
    change (W.image g).card = t
    rw [Finset.card_image_of_injective _ hg, hWcard]
  let rank : {x // x ∈ T} → Fin (Fintype.card {x // x ∈ S}) :=
    fun x => e ⟨x.val, hTS x.property⟩
  have hrank : ∀ x, rank x ∈ W := by
    intro x
    obtain ⟨j, hj, hgx⟩ := Finset.mem_image.mp x.property
    have heq : rank x = j := by
      apply e.symm.injective
      apply Subtype.ext
      simpa only [rank, Equiv.symm_apply_apply] using hgx.symm
    rwa [heq]
  refine ⟨T, hTS, hTcard, ?_⟩
  apply (measure (fun x : {x // x ∈ T} => (rank x).val)).wf.mono
  intro x y hxy
  apply hforward (rank x) (hWV (hrank x)) (rank y) (hWV (hrank y))
  simpa only [R', g, rank, Equiv.symm_apply_apply] using hxy

theorem source_surplus_acyclic {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (b κ : ℕ)
    (hb : 3 ≤ b) (hκ : κ ≤ 1)
    (hcard : 2 * b + 2 - 4 * κ ≤ S.card)
    (hloop : ∀ x ∈ S, ¬ R x x)
    (hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ 2) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = 3 - κ ∧
      WellFounded (fun x y : {x // x ∈ T} => R x.val y.val) := by
  exact exists_acyclic_subset_finset S R 2 (3 - κ) hloop hdegree (by omega)

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAcyclicSpecifications
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open Surplus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

theorem exists_acyclic_codes (S : Finset (Position b))
    (u : Position b → Position b) (hb : 3 ≤ b) (hκ : κ ≤ 1)
    (hcard : 2 * b + 2 - 4 * κ ≤ S.card)
    (hex : ∀ v ∈ S, ∃ z : Code b κ,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z) :
    ∃ (T : Finset (Position b)) (code : Position b → Code b κ),
      T ⊆ S ∧ T.card = 3 - κ ∧
      (∀ v ∈ T, Holds P a bits p M v (code v) ∧
        v ∉ underlyingAnchors u (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} =>
        y.val ∈ underlyingAnchors u (code x.val)) := by
  have hex' : ∀ v : Position b, ∃ z : Code b κ,
      v ∈ S → Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨z, hz⟩ := hex v hv
      exact ⟨z, fun _ => hz⟩
    · exact ⟨Sum.inl (), fun h => False.elim (hv h)⟩
  choose code hcode using hex'
  let R : Position b → Position b → Prop :=
    fun x y => y ∈ underlyingAnchors u (code x)
  have hloop : ∀ x ∈ S, ¬ R x x := fun x hx => (hcode x hx).2
  have hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ 2 := by
    intro x _
    apply (Finset.card_le_card (show S.filter (R x) ⊆
      underlyingAnchors u (code x) from fun y hy => (Finset.mem_filter.mp hy).2)).trans
    exact underlyingAnchors_card_le_two u (code x)
  obtain ⟨T, hTS, hTcard, hTwf⟩ :=
    source_surplus_acyclic S R b κ hb hκ hcard hloop (by
      intro x hx
      convert hdegree x hx using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext y
      simp only [Finset.mem_filter])
  exact ⟨T, code, hTS, hTcard, fun v hv => hcode v (hTS hv), hTwf⟩

theorem badCover_zero_reuse_exists_acyclic_spec
    {b : ℕ} (P : EqualityPattern b 0)
    (a : DirectionAssignment F b 0) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M) :
    ∃ (T : Finset (Position b)) (code : Position b → Code b 0),
      T.card = 3 ∧
      (∀ v ∈ T, Holds P a bits p M v (code v) ∧ v ∉ anchors (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} => y.val ∈ anchors (code x.val)) := by
  obtain ⟨A, hA, hallowed, f, R, hR, hsurplus, _⟩ :=
    badCover_exists_marked_surplus P a bits p M (by omega) (by omega) ha hbad
  let S : Finset (Position b) := Finset.univ \ A.biUnion R
  have hex : ∀ v ∈ S, ∃ z : Code b 0,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors id z := by
    intro v hv
    obtain ⟨z, hz, hn⟩ := marked_exists_identity_spec P a bits p M f R
      hallowed hR hb ha hadm v hv
    exact ⟨z, hz, by simpa [underlyingAnchors] using hn⟩
  have hcard : 2 * b + 2 - 4 * 0 ≤ S.card := by
    simpa only [Nat.mul_zero] using hsurplus
  obtain ⟨T, code, _, hTcard, hT, hwf⟩ :=
    exists_acyclic_codes P a bits p M S id hb (by omega) hcard hex
  refine ⟨T, code, by simpa using hTcard, ?_, ?_⟩
  · simpa only [underlyingAnchors, Finset.image_id] using hT
  · simpa only [underlyingAnchors, Finset.image_id] using hwf

theorem badCover_one_reuse_exists_acyclic_spec
    {b : ℕ} (P : EqualityPattern b 1)
    (a : DirectionAssignment F b 1) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) :
    let u := ParentMap.underlying root child r s (bits root r) (bits child s)
    ∃ (T : Finset (Position b)) (code : Position b → Code b 1),
      T.card = 2 ∧
      (∀ v ∈ T, v ∉ ParentMap.dependent child s ∧
        Holds P a bits p M v (code v) ∧ v ∉ underlyingAnchors u (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} => y.val ∈ underlyingAnchors u (code x.val)) := by
  dsimp only
  let u := ParentMap.underlying root child r s (bits root r) (bits child s)
  obtain ⟨A, hA, hallowed, f, R, hR, _, hdiscard⟩ :=
    badCover_exists_marked_surplus P a bits p M (by omega) (by omega) ha hbad
  let S : Finset (Position b) :=
    (Finset.univ \ A.biUnion R) \ ParentMap.dependent child s
  have hdep : (ParentMap.dependent child s).card ≤ 2 * 1 := by
    simpa only [ParentMap.dependent, Nat.mul_one] using
      (Finset.card_le_two (a := (child, s)) (b := (child, s - 1)))
  have hcard : 2 * b + 2 - 4 * 1 ≤ S.card := hdiscard _ hdep
  have hex : ∀ v ∈ S, ∃ z : Code b 1,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z := by
    intro v hv
    obtain ⟨hvs, hvd⟩ := Finset.mem_sdiff.mp hv
    exact marked_exists_spec P a bits p M f R hallowed hR ha hadm
      root child r s hshared v hvs hvd
  obtain ⟨T, code, hTS, hTcard, hT, hwf⟩ :=
    exists_acyclic_codes P a bits p M S u hb (by omega) hcard hex
  refine ⟨T, code, by simpa using hTcard, ?_, hwf⟩
  intro v hv
  exact ⟨(Finset.mem_sdiff.mp (hTS hv)).2, hT v hv⟩

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_AcyclicProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.DependencyExtraction

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

theorem expect_coordinate_refresh (i : α) (f : (α → β) → ℝ) :
    (𝔼 x, 𝔼 y, f (Function.update x i y)) = 𝔼 x, f x := by
  classical
  have hswap := Fintype.expect_equiv (coordinateSwap (β := β) i)
    (fun z : (α → β) × β => f (Function.update z.1 i z.2))
    (fun z : (α → β) × β => f z.1) (fun _ => rfl)
  have hprod₁ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x y => f (Function.update x i y))
  have hprod₂ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x (_ : β) => f x)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using
    hprod₁.symm.trans (hswap.trans hprod₂)

theorem expect_mul_le_of_coordinate_bound (i : α)
    (f g : (α → β) → ℝ) (p : ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hginv : ∀ x y, g (Function.update x i y) = g x)
    (hf : ∀ x, (𝔼 y, f (Function.update x i y)) ≤ p) :
    (𝔼 x, f x * g x) ≤ p * (𝔼 x, g x) := by
  classical
  rw [← expect_coordinate_refresh i (fun x => f x * g x)]
  calc
    (𝔼 x, 𝔼 y, f (Function.update x i y) * g (Function.update x i y))
        = 𝔼 x, (𝔼 y, f (Function.update x i y)) * g x := by
          apply Finset.expect_congr rfl
          intro x _
          simp_rw [hginv, Finset.expect_mul]
    _ ≤ 𝔼 x, p * g x := by
      apply Finset.expect_le_expect
      intro x _
      exact mul_le_mul_of_nonneg_right (hf x) (hg x)
    _ = p * (𝔼 x, g x) := (Finset.mul_expect _ _ _).symm

theorem expect_prod_le_of_ranked_dependencies
    (s : Finset α) (rank : α → ℕ) (f : α → (α → β) → ℝ) (p : α → ℝ)
    (hnonneg : ∀ i ∈ s, ∀ x, 0 ≤ f i x)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hfiber : ∀ i ∈ s, ∀ x, (𝔼 y, f i (Function.update x i y)) ≤ p i)
    (hdep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → rank j ≤ rank i →
      ∀ x y, f i (Function.update x j y) = f i x) :
    (𝔼 x, ∏ i ∈ s, f i x) ≤ ∏ i ∈ s, p i := by
  classical
  revert hnonneg hp hfiber hdep
  refine Finset.strongInductionOn s ?_
  intro s ih hnonneg hp hfiber hdep
  by_cases hs : s = ∅
  · subst s
    simp
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s rank
    (Finset.nonempty_iff_ne_empty.mpr hs)
  have hsub : s.erase a ⊆ s := Finset.erase_subset a s
  have hih : (𝔼 x, ∏ i ∈ s.erase a, f i x) ≤ ∏ i ∈ s.erase a, p i := by
    apply ih (s.erase a) (Finset.erase_ssubset ha)
    · exact fun i hi => hnonneg i (hsub hi)
    · exact fun i hi => hp i (hsub hi)
    · exact fun i hi => hfiber i (hsub hi)
    · exact fun i hi j hj => hdep i (hsub hi) j (hsub hj)
  have hg : ∀ x, 0 ≤ ∏ i ∈ s.erase a, f i x := by
    intro x
    exact Finset.prod_nonneg (fun i hi => hnonneg i (hsub hi) x)
  have hginv : ∀ x y,
      (∏ i ∈ s.erase a, f i (Function.update x a y)) =
        ∏ i ∈ s.erase a, f i x := by
    intro x y
    apply Finset.prod_congr rfl
    intro i hi
    exact hdep i (hsub hi) a ha (Finset.mem_erase.mp hi).1
      (hmin i (hsub hi)) x y
  calc
    (𝔼 x, ∏ i ∈ s, f i x)
        = 𝔼 x, f a x * ∏ i ∈ s.erase a, f i x := by
          apply Finset.expect_congr rfl
          intro x _
          exact (Finset.mul_prod_erase s (fun i => f i x) ha).symm
    _ ≤ p a * (𝔼 x, ∏ i ∈ s.erase a, f i x) :=
      expect_mul_le_of_coordinate_bound a (f a)
        (fun x => ∏ i ∈ s.erase a, f i x) (p a) hg hginv (hfiber a ha)
    _ ≤ p a * ∏ i ∈ s.erase a, p i := mul_le_mul_of_nonneg_left hih (hp a ha)
    _ = ∏ i ∈ s, p i := Finset.mul_prod_erase s p ha

theorem uniform_event_bound_of_ranked_dependencies
    (s : Finset α) (rank : α → ℕ) (E : α → (α → β) → Prop)
    [∀ i x, Decidable (E i x)] (p : ℝ) (hp : 0 ≤ p)
    (hfiber : ∀ i ∈ s, ∀ x,
      ((Finset.univ.filter (fun y => E i (Function.update x i y))).card : ℝ) /
        Fintype.card β ≤ p)
    (hdep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → rank j ≤ rank i →
      ∀ x y, E i (Function.update x j y) ↔ E i x) :
    ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
      Fintype.card (α → β) ≤ p ^ s.card := by
  classical
  have h := expect_prod_le_of_ranked_dependencies s rank
    (fun i x => if E i x then (1 : ℝ) else 0) (fun _ => p)
    (fun _ _ _ => by split_ifs <;> norm_num)
    (fun _ _ => hp) (fun i hi x => ?_) (fun i hi j hj hij hr x y => ?_)
  · have heq : ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
          Fintype.card (α → β) =
          𝔼 x, ∏ i ∈ s, (if E i x then (1 : ℝ) else 0) := by
      rw [Fintype.expect_eq_sum_div_card]
      congr 1
      rw [← Finset.sum_boole (R := ℝ) (fun x => ∀ i ∈ s, E i x) Finset.univ]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i ∈ s, E i x <;> simp [Finset.prod_boole, hx]
    rw [heq]
    simpa only [Finset.prod_const] using h
  · simpa only [Fintype.expect_eq_sum_div_card, Finset.sum_boole] using hfiber i hi x
  · simp only [hdep i hi j hj hij hr x y]

theorem uniform_event_bound_of_dependency_relation
    (s : Finset α) (R : α → α → Prop) (rank : α → ℕ)
    (E : α → (α → β) → Prop) [∀ i x, Decidable (E i x)]
    (p : ℝ) (hp : 0 ≤ p)
    (hrank : ∀ i ∈ s, ∀ j ∈ s, R i j → rank i < rank j)
    (hfiber : ∀ i ∈ s, ∀ x,
      ((Finset.univ.filter (fun y => E i (Function.update x i y))).card : ℝ) /
        Fintype.card β ≤ p)
    (hsupport : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ R i j →
      ∀ x y, E i (Function.update x j y) ↔ E i x) :
    ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
      Fintype.card (α → β) ≤ p ^ s.card := by
  apply uniform_event_bound_of_ranked_dependencies s rank E p hp hfiber
  intro i hi j hj hij hji x y
  apply hsupport i hi j hj hij
  intro hijR
  exact (not_lt_of_ge hji) (hrank i hi j hj hijR)

end Balanced.DependencyExtraction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFiberBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem line_fiber_card_le_one (S l : Line F) (hne : l ≠ S)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S) :
    (Finset.univ.filter (fun t => OnLine (x t) l)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  apply hinj
  exact common_point_eq_of_lines_ne l S hne (x t) (x u)
    (Finset.mem_filter.mp ht).2 (hx t) (Finset.mem_filter.mp hu).2 (hx u)

theorem line_union_fiber_card_le (S : Line F) (L : Finset (Line F))
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hne : ∀ l ∈ L, l ≠ S) :
    (Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l)).card ≤ L.card := by
  have heq : Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l) =
      L.biUnion (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) := by
    ext t
    simp
  rw [heq]
  simpa using Finset.card_biUnion_le_card_mul L
    (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) 1
    (fun l hl => line_fiber_card_le_one S l (hne l hl) x hinj hx)

theorem card_partnerCandidates_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ) (hB : (indexedThrough M U a).card ≤ B) :
    (partnerCandidates M U a).card ≤ B :=
  (Finset.card_image_le).trans hB

theorem card_mergedCandidates_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ) (hB : (indexedThrough M U a).card ≤ B) :
    (mergedCandidates M U a).card ≤ 2 * B := by
  have h := Finset.card_biUnion_le_card_mul (indexedThrough M U a)
    (fun ds => {constituent M ds.1 false, constituent M ds.1 true}) 2
    (fun (ds : Direction F × Bool) _ => by
      simpa using (Finset.card_insert_le (constituent M ds.1 false)
        {constituent M ds.1 true}))
  exact h.trans (by omega)

theorem indexedThrough_card_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    (indexedThrough M U a).card ≤ B := by
  refine (Finset.card_le_card ?_).trans hB
  intro ds hds
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ds, (Finset.mem_filter.mp hds).2.2⟩

theorem constituent_mem_mergedCandidates (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (d : Direction F) (s t : Bool)
    (hd : d ∈ U) (ha : OnLine a (constituent M d s)) :
    constituent M d t ∈ mergedCandidates M U a := by
  refine Finset.mem_biUnion.mpr ⟨(d, s), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, ha⟩
  · cases t <;> simp

theorem partner_mem_partnerCandidates (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (d : Direction F) (s : Bool)
    (hd : d ∈ U) (ha : OnLine a (constituent M d s)) :
    constituent M d (!s) ∈ partnerCandidates M U a := by
  exact Finset.mem_image.mpr ⟨(d, s),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, ha⟩, rfl⟩

end Balanced.LocalFiberBounds

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConditionFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem holds_eq_pointHolds (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (v : Position b) (z : Code b κ) :
    Holds P a bits p M v z =
      PointHolds a p M (prescribedPoint P a bits M) v z := by
  cases z with
  | inl z => rfl
  | inr z => cases z with
    | inl z => rfl
    | inr z => cases z <;> rfl

theorem pointHolds_imp_testLines (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (v : Position b) (z : Code b κ)
    (h : PointHolds a p M x v z) :
    ∃ l ∈ testLines a p M x z, l ≠ lineThrough (a.1 v.1) p ∧ OnLine (x v) l := by
  rcases z with u | xy | w | cw
  · obtain ⟨d, hd, t, hp, hv, hn⟩ := h
    exact ⟨constituent M d (!t), partner_mem_partnerCandidates M _ p d t
      (by simpa [unusedDirections] using hd) hp, hn, hv⟩
  · exact ⟨joiningLine (x xy.1) (x xy.2), by simp [testLines], h.2.2, h.2.1⟩
  · obtain ⟨d, hd, hw, t, hv, hn⟩ := h
    have hw' : ∃ s : Bool, OnLine (x w) (constituent M d s) := by
      simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, Bool.exists_bool] using hw
    obtain ⟨s, hs⟩ := hw'
    exact ⟨constituent M d t, constituent_mem_mergedCandidates M _ (x w) d s t
      (by simpa [unusedDirections] using hd) hs, hn, hv⟩
  · exact ⟨lineThrough (a.2 cw.1) (x cw.2), by simp [testLines], h.2, h.1⟩

theorem testLines_card_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (z : Code b κ) : (testLines a p M x z).card ≤ 2 * B := by
  rcases z with u | xy | w | cw
  · exact (card_partnerCandidates_le M _ p B (hmult p)).trans (by omega)
  · simp only [testLines, Finset.card_singleton]; omega
  · exact card_mergedCandidates_le M _ (x w) B (hmult (x w))
  · simp only [testLines, Finset.card_singleton]; omega

theorem testLines_congr (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x y : Position b → Point F) (z : Code b κ)
    (h : ∀ w ∈ anchors z, x w = y w) :
    testLines a p M x z = testLines a p M y z := by
  rcases z with u | xy | w | cw
  · rfl
  · simp only [testLines, h xy.1 (by simp [anchors]), h xy.2 (by simp [anchors])]
  · simp only [testLines, h w (by simp [anchors])]
  · simp only [testLines, h cw.2 (by simp [anchors])]

theorem pointHolds_congr (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x y : Position b → Point F) (v : Position b) (z : Code b κ)
    (hv : x v = y v) (h : ∀ w ∈ anchors z, x w = y w) :
    PointHolds a p M x v z ↔ PointHolds a p M y v z := by
  rcases z with u | xy | w | cw
  · simp only [PointHolds, hv]
  · simp only [PointHolds, hv, h xy.1 (by simp [anchors]), h xy.2 (by simp [anchors])]
  · simp only [PointHolds, hv, h w (by simp [anchors])]
  · simp only [PointHolds, hv, h cw.2 (by simp [anchors])]

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem pointHolds_fiber_card_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (x : α → F) (i : α) (v : Position b) (z : Code b κ)
    (hown : u v = i) (hanchor : ∀ w ∈ anchors z, u w ≠ i)
    (hinj : Function.Injective (point v))
    (hline : ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p)) :
    (Finset.univ.filter (fun t : F => PointHolds a p M
      (fun w => point w (Function.update x i t (u w))) v z)).card ≤ 2 * B := by
  let S := lineThrough (a.1 v.1) p
  let L := testLines a p M (fun w => point w (x (u w))) z
  have hsub : Finset.univ.filter (fun t : F => PointHolds a p M
      (fun w => point w (Function.update x i t (u w))) v z) ⊆
      Finset.univ.filter (fun t : F => ∃ l ∈ L.erase S, OnLine (point v t) l) := by
    intro t ht
    obtain ⟨l, hl, hn, hv⟩ := pointHolds_imp_testLines a p M _ v z
      (Finset.mem_filter.mp ht).2
    have heq : testLines a p M
        (fun w => point w (Function.update x i t (u w))) z = L := by
      apply testLines_congr
      intro w hw
      simp only [Function.update_of_ne (hanchor w hw)]
    rw [heq] at hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, l,
      Finset.mem_erase.mpr ⟨hn, hl⟩, by simpa [hown] using hv⟩
  exact (Finset.card_le_card hsub).trans
    ((line_union_fiber_card_le S (L.erase S) (point v) hinj hline
      (fun l hl => (Finset.mem_erase.mp hl).1)).trans
      ((Finset.card_le_card (Finset.erase_subset S L)).trans
        (testLines_card_le a p M _ B hB hmult z)))

omit [Fintype α] in
theorem pointHolds_update_iff (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (u : Position b → α) (point : Position b → F → Point F)
    (x : α → F) (j : α) (t : F) (v : Position b) (z : Code b κ)
    (hown : u v ≠ j) (hanchor : ∀ w ∈ anchors z, u w ≠ j) :
    PointHolds a p M (fun w => point w (Function.update x j t (u w))) v z ↔
      PointHolds a p M (fun w => point w (x (u w))) v z := by
  apply pointHolds_congr
  · simp only [Function.update_of_ne hown]
  · intro w hw
    simp only [Function.update_of_ne (hanchor w hw)]

theorem pointHolds_product_bound (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (s : Finset α) (test : α → Position b) (code : α → Code b κ)
    (rank : α → ℕ)
    (hown : ∀ i ∈ s, u (test i) = i)
    (hanchor : ∀ i ∈ s, ∀ w ∈ anchors (code i), u w ≠ i)
    (hinj : ∀ i ∈ s, Function.Injective (point (test i)))
    (hline : ∀ i ∈ s, ∀ t, OnLine (point (test i) t) (lineThrough (a.1 (test i).1) p))
    (hrank : ∀ i ∈ s, ∀ j ∈ s,
      j ∈ (anchors (code i)).image u → rank i < rank j) :
    ((Finset.univ.filter (fun x : α → F => ∀ i ∈ s,
      PointHolds a p M (fun w => point w (x (u w))) (test i) (code i))).card : ℝ) /
      Fintype.card (α → F) ≤ (2 * (B : ℝ) / Fintype.card F) ^ s.card := by
  apply DependencyExtraction.uniform_event_bound_of_dependency_relation
    s (fun i j => j ∈ (anchors (code i)).image u) rank
    (fun i x => PointHolds a p M (fun w => point w (x (u w))) (test i) (code i))
    (2 * (B : ℝ) / Fintype.card F) (by positivity) hrank
  · intro i hi x
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast pointHolds_fiber_card_le a p M B hB hmult u point x i
      (test i) (code i) (hown i hi) (hanchor i hi) (hinj i hi) (hline i hi)
  · intro i hi j hj hij hn x t
    apply pointHolds_update_iff
    · rw [hown i hi]
      exact hij
    · intro w hw heq
      apply hn
      exact Finset.mem_image.mpr ⟨w, hw, heq⟩

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSpecificationProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical BigOperators
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {b κ n : ℕ}

theorem specification_product_bound (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (v₀ : Position b) (σ : Fin n → Position b × Code b κ)
    (hσ : GoodSpecification u I σ) :
    UnusedOffsetIncidence.probability (fun x : α → F => ∀ k,
      PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) ≤
        (2 * (B : ℝ) / Fintype.card F) ^ n := by
  obtain ⟨hτ, hI, rank, hrank⟩ := hσ
  let τ : Fin n → α := fun k => u (σ k).1
  let s : Finset α := Finset.univ.image τ
  let test : α → Position b := Function.extend τ (fun k => (σ k).1) (fun _ => v₀)
  let code : α → Code b κ := Function.extend τ (fun k => (σ k).2) (fun _ => Sum.inl ())
  have htest : ∀ k, test (τ k) = (σ k).1 := fun k => hτ.extend_apply _ _ k
  have hcode : ∀ k, code (τ k) = (σ k).2 := fun k => hτ.extend_apply _ _ k
  have hs : ∀ i ∈ s, ∃ k, τ k = i := by
    intro i hi
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    exact ⟨k, hk⟩
  have hp := pointHolds_product_bound a p M B hB hmult u point s test code rank
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest])
    (fun i hi w hw hwi => by
      obtain ⟨k, rfl⟩ := hs i hi
      rw [hcode] at hw
      exact (lt_irrefl _) (hrank k k (Finset.mem_image.mpr ⟨w, hw, hwi⟩)))
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest]; exact hinj _ (hI k))
    (fun i hi => by obtain ⟨k, rfl⟩ := hs i hi; rw [htest]; exact hline _ (hI k))
    (fun i hi j hj hdep => by
      obtain ⟨k, rfl⟩ := hs i hi
      obtain ⟨l, rfl⟩ := hs j hj
      rw [hcode] at hdep
      exact hrank k l hdep)
  have hcard : s.card = n := by
    rw [Finset.card_image_of_injective _ hτ]
    simp
  rw [hcard] at hp
  have hevent : (fun x : α → F => ∀ i ∈ s,
      PointHolds a p M (fun w => point w (x (u w))) (test i) (code i)) =
      (fun x : α → F => ∀ k,
        PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) := by
    funext x
    apply propext
    constructor
    · intro h k
      simpa only [htest, hcode] using h (τ k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    · intro h i hi
      obtain ⟨k, rfl⟩ := hs i hi
      simpa only [htest, hcode] using h k
  unfold UnusedOffsetIncidence.probability
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Eq.to_iff (congrFun hevent x).symm

theorem specifications_probability_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (hb : 1 ≤ b) :
    UnusedOffsetIncidence.probability (fun x : α → F =>
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification u I σ ∧ ∀ k,
          PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
  let E := fun (σ : Fin (3 - κ) → Position b × Code b κ) (x : α → F) =>
    GoodSpecification u I σ ∧ ∀ k,
      PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2
  have hE : ∀ σ, UnusedOffsetIncidence.probability (E σ) ≤
      (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
    intro σ
    by_cases hσ : GoodSpecification u I σ
    · apply (UnusedOffsetIncidence.probability_mono (fun x h => h.2)).trans
      exact specification_product_bound a p M B hB hmult u point I hinj hline
        (⟨0, by omega⟩, 0) σ hσ
    · simp only [E, hσ, false_and, UnusedOffsetIncidence.probability,
        Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  have hsum := (UnusedOffsetIncidence.probability_exists_fintype_le E).trans
    (Finset.sum_le_sum (fun σ _ => hE σ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc := card_specifications_le b κ hb
  have hcr : (Fintype.card (Fin (3 - κ) → Position b × Code b κ) : ℝ) ≤
      (148 * (b : ℝ) ^ 3) ^ 3 := by exact_mod_cast hc
  calc
    _ ≤ (148 * (b : ℝ) ^ 3) ^ 3 := hcr
    _ = (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 := by ring

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSpecificationEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

variable {b κ n : ℕ} {α : Type*} [DecidableEq α]

theorem exists_goodSpecification_of_finset
    (u : Position b → α) (I T : Finset (Position b))
    (hTI : T ⊆ I) (hcard : T.card = n) (hinj : Set.InjOn u T)
    (code : Position b → Code b κ) (rank : α → ℕ)
    (hrank : ∀ v ∈ T, ∀ w ∈ T,
      u w ∈ (anchors (code v)).image u → rank (u v) < rank (u w))
    (E : Position b → Code b κ → Prop) (hE : ∀ v ∈ T, E v (code v)) :
    ∃ σ : Fin n → Position b × Code b κ,
      GoodSpecification u I σ ∧
      (∀ k, E (σ k).1 (σ k).2) ∧
      Finset.univ.image (fun k => (σ k).1) = T := by
  let e : Fin n ≃ {v // v ∈ T} :=
    (Fintype.equivFinOfCardEq (show Fintype.card {v // v ∈ T} = n by
      simpa using hcard)).symm
  let σ : Fin n → Position b × Code b κ := fun k => ((e k).val, code (e k).val)
  refine ⟨σ, ?_, ?_, ?_⟩
  · refine ⟨?_, fun k => hTI (e k).property, rank, ?_⟩
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hinj (e i).property (e j).property hij
    · intro i j hij
      exact hrank _ (e i).property _ (e j).property hij
  · intro k
    exact hE _ (e k).property
  · ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk⟩
      exact hk ▸ (e k).property
    · intro hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteDependencyRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

theorem exists_nat_rank_of_wellFounded {α : Type*} [Fintype α]
    (R : α → α → Prop) (hR : WellFounded R) :
    ∃ rank : α → ℕ, ∀ x y, R x y → rank x < rank y := by
  let pred : α → Finset α := fun x =>
    Finset.univ.filter (fun z => Relation.TransGen R z x)
  refine ⟨fun x => (pred x).card, ?_⟩
  intro x y hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hz).2.trans (Relation.TransGen.single hxy)⟩
  · intro heq
    have hx : x ∈ pred y := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Relation.TransGen.single hxy⟩
    rw [← heq] at hx
    have hxx := (Finset.mem_filter.mp hx).2
    exact hR.transGen.asymmetric x x hxx hxx

theorem exists_nat_rank_on_finset {α : Type*} [DecidableEq α]
    (T : Finset α) (R : α → α → Prop)
    (hR : WellFounded (fun x y : {v // v ∈ T} => R x.val y.val)) :
    ∃ rank : α → ℕ, ∀ x ∈ T, ∀ y ∈ T, R x y → rank x < rank y := by
  obtain ⟨rank, hrank⟩ := exists_nat_rank_of_wellFounded
    (fun x y : {v // v ∈ T} => R x.val y.val) hR
  refine ⟨fun x => if h : x ∈ T then rank ⟨x, h⟩ else 0, ?_⟩
  intro x hx y hy hxy
  simpa only [dite_eq_left hx, dite_eq_left hy] using hrank ⟨x, hx⟩ ⟨y, hy⟩ hxy

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalBadCoverSpecifications
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

variable {b κ n : ℕ}

theorem exists_goodSpecification_of_acyclic_fixed
    (u : Position b → Position b) (I T : Finset (Position b))
    (hTI : T ⊆ I) (hcard : T.card = n) (hfix : ∀ v ∈ T, u v = v)
    (code : Position b → Code b κ)
    (hwf : WellFounded (fun x y : {v // v ∈ T} =>
      y.val ∈ underlyingAnchors u (code x.val)))
    (E : Position b → Code b κ → Prop) (hE : ∀ v ∈ T, E v (code v)) :
    ∃ σ : Fin n → Position b × Code b κ,
      GoodSpecification u I σ ∧
      (∀ k, E (σ k).1 (σ k).2) ∧
      Finset.univ.image (fun k => (σ k).1) = T := by
  obtain ⟨rank, hrank⟩ := exists_nat_rank_on_finset T
    (fun v w => w ∈ underlyingAnchors u (code v)) hwf
  apply exists_goodSpecification_of_finset u I T hTI hcard
    (fun v hv w hw h => by simpa only [hfix v hv, hfix w hw] using h)
    code rank _ E hE
  intro v hv w hw hdep
  rw [hfix v hv, hfix w hw]
  exact hrank v hv w hw (by simpa only [underlyingAnchors, hfix w hw] using hdep)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem badCover_zero_reuse_exists_goodSpecification
    (P : EqualityPattern b 0) (a : DirectionAssignment F b 0)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M) :
    ∃ σ : Fin 3 → Position b × Code b 0,
      GoodSpecification id Finset.univ σ ∧
      ∀ k, Holds P a bits p M (σ k).1 (σ k).2 := by
  obtain ⟨T, code, hcard, hT, hwf⟩ :=
    badCover_zero_reuse_exists_acyclic_spec P a bits p M hb ha hadm hbad
  obtain ⟨σ, hσ, hE, _⟩ := exists_goodSpecification_of_acyclic_fixed
    id Finset.univ T (Finset.subset_univ _) hcard (fun _ _ => rfl) code
    (by simpa only [underlyingAnchors, Finset.image_id] using hwf)
    (Holds P a bits p M) (fun v hv => (hT v hv).1)
  exact ⟨σ, hσ, hE⟩

theorem badCover_one_reuse_exists_goodSpecification
    (P : EqualityPattern b 1) (a : DirectionAssignment F b 1)
    (bits : Bits b) (p : Point F) (M : MergedPairs F)
    (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) :
    let u := ParentMap.underlying root child r s (bits root r) (bits child s)
    ∃ σ : Fin 2 → Position b × Code b 1,
      GoodSpecification u (Finset.univ \ ParentMap.dependent child s) σ ∧
      ∀ k, Holds P a bits p M (σ k).1 (σ k).2 := by
  dsimp only
  let u := ParentMap.underlying root child r s (bits root r) (bits child s)
  obtain ⟨T, code, hcard, hT, hwf⟩ :=
    badCover_one_reuse_exists_acyclic_spec P a bits p M hb ha hadm hbad
      root child r s hshared
  have hTI : T ⊆ Finset.univ \ ParentMap.dependent child s := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hT v hv).1⟩
  have hfix : ∀ v ∈ T, u v = v := by
    intro v hv
    exact ParentMap.underlying_fixed root child r s (bits root r) (bits child s)
      (hT v hv).1
  obtain ⟨σ, hσ, hE, _⟩ := exists_goodSpecification_of_acyclic_fixed u
    (Finset.univ \ ParentMap.dependent child s) T hTI hcard hfix code hwf
    (Holds P a bits p M) (fun v hv => (hT v hv).2.1)
  exact ⟨σ, hσ, hE⟩

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConditionUnusedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem pointHolds_iff_of_unused_eq (a : DirectionAssignment F b κ)
    (p : Point F) (M N : MergedPairs F)
    (h : ∀ d, d ∉ FourEvents.usedDirections a → M d = N d)
    (x : Position b → Point F) (v : Position b) (z : Code b κ) :
    PointHolds a p M x v z ↔ PointHolds a p N x v z := by
  rcases z with z | xy | w | cw
  · simp only [PointHolds]
    apply exists_congr
    intro d
    by_cases hd : d ∉ FourEvents.usedDirections a
    · simp only [hd, constituent, h d hd]
    · simp only [hd, false_and]
  · rfl
  · simp only [PointHolds]
    apply exists_congr
    intro d
    by_cases hd : d ∉ FourEvents.usedDirections a
    · simp only [hd, mergedPoints, constituent, h d hd]
    · simp only [hd, false_and]
  · rfl

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrecoverageTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M N : MergedPairs F}

theorem indexedThrough_congr (U : Finset (Direction F)) (z : Point F)
    (hMN : ∀ d ∈ U, M d = N d) : indexedThrough M U z = indexedThrough N U z := by
  ext ds
  simp only [indexedThrough, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hd, hz⟩ <;> refine ⟨hd, ?_⟩
  · simpa only [constituent, hMN ds.1 hd] using hz
  · simpa only [constituent, hMN ds.1 hd] using hz

theorem fixedUnused_multiplicity_le (hA : Admissible P a bits p M)
    (hMN : ∀ d ∈ unusedDirections a, M d = N d) (z : Point F) :
    (indexedThrough N (unusedDirections a) z).card ≤ logBudget F := by
  rw [← indexedThrough_congr (unusedDirections a) z hMN]
  exact indexedThrough_card_le M _ z _ (hA.2.2.2.2 z)

end
end Balanced.Local.PrescribedGeometry

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSpecificationTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {b κ : ℕ}

theorem admissibleBadCover_fixedUnused_bound
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (bits : Bits b)
    (p : Point F) (N : MergedPairs F) (Ms : (α → F) → MergedPairs F)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b)) (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hfixed : ∀ x d, d ∈ unusedDirections a → Ms x d = N d)
    (hpoints : ∀ x v, prescribedPoint P a bits (Ms x) v = point v (x (u v)))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (hextract : ∀ x, AdmissibleBadCover P a bits p (Ms x) →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification u I σ ∧ ∀ k, Holds P a bits p (Ms x) (σ k).1 (σ k).2) :
    UnusedOffsetIncidence.probability
      (fun x : α → F => AdmissibleBadCover P a bits p (Ms x)) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  by_cases hmult : ∀ y : Point F,
      (indexedThrough N (unusedDirections a) y).card ≤ logBudget F
  · apply (UnusedOffsetIncidence.probability_mono (fun x hx => ?_)).trans
      (specifications_probability_le a p N (logBudget F) hB hmult u point I hinj hline hb)
    obtain ⟨σ, hσ, hholds⟩ := hextract x hx
    refine ⟨σ, hσ, fun k => ?_⟩
    have hh := hholds k
    rw [holds_eq_pointHolds] at hh
    have heq : prescribedPoint P a bits (Ms x) = fun v => point v (x (u v)) :=
      funext (hpoints x)
    rw [heq] at hh
    exact (pointHolds_iff_of_unused_eq a p (Ms x) N
      (fun d hd => hfixed x d (by simpa [unusedDirections] using hd)) _ _ _).mp hh
  · have hempty : ∀ x : α → F, ¬ AdmissibleBadCover P a bits p (Ms x) := by
      intro x hx
      apply hmult
      intro y
      exact PrescribedGeometry.fixedUnused_multiplicity_le hx.1 (hfixed x) y
    simp only [UnusedOffsetIncidence.probability, hempty, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSmallReuseAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

noncomputable section
open scoped Classical
open RootChildPartition AlignedUnused ConditionSpec

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem PointSystem.fixedUnused_badCover_bound
    {P : EqualityPattern b κ} {a : DirectionAssignment F b κ}
    {bits : Bits b} {p : Point F} {R : Finset (Fin b)}
    (S : PointSystem P a bits p R) (hκ : κ ≤ 2)
    (hD : (dependentOccurrences P R).card = 2 * κ) (ha : Eligible P a)
    (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hextract : ∀ M, AdmissibleBadCover P a bits p M →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification S.underlying (Finset.univ \ dependentOccurrences P R) σ ∧
          ∀ k, Holds P a bits p M (σ k).1 (σ k).2)
    (z : UnusedArray P a) :
    UnusedOffsetIncidence.probability (fun x : FreeIndex P R → F =>
      AdmissibleBadCover P a bits p
        ((coordinateEquiv P hκ R hD a ha bits p).symm (x,z)).1) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  let Ms : (FreeIndex P R → F) → MergedPairs F := fun x => (e.symm (x,z)).1
  apply admissibleBadCover_fixedUnused_bound P a bits p (Ms (fun _ => 0)) Ms
    S.underlying S.point (Finset.univ \ dependentOccurrences P R) hb hB
  · intro x d hd
    have hdu : d ∉ usedDirections P a := by
      simpa only [ConditionSpec.unusedDirections, Finset.mem_sdiff,
        Finset.mem_univ, true_and, FourEvents.usedDirections, usedDirections] using hd
    exact (generated_unused P hκ R hD a ha bits p (x,z) ⟨d,hdu⟩).trans
      (generated_unused P hκ R hD a ha bits p ((fun _ => 0),z) ⟨d,hdu⟩).symm
  · intro x v
    exact S.generated_points hκ hD ha (x,z) v
  · intro v hv
    exact S.free_injective ⟨v, (Finset.mem_sdiff.mp hv).2⟩
  · intro v hv t
    exact S.free_onLine ⟨v, (Finset.mem_sdiff.mp hv).2⟩ t
  · intro x hx
    exact hextract (Ms x) hx

theorem PointSystem.badCover_probability_bound
    {P : EqualityPattern b κ} {a : DirectionAssignment F b κ}
    {bits : Bits b} {p : Point F} {R : Finset (Fin b)}
    (S : PointSystem P a bits p R) (hκ : κ ≤ 2)
    (hD : (dependentOccurrences P R).card = 2 * κ) (ha : Eligible P a)
    (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hextract : ∀ M, AdmissibleBadCover P a bits p M →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification S.underlying (Finset.univ \ dependentOccurrences P R) σ ∧
          ∀ k, Holds P a bits p M (σ k).1 (σ k).2) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  apply conditionedOffsetProbability_le_of_freeCoordinate_fibers P hκ R hD a ha bits p
  intro z
  rw [← UnusedOffsetIncidence.probability_eq_pmf]
  exact S.fixedUnused_badCover_bound hκ hD ha hb hB hextract z

theorem goodSpecification_lift {α β : Type*} [DecidableEq α] [DecidableEq β]
    {n : ℕ} {u : Position b → α} (v : Position b → β) (f : β → α)
    (hfv : ∀ w, f (v w) = u w) {I : Finset (Position b)}
    {σ : Fin n → Position b × Code b κ} (h : GoodSpecification u I σ) :
    GoodSpecification v I σ := by
  obtain ⟨hinj, hI, rank, hrank⟩ := h
  refine ⟨?_, hI, rank ∘ f, ?_⟩
  · intro i j hij
    apply hinj
    exact (hfv _).symm.trans ((congrArg f hij).trans (hfv _))
  · intro i j hij
    simp only [Function.comp_apply, hfv]
    apply hrank i j
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hij
    exact Finset.mem_image.mpr ⟨w, hw,
      (hfv w).symm.trans ((congrArg f heq).trans (hfv _))⟩

theorem smallReuse_badCover_probability_bound
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (hb : 3 ≤ b) (hB : b ≤ logBudget F)
    (hκ : κ ≤ 1) (ha : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hκ with rfl | rfl
  · let R : Finset (Fin b) := Finset.univ
    have hdep : dependentOccurrences P R = ∅ := by simp [R, dependentOccurrences]
    have hD : (dependentOccurrences P R).card = 2 * 0 := by simp [hdep]
    let S := pointSystemOfNoDependents P a bits p R hdep
    apply S.badCover_probability_bound (by omega) hD ha (by omega) (by omega)
    intro M hM
    obtain ⟨σ, hσ, hholds⟩ := badCover_zero_reuse_exists_goodSpecification
      P a bits p M hb ha hM.1 hM.2
    refine ⟨σ, ?_, hholds⟩
    have hg : GoodSpecification id (Finset.univ \ dependentOccurrences P R) σ := by
      simpa only [hdep, Finset.sdiff_empty] using hσ
    exact goodSpecification_lift S.underlying Subtype.val (fun _ => rfl) hg
  · obtain ⟨R, root, child, r, s, _, _, _, hne, _, _, hshared, hdep, _⟩ :=
      exists_one_reuse_linked_pair P hb
    have hdep' : dependentOccurrences P R = ParentMap.dependent child s := hdep
    have hD : (dependentOccurrences P R).card = 2 * 1 := by
      rw [hdep']
      have hne' : (child,s) ≠ (child,s-1) := by
        intro h
        exact ParentMap.sub_one_ne s (congrArg Prod.snd h).symm
      simp [ParentMap.dependent, hne']
    let S := pointSystemOfLinkedPair P a ha bits p R root child r s hne hshared hdep'
    apply S.badCover_probability_bound (by omega) hD ha (by omega) (by omega)
    intro M hM
    obtain ⟨σ, hσ, hholds⟩ := badCover_one_reuse_exists_goodSpecification
      P a bits p M hb ha hM.1 hM.2 root child r s hshared
    refine ⟨σ, ?_, hholds⟩
    have hg : GoodSpecification
        (ParentMap.underlying root child r s (bits root r) (bits child s))
        (Finset.univ \ dependentOccurrences P R) σ := by
      simpa only [hdep'] using hσ
    exact goodSpecification_lift S.underlying Subtype.val (fun _ => rfl) hg

end
end Balanced.Local.AlignedGlobal

namespace Balanced.Local

universe u

theorem pencilSmallReuse_proof_oai : PencilSmallReuseResult.{u} := by
  refine ⟨alignmentNormalization_proof, (148 : ℝ) ^ 3, by positivity, 9, 0, ?_⟩
  intro F _ _ _ _ b κ hb hB hκ P a ha bits p
  exact AlignedGlobal.smallReuse_badCover_probability_bound P a bits p hb hB hκ ha

end Balanced.Local

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.Local.pencilSmallReuse_proof_oai.{u} := @OAI.Balanced.Local.pencilSmallReuse_proof_oai.{u}
