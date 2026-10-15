-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:14:42.0211+00:00
-- url     : https://prove2.me/submissions/5b1b6194-4d15-43f5-b8ba-975934097b61

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/SeparateCounterexamples.lean:L10-L25
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_InfiniteMatroidCounterexample_separate_covering_packing_counterexamples) verbatim and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_RankDescent__InfiniteMatroidCorollaries
import Theorems.Thm_OAI_InfiniteMatroidCounterexample_exists_maximal_wave

-- ---- from OAI.Combinatorics.InfiniteMatroid.Matroid ----
namespace OAI

section

open Set Matroid

namespace InfiniteMatroidCounterexample

namespace BasisSystem

variable {α : Type*} (S : BasisSystem α)

lemma self_dual : S.matroid.dual = S.matroid := by
  apply Matroid.ext_isBase Matroid.dual_ground
  intro B _
  rw [Matroid.dual_isBase_iff, ground, ← Set.compl_eq_univ_sdiff, isBase_iff, isBase_iff]
  exact ⟨fun h ↦ by simpa using S.compl_closed h, fun h ↦ S.compl_closed h⟩

end BasisSystem
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.DoubleRay ----
namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

lemma rayMatroid_ground {α : Type*} (Q : Matroid (α × Bool)) (hQ : Q.E = univ) (p : Bool) :
    (rayMatroid Q p).E = univ := by
  have hg : (Matroid.sum' (fun _ : Vertex p ↦ Q)).E = univ := by
    ext ⟨v,x⟩
    simp only [Matroid.sum'_ground_eq,hQ,mem_iUnion,mem_image,mem_univ,true_and,iff_true]
    exact ⟨v,x,rfl⟩
  rw [rayMatroid,Matroid.mapEquiv_ground_eq,hg]
  rw [Set.image_univ]
  exact Set.range_eq_univ.mpr (componentEquiv α p).surjective

lemma rayMatroid_indep_iff {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) (I : Set (ℤ × α)) :
    (rayMatroid Q p).Indep I ↔ ∀ v : Vertex p, Q.Indep (componentMap v ⁻¹' I) := by
  rw [rayMatroid,Matroid.mapEquiv_indep_iff,Equiv.image_symm_eq_preimage,Matroid.sum'_indep_iff]
  rfl
lemma rayMatroid_isBase_iff {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) (B : Set (ℤ × α)) :
    (rayMatroid Q p).IsBase B ↔ ∀ v : Vertex p, Q.IsBase (componentMap v ⁻¹' B) := by
  rw [rayMatroid,Matroid.mapEquiv_isBase_iff,Equiv.image_symm_eq_preimage,Matroid.sum'_isBase_iff]
  rfl

lemma selfDual_compl_base_iff {α : Type*} (Q : Matroid α) (hE : Q.E = univ) (hQ : Q.dual = Q)
    (B : Set α) : Q.IsBase Bᶜ ↔ Q.IsBase B := by
  have h : Q.dual.IsBase B ↔ Q.IsBase Bᶜ := by
    rw [Matroid.dual_isBase_iff,hE,←Set.compl_eq_univ_sdiff]
  rw [hQ] at h
  exact h.symm

lemma rayMatroid_selfDual {α : Type*} (Q : Matroid (α × Bool)) (hE : Q.E = univ) (hQ : Q.dual = Q)
    (p : Bool) : (rayMatroid Q p).dual = rayMatroid Q p := by
  apply Matroid.ext_isBase Matroid.dual_ground
  intro B _
  rw [Matroid.dual_isBase_iff,rayMatroid_ground Q hE,←Set.compl_eq_univ_sdiff,
    rayMatroid_isBase_iff,rayMatroid_isBase_iff]
  exact forall_congr' (fun v ↦ selfDual_compl_base_iff Q hE hQ (componentMap v ⁻¹' B))

lemma assignment_indep {α : Type*} (Q : Matroid (α × Bool)) {I : Set (ℤ × α)}
    (h0 : (rayMatroid Q false).Indep I) (h1 : (rayMatroid Q true).Indep Iᶜ) (n : ℤ) :
    Q.Indep (assignment I n) := by
  by_cases hn : n % 2 = 0
  · have hv : n % 2 = parityBit false := hn
    have hi := (rayMatroid_indep_iff Q false I).mp h0 ⟨n,hv⟩
    change Q.Indep {x | (bundleAt n x.2,x.1) ∈ I} at hi
    simpa only [assignment,hn,ite_true] using hi
  · have hv : n % 2 = parityBit true := by change n % 2 = 1; omega
    have hi := (rayMatroid_indep_iff Q true Iᶜ).mp h1 ⟨n,hv⟩
    change Q.Indep {x | (bundleAt n x.2,x.1) ∉ I} at hi
    simpa only [assignment,hn,ite_false] using hi

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Waves ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma contractOnto_ground_sdiff {α : Type*} (M : Matroid α) (P : Set α) :
    contractOnto M (M.E \ P) = M ／ P := rfl

lemma Wave.lift_contract {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W V : Set α × (ι → Set α)}
    (hW : Wave M F W) (hV : Wave (fun i ↦ M i ／ W.1) (F \ W.1) V) :
    Wave M F (W.1 ∪ V.1, fun i ↦ W.2 i ∪ V.2 i) := by
  refine ⟨union_subset hW.1 (hV.1.trans sdiff_subset), ?_, ?_, ?_⟩
  · intro i
    exact union_subset_union (hW.2.1 i) (hV.2.1 i)
  · intro i j hij
    apply disjoint_left.mpr
    rintro x (hxi | hxi) (hxj | hxj)
    · exact disjoint_left.mp (hW.2.2.1 hij) hxi hxj
    · exact (hV.1 (hV.2.1 j hxj)).2 (hW.2.1 i hxi)
    · exact (hV.1 (hV.2.1 i hxi)).2 (hW.2.1 j hxj)
    · exact disjoint_left.mp (hV.2.2.1 hij) hxi hxj
  · intro i
    have hP : W.1 ⊆ (M i).closure (W.2 i ∪ V.2 i) :=
      (hW.2.2.2 i).trans ((M i).closure_mono subset_union_left)
    have hT : V.2 i ⊆ (M i).closure (W.2 i ∪ V.2 i) := by
      intro x hx
      refine (M i).mem_closure_of_mem' (Or.inr hx) ?_
      rw [hE i]
      exact (hV.1 (hV.2.1 i hx)).1
    refine union_subset hP ?_
    have hv := hV.2.2.2 i
    rw [Matroid.contract_closure_eq] at hv
    exact (hv.trans sdiff_subset).trans
      ((M i).closure_subset_closure_of_subset_closure (union_subset hT hP))

lemma residual_wave_empty {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W V : Set α × (ι → Set α)}
    (hW : Maximal (Wave M F) W)
    (hV : Wave (fun i ↦ M i ／ W.1) (F \ W.1) V) : V.1 = ∅ := by
  have hLift := hW.1.lift_contract hE hV
  have hle : W ≤ (W.1 ∪ V.1, fun i ↦ W.2 i ∪ V.2 i) :=
    ⟨subset_union_left, fun _ ↦ subset_union_left⟩
  have hsub : V.1 ⊆ W.1 := subset_union_right.trans (hW.2 hLift hle).1
  exact eq_empty_iff_forall_notMem.mpr fun x hx ↦ (hV.1 hx).2 (hsub hx)

lemma wave_of_restriction_packing {α ι : Type*} {M : ι → Matroid α} {F Y : Set α}
    (hE : ∀ i, (M i).E = F) (hY : Y ⊆ F)
    (h : FamilyPacking (fun i ↦ M i ↾ Y)) :
    ∃ S, Wave M F (Y, S) := by
  obtain ⟨S, hdisj, hS⟩ := h
  have hSY : ∀ i, S i ⊆ Y := fun i ↦ (hS i).subset_ground
  refine ⟨S, hY, hSY, hdisj, fun i ↦ ?_⟩
  exact ((M i).restrict_spanning_iff (hSY i) (by rw [hE]; exact hY)).mp (hS i)

lemma FamilyCovering.empty {α ι : Type*} (M : ι → Matroid α) :
    FamilyCovering ∅ (fun i ↦ M i ↾ ∅) := by
  refine ⟨fun _ ↦ ∅, fun _ ↦ Matroid.empty_indep _, ?_⟩
  simp

lemma residual_covering_condition {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W : Set α × (ι → Set α)}
    (hW : Maximal (Wave M F) W) :
    ∀ Y ⊆ F \ W.1, FamilyPacking (fun i ↦ (M i ／ W.1) ↾ Y) →
      FamilyCovering Y (fun i ↦ (M i ／ W.1) ↾ Y) := by
  intro Y hY hpack
  have hg : ∀ i, (M i ／ W.1).E = F \ W.1 := by simp [hE]
  obtain ⟨S, hS⟩ := wave_of_restriction_packing hg hY hpack
  have hzero : Y = ∅ := residual_wave_empty hE hW hS
  subst Y
  exact FamilyCovering.empty _

end InfiniteMatroidCounterexample

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.CoveringReduction ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma packingCovering_of_wave_covering {α : Type*} {M : Bool → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W : Set α × (Bool → Set α)}
    (hW : Wave M F W) (hC : FamilyCovering (F \ W.1) (fun i ↦ M i ／ W.1)) :
    HasPackingCovering (M false) (M true) := by
  obtain ⟨I, hI, hcov⟩ := hC
  have hfull : I false ∪ I true = F \ W.1 := by
    rw [← hcov]
    ext x
    simp only [mem_union, mem_iUnion]
    exact ⟨fun h ↦ h.elim (fun hx ↦ ⟨false, hx⟩) (fun hx ↦ ⟨true, hx⟩),
      fun ⟨i, hi⟩ ↦ by cases i <;> simp_all⟩
  have hsub : ∀ i, I i ⊆ F \ W.1 := by
    intro i
    simpa [hE] using (hI i).subset_ground
  have hcont : ∀ i, (contractOnto (M i) (F \ W.1)).Indep (I i) := by
    intro i
    rw [← hE i, contractOnto_ground_sdiff]
    exact hI i
  refine ⟨W.1, F \ W.1, W.2 false, W.2 true, I false, I true,
    disjoint_sdiff_right, ?_, (hE true).trans (hE false).symm,
    hW.2.1 false, hW.2.1 true, hW.2.2.1 Bool.false_ne_true, ?_, ?_,
    hsub false, hsub true, hcont false, hcont true, hfull⟩
  · rw [hE false]
    exact union_sdiff_cancel hW.1
  · exact ((M false).restrict_spanning_iff (hW.2.1 false)
      (by rw [hE]; exact hW.1)).mpr (hW.2.2.2 false)
  · exact ((M true).restrict_spanning_iff (hW.2.1 true)
      (by rw [hE]; exact hW.1)).mpr (hW.2.2.2 true)

theorem separate_covering_of_no_packingCovering {α : Type*} {M : Bool → Matroid α}
    {F : Set α} (hE : ∀ i, (M i).E = F)
    (hno : ¬ HasPackingCovering (M false) (M true)) :
    ∃ (C : Set α) (N : Bool → Matroid α),
      (∀ i, (N i).E = C) ∧ ¬ FamilyCovering C N ∧
      (∀ Y ⊆ C, FamilyPacking (fun i ↦ N i ↾ Y) →
        FamilyCovering Y (fun i ↦ N i ↾ Y)) := by
  obtain ⟨W, hW⟩ := exists_maximal_wave M F
  refine ⟨F \ W.1, fun i ↦ M i ／ W.1, ?_, ?_, residual_covering_condition hE hW⟩
  · simp [hE]
  · exact fun h ↦ hno (packingCovering_of_wave_covering hE hW.1 h)

end InfiniteMatroidCounterexample

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.PairDuality ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma pair_covering_iff_dual_packing {α : Type*} {M : Bool → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) :
    FamilyCovering F M ↔ FamilyPacking (fun i ↦ (M i).dual) := by
  constructor
  · rintro ⟨I, hI, hcov⟩
    refine ⟨fun i ↦ F \ I i, ?_, ?_⟩
    · intro i j hij
      apply disjoint_left.mpr
      rintro x ⟨hxF, hxi⟩ ⟨_, hxj⟩
      have hx : x ∈ ⋃ k, I k := hcov.symm ▸ hxF
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
      have hk : k = i ∨ k = j := by cases i <;> cases j <;> cases k <;> simp_all
      rcases hk with rfl | rfl
      · exact hxi hxk
      · exact hxj hxk
    · intro i
      have hc : (M i).dual.Coindep (I i) := by
        rw [Matroid.dual_coindep_iff]
        exact hI i
      simpa only [Matroid.dual_ground, hE] using hc.compl_spanning
  · rintro ⟨S, hdisj, hS⟩
    refine ⟨fun i ↦ F \ S i, ?_, ?_⟩
    · intro i
      have hc := (hS i).compl_coindep
      simpa only [Matroid.dual_ground, hE, Matroid.dual_coindep_iff] using hc
    · ext x
      simp only [mem_iUnion, mem_sdiff]
      constructor
      · rintro ⟨i, hx, _⟩
        exact hx
      · intro hx
        by_cases hs : x ∈ S false
        · exact ⟨true, hx, fun h ↦ disjoint_left.mp (hdisj Bool.false_ne_true) hs h⟩
        · exact ⟨false, hx, hs⟩

lemma separate_packing_of_covering_counterexample {α : Type*}
    {M : Bool → Matroid α} {F : Set α} (hE : ∀ i, (M i).E = F)
    (hno : ¬ FamilyCovering F M)
    (hcond : ∀ Y ⊆ F, FamilyPacking (fun i ↦ M i ↾ Y) →
      FamilyCovering Y (fun i ↦ M i ↾ Y)) :
    ¬ PackingConjectureFor F (fun i ↦ (M i).dual) := by
  intro hconj
  apply hno
  apply (pair_covering_iff_dual_packing hE).mpr
  apply hconj.mpr
  intro Y hY hcov
  have hground : ∀ i, (M i ↾ Y).E = Y := fun _ ↦ rfl
  have hdualground : ∀ i, (M i ↾ Y).dual.E = Y := fun _ ↦ rfl
  have hcov' : FamilyCovering Y (fun i ↦ (M i ↾ Y).dual) := by
    simpa only [contractOnto, Matroid.dual_dual] using hcov
  have hp : FamilyPacking (fun i ↦ M i ↾ Y) := by
    simpa only [Matroid.dual_dual] using
      (pair_covering_iff_dual_packing hdualground).mp hcov'
  have hdc := (pair_covering_iff_dual_packing hground).mp (hcond Y hY hp)
  simpa only [contractOnto, Matroid.dual_dual] using hdc

end InfiniteMatroidCounterexample

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Cardinality ----
namespace OAI

section

open Set Cardinal

namespace InfiniteMatroidCounterexample

lemma cindex_initial_segment (i : CIndex) : Cardinal.mk (Iic i) < Cardinal.continuum := by
  have h : Iic i = insert i (Iio i) := by ext x; simp [le_iff_lt_or_eq, eq_comm, or_comm]
  rw [h]
  apply lt_of_le_of_lt Cardinal.mk_insert_le
  have h0 := cindex_predecessors i
  have hc : ℵ₀ < Cardinal.continuum := Cardinal.aleph0_lt_continuum
  calc
    _ ≤ max (Cardinal.mk (Iio i)) ℵ₀ + max (Cardinal.mk (Iio i)) ℵ₀ :=
      add_le_add (le_max_left _ _) (le_trans Cardinal.one_le_aleph0 (le_max_right _ _))
    _ = max (Cardinal.mk (Iio i)) ℵ₀ := Cardinal.add_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt h0 hc

/-- Enumeration of all subsets of any countably infinite type, on the initial continuum ordinal. -/
lemma exists_set_enumeration (α : Type) [Countable α] [Infinite α] :
    ∃ f : CIndex → Set α, Function.Surjective f := by
  have hc : Cardinal.mk (Set α) = Cardinal.continuum := by
    rw [Cardinal.mk_set, Cardinal.mk_eq_aleph0]
    rfl
  obtain ⟨e⟩ := Cardinal.eq.mp (cindex_card.trans hc.symm)
  exact ⟨e, e.surjective⟩

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Ideals ----
namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

namespace SubsetIdeal
variable {α : Type*} (K : SubsetIdeal α)

lemma finite_sUnion {S : Set (Set α)} (hS : S.Finite) (h : ∀ X ∈ S, K.small X) :
    K.small (⋃₀ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using K.empty
  | @insert X S hn hS ih =>
    rw [sUnion_insert]
    exact K.union (h X (mem_insert _ _)) (ih (fun Y hY ↦ h Y (mem_insert_of_mem _ hY)))

lemma positive_nonempty {X : Set α} (h : ¬ K.small X) : X.Nonempty := by
  by_contra hn
  exact h ((not_nonempty_iff_eq_empty.mp hn).symm ▸ K.empty)

lemma remove_small {X N : Set α} (hX : ¬ K.small X) (hN : K.small N) :
    ¬ K.small (X \ N) := by
  intro h
  apply hX
  exact K.mono (K.union hN h) (by intro x hx; by_cases hn : x ∈ N; exact Or.inl hn; exact Or.inr ⟨hx, hn⟩)

lemma modSubset_trans {X Y Z : Set α} (hXY : K.ModSubset X Y) (hYZ : K.ModSubset Y Z) :
    K.ModSubset X Z := by
  exact K.mono (K.union hXY hYZ) (by intro x; simp only [Set.mem_sdiff, mem_union]; tauto)

end SubsetIdeal

lemma forbidden_finite_avoidance {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α)
    (hpattern : ∀ F H : Finset ι, Disjoint F H → ¬ K.small (columnPattern G F H))
    {N : Set α} (hN : K.small N) (F : Finset ι) {Z : Set (Set α)}
    (hZ : Z.Finite) (hforbid : ∀ z ∈ Z, Forbidden K G z) :
    ({x | (∀ t ∈ F, x ∈ G t)} \ (N ∪ ⋃₀ Z)).Nonempty := by
  classical
  have hchoose : ∀ z : Z, ∃ t, t ∉ F ∧ K.ModSubset z.val (G t) := by
    intro z
    obtain ⟨t, ht, hnot⟩ := (hforbid z.val z.property).exists_notMem_finset F
    exact ⟨t, hnot, ht⟩
  choose t htF htK using hchoose
  let H : Finset ι := hZ.toFinset.attach.image (fun z ↦ t ⟨z.val, hZ.mem_toFinset.mp z.property⟩)
  have hH : ∀ z : Z, t z ∈ H := by
    intro z
    apply Finset.mem_image.mpr
    exact ⟨⟨z.val, hZ.mem_toFinset.mpr z.property⟩, by simp, rfl⟩
  have hdisj : Disjoint F H := by
    apply Finset.disjoint_left.mpr
    intro i hiF hiH
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hiH
    exact htF ⟨z.val, hZ.mem_toFinset.mp z.property⟩ hiF
  let P := columnPattern G F H
  have hp : ¬ K.small P := hpattern F H hdisj
  have hpz : ∀ z ∈ Z, K.small (P ∩ z) := by
    intro z hz
    apply K.mono (htK ⟨z, hz⟩)
    intro x hx
    exact ⟨hx.2, hx.1.2 _ (hH ⟨z, hz⟩)⟩
  have hsmall : K.small (N ∪ ⋃₀ ((fun z ↦ P ∩ z) '' Z)) :=
    K.union hN (K.finite_sUnion (hZ.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hpz z hz))
  obtain ⟨x, hxP, hxnot⟩ := K.positive_nonempty (K.remove_small hp hsmall)
  refine ⟨x, hxP.1, ?_⟩
  rintro (hxN | hxZ)
  · exact hxnot (Or.inl hxN)
  · obtain ⟨z, hz, hxz⟩ := mem_sUnion.mp hxZ
    exact hxnot (Or.inr (mem_sUnion.mpr ⟨P ∩ z, mem_image_of_mem _ hz, hxP, hxz⟩))

/-- The finite-intersection argument produces the required ultrafilter;
no countable completeness or continuum regularity is used. -/
lemma exists_rank_ultrafilter {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α)
    (hpattern : ∀ F H : Finset ι, Disjoint F H → ¬ K.small (columnPattern G F H)) :
    ∃ U : Ultrafilter α,
      (∀ N, K.small N → N ∉ U) ∧ (∀ t, G t ∈ U) ∧
      (∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite) := by
  classical
  let S : Set (Set α) := {s | (∃ N, K.small N ∧ s = Nᶜ) ∨
    (∃ t, s = G t) ∨ (∃ Z, Forbidden K G Z ∧ s = Zᶜ)}
  have hFIP : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Nonempty := by
    intro T hTS
    let Ns := {s ∈ T | ∃ N, K.small N ∧ s = Nᶜ}
    let Gs := {s ∈ T | ∃ t, s = G t}
    let Zs := {s ∈ T | ∃ Z, Forbidden K G Z ∧ s = Zᶜ}
    have hNs : ∀ s ∈ Ns, K.small sᶜ := by
      intro s hs
      obtain ⟨N, hN, rfl⟩ := (Finset.mem_filter.mp hs).2
      simpa using hN
    have hGs : ∀ s : {s // s ∈ Gs}, ∃ t, s.val = G t := fun s ↦ (Finset.mem_filter.mp s.property).2
    choose g hg using hGs
    let F : Finset ι := Gs.attach.image g
    let N : Set α := ⋃₀ ((fun s : Set α ↦ sᶜ) '' (↑Ns : Set (Set α)))
    let Z : Set (Set α) := (fun s : Set α ↦ sᶜ) '' (↑Zs : Set (Set α))
    have hN : K.small N := K.finite_sUnion (Ns.finite_toSet.image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact hNs s hs)
    have hZ : Z.Finite := Zs.finite_toSet.image _
    have hforbid : ∀ z ∈ Z, Forbidden K G z := by
      rintro z ⟨s, hs, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (Finset.mem_filter.mp hs).2
      simpa using hz
    obtain ⟨x, hxG, hxNZ⟩ := forbidden_finite_avoidance K G hpattern hN F hZ hforbid
    refine ⟨x, mem_sInter.mpr ?_⟩
    intro s hs
    rcases hTS hs with hsmall | hcol | hforb
    · have hNs' : s ∈ Ns := Finset.mem_filter.mpr ⟨hs, hsmall⟩
      by_contra hxs
      exact hxNZ (Or.inl (mem_sUnion.mpr ⟨sᶜ, mem_image_of_mem _ hNs', hxs⟩))
    · have hGs' : s ∈ Gs := Finset.mem_filter.mpr ⟨hs, hcol⟩
      have heq : s = G (g ⟨s, hGs'⟩) := hg ⟨s, hGs'⟩
      rw [heq]
      exact hxG _ (Finset.mem_image.mpr ⟨⟨s, hGs'⟩, by simp, rfl⟩)
    · have hZs' : s ∈ Zs := Finset.mem_filter.mpr ⟨hs, hforb⟩
      by_contra hxs
      exact hxNZ (Or.inr (mem_sUnion.mpr ⟨sᶜ, mem_image_of_mem _ hZs', hxs⟩))
  obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty S hFIP
  refine ⟨U, ?_, ?_, ?_⟩
  · intro N hN
    exact Ultrafilter.compl_mem_iff_notMem.mp (hU (Or.inl ⟨N, hN, rfl⟩))
  · intro t
    exact hU (Or.inr (Or.inl ⟨t, rfl⟩))
  · intro X hX
    by_contra hfin
    have hc : Xᶜ ∈ U := hU (Or.inr (Or.inr ⟨X, hfin, rfl⟩))
    exact (Ultrafilter.compl_mem_iff_notMem.mp hc) hX

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.OrdinalRank ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

namespace SubsetIdeal
variable {α : Type} (K : SubsetIdeal α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U)

end SubsetIdeal

namespace RankModel
variable {α : Type} (R : RankModel α)
end RankModel

section Construction
variable {α : Type}
variable (K : SubsetIdeal α) (G : CIndex → Set α) (U : Ultrafilter α)
  (hUK : ∀ N, K.small N → N ∉ U) (hG : ∀ t, G t ∈ U)
  (hfinite : ∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite)

lemma exists_large_enumeration [Countable α] [Infinite α] : ∃ F : CIndex → Set α,
    (∀ i, F i ∈ U) ∧ ∀ X, X ∈ U → ∃ i, F i = X := by
  classical
  obtain ⟨e, he⟩ := exists_set_enumeration α
  refine ⟨fun i ↦ if e i ∈ U then e i else univ, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h
    · exact h
    · exact univ_mem
  · intro X hX
    obtain ⟨i, hi⟩ := he X
    exact ⟨i, by simp [hi, hX]⟩

variable (F : CIndex → Set α) (hF : ∀ i, F i ∈ U)
  (hFs : ∀ X, X ∈ U → ∃ i, F i = X)

lemma ordinalRank_spec {X : Set α} (hX : X ∈ U) :
    K.ModSubset (F (ordinalRank K U F hFs X)) X := by
  rw [ordinalRank, dite_eq_left hX]
  exact (wellFounded_lt (α := CIndex)).min_mem {i | K.ModSubset (F i) X}
    (rank_candidates_nonempty K U F hFs hX)

lemma ordinalRank_le {X : Set α} (hX : X ∈ U) {i : CIndex} (hi : K.ModSubset (F i) X) :
    ordinalRank K U F hFs X ≤ i := by
  rw [ordinalRank, dite_eq_left hX]
  exact (wellFounded_lt (α := CIndex)).min_le (s := {index | K.ModSubset (F index) X}) hi

lemma ordinalRank_antitone {X Y : Set α} (hX : X ∈ U) (hY : Y ∈ U)
    (hXY : K.ModSubset X Y) : ordinalRank K U F hFs Y ≤ ordinalRank K U F hFs X :=
  ordinalRank_le K U F hFs hY (K.modSubset_trans (ordinalRank_spec K U F hFs hX) hXY)

include hG hfinite hF in
lemma ordinalRank_thinning (s X : Set α) (hsX : s ⊆ X) (hs : s ∉ U) (hX : X ∈ U)
    (γ : CIndex) : ∃ u, s ⊆ u ∧ u ⊆ X ∧ u ∈ U ∧ γ < ordinalRank K U F hFs u := by
  classical
  let Y (i : Iic γ) := F i ∩ (X \ s)
  have hY : ∀ i, Y i ∈ U := fun i ↦
    inter_mem (hF i) (inter_mem hX (Ultrafilter.compl_mem_iff_notMem.mpr hs))
  obtain ⟨t, ht⟩ := exists_avoid_finite_family (cindex_initial_segment γ)
    (fun i : Iic γ ↦ {t | K.ModSubset (Y i) (G t)}) (fun i ↦ hfinite _ (hY i))
  let u := s ∪ (X ∩ G t)
  have hu : u ∈ U := Filter.mem_of_superset (inter_mem hX (hG t)) subset_union_right
  refine ⟨u, subset_union_left, union_subset hsX inter_subset_left, hu, ?_⟩
  apply lt_of_not_ge
  intro hr
  let i : Iic γ := ⟨ordinalRank K U F hFs u, hr⟩
  apply ht i
  apply K.mono (ordinalRank_spec K U F hFs hu)
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  rintro (hxs | hxG)
  · exact hx.1.2.2 hxs
  · exact hx.2 hxG.2

include hUK hG hfinite in

lemma exists_rankModel [Countable α] [Infinite α] : ∃ R : RankModel α, R.ideal = K ∧ R.ultra = U := by
  classical
  obtain ⟨F, hF, hFs⟩ := exists_large_enumeration U
  refine ⟨⟨K, U, hUK, ordinalRank K U F hFs,
    ?_, ?_⟩, rfl, rfl⟩
  · exact fun _ _ hX hY hXY ↦ ordinalRank_antitone K U F hFs hX hY hXY
  · exact ordinalRank_thinning K G U hG hfinite F hF hFs

end Construction
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.BlockDensity ----
namespace OAI

section

open Set Filter Finset
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

lemma small_finite {X : Set E0} (hX : X.Finite) : Small X := by
  classical
  obtain ⟨N, hN⟩ := finite_subset_prefix hX
  have heq : density X =ᶠ[atTop] fun _ ↦ 0 := by
    filter_upwards [eventually_ge_atTop N] with m hm
    have hempty : traceFinset (wBlock m) X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h1 := (mem_prefix x N).mp (hN ((mem_traceFinset (wBlock m) X x).mp hx).2)
      have h2 := (mem_wBlock x m).mp ((mem_traceFinset (wBlock m) X x).mp hx).1
      omega
    simp [density, finiteDensity, hempty]
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Interpolation ----
namespace OAI

section

open Set Filter
open scoped Topology

namespace InfiniteMatroidCounterexample

lemma probeLiminf_mono {α : Type*} {f : ℕ → Set α → ℝ}
    {X Y : Set α} (h : ∀ n, f n X ≤ f n Y) :
    probeLiminf f X ≤ probeLiminf f Y := by
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr (h n))

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.LocalBases ----
namespace OAI

section

open Set Filter
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

lemma localLower_antichain (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalLower T → Y ∈ LocalLower T → X ⊆ Y → X = Y := by
  intro X Y hX hY hXY
  by_contra hne
  obtain ⟨e, heY, heX⟩ := Set.not_subset.mp (fun hYX ↦ hne (Subset.antisymm hXY hYX))
  have hs : probeLiminf (fProbe T) (insert e X) = probeLiminf (fProbe T) X + 1 := by
    have heq : insert e X \ X = {e} := by ext x; simp [heX]
    have he := finite_change_eventually (T := T) (subset_insert e X)
      (show (insert e X \ X).Finite by rw [heq]; exact finite_singleton e)
    simp only [heq, ncard_singleton, Nat.cast_one] at he
    simpa using probeLiminf_finite_change he
  have hm := probeLiminf_mono (fun n ↦ fProbe_mono T (Set.insert_subset heY hXY) n)
  rw [hs] at hm
  have : (0 : EReal) < probeLiminf (fProbe T) X + 1 := by
    have hh := EReal.add_lt_add_right_coe hX.2.1 1
    have hz : (-1 : EReal) + 1 = 0 := by
      change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = 0
      rw [← EReal.coe_add]
      norm_num
    simpa only [EReal.coe_one, hz] using hh
  exact (this.trans_le hm).not_ge hY.2.2

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.DensityIdeal ----
namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma Gpattern_kPositive (P N : Finset CIndex) (hPN : Disjoint P N) :
    ¬ KIdeal.small (columnPattern GColumn P N) := by
  classical
  rintro ⟨F,hF⟩
  let P' := F.image tagA ∪ P.image tagG
  let N' := N.image tagG
  have hd : Disjoint P' N' := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨v,hvN,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hu with hu|hu
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hu
      have : (0 : Fin 3) = 2 := congrArg Prod.snd he
      have hv : (0 : ℕ) = 2 := congrArg Fin.val this
      omega
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hu
      have htv : t = v := congrArg Prod.fst he
      exact Finset.disjoint_left.mp hPN (htv ▸ ht) hvN
  apply signed_columns_positive P' N' hd
  apply dSmall_mono hF
  intro x hx
  refine ⟨⟨?_,?_⟩, ?_⟩
  · intro t ht
    exact hx.1 _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))
  · intro t ht
    exact hx.2 _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
  · intro t ht
    exact hx.1 _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))

lemma exists_concrete_rank : ∃ R : RankModel D, R.ideal = KIdeal := by
  obtain ⟨U,hUK,hG,hfinite⟩ := exists_rank_ultrafilter KIdeal GColumn Gpattern_kPositive
  obtain ⟨R,hK,_⟩ := exists_rankModel KIdeal GColumn U hUK hG hfinite
  exact ⟨R,hK⟩

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.BasisExtension ----
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma localLower_swap {T B : Set E0} (hB : B ∈ LocalLower T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalLower T := by
  have heq : B \ (B \ {e}) = {e} := by ext x; simp only [Set.mem_sdiff, Set.mem_singleton_iff]; aesop
  have hfq : insert f (B \ {e}) \ (B \ {e}) = {f} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    have : f ∉ B \ {e} := fun h ↦ hf h.1
    aesop
  have h1 := finite_change_eventually (T := T) (Set.sdiff_subset : B \ {e} ⊆ B)
    (show (B \ (B \ {e})).Finite by rw [heq]; exact finite_singleton e)
  have h2 := finite_change_eventually (T := T) (subset_insert f (B \ {e}))
    (show (insert f (B \ {e}) \ (B \ {e})).Finite by rw [hfq]; exact finite_singleton f)
  simp only [heq, hfq, ncard_singleton, Nat.cast_one] at h1 h2
  have hevent : ∀ᶠ n in atTop, fProbe T n (insert f (B \ {e})) = fProbe T n B + 0 := by
    filter_upwards [h1,h2] with n hn1 hn2
    rw [hn2, hn1, add_zero]
  have hlim := probeLiminf_finite_change hevent
  simp only [EReal.coe_zero, add_zero] at hlim
  refine ⟨?_,by simpa only [LowerBasis,hlim] using hB.2⟩
  have hclass := sameClass_add (sameClass_delete hB.1 (small_finite (finite_singleton e)))
    (small_finite (finite_singleton f))
  simpa only [Set.union_singleton] using hclass

lemma localRule_class {s : Bool} {T X : Set E0} (h : X ∈ LocalRule s T) : SameClass T X := by
  cases s with
  | false => exact h.1
  | true =>
    change Xᶜ ∈ LocalLower Tᶜ at h
    simpa using sameClass_compl h.1

lemma localRule_antichain (s : Bool) (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalRule s T → Y ∈ LocalRule s T → X ⊆ Y → X = Y := by
  cases s with
  | false => exact localLower_antichain T
  | true =>
    intro X Y hX hY hXY
    have he := localLower_antichain Tᶜ hY hX (compl_subset_compl.mpr hXY)
    exact compl_injective he.symm

lemma localRule_swap {s : Bool} {T B : Set E0} (hB : B ∈ LocalRule s T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalRule s T := by
  cases s with
  | false => exact localLower_swap hB e he f hf
  | true =>
    have hc : (insert f (B \ {e}))ᶜ = insert e (Bᶜ \ {f}) := by
      ext x
      simp only [mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      have hx1 : x = e → x ∈ B := fun h ↦ h ▸ he
      have hx2 : x = f → x ∉ B := fun h ↦ h ▸ hf
      tauto
    change (insert f (B \ {e}))ᶜ ∈ LocalLower Tᶜ
    rw [hc]
    change Bᶜ ∈ LocalLower Tᶜ at hB
    exact localLower_swap hB f hf e (by simpa using he)

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Zones ----
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

namespace RankModel
variable (R : RankModel D)

variable (hK : R.ideal = KIdeal)
include hK
lemma admissible_sameClass {T X : Set E0} (hT : R.Admissible T) (hX : SameClass T X) : R.Admissible X :=
  ((R.status_invariant hK (small_kSmall0 hX)).2.2).mpr hT

end RankModel
namespace RankModel
variable (R : RankModel D)

end RankModel
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Prototype ----
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma small_sdiff_of_class_subset {T S X Y : Set E0} (hX : SameClass T X)
    (hY : SameClass S Y) (hXY : X ⊆ Y) : Small (T \ S) := by
  apply small_subset (small_union hX hY)
  intro x hx
  have hxy := @hXY x
  simp only [Set.mem_sdiff,Set.mem_union,Set.mem_symmDiff] at hx ⊢
  tauto

lemma prototypeBases_mono {P Q : Set Prototype} (hPQ : P ⊆ Q) : PrototypeBases P ⊆ PrototypeBases Q := by
  rintro B ⟨p,hp,hB⟩
  exact ⟨p,hPQ hp,hB⟩
namespace RankModel
variable (R : RankModel D)

lemma bases_compl_closed {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → Bᶜ ∈ PrototypeBases P := by
  rintro B ⟨p,hp,hB⟩
  exact ⟨flipPrototype p,hP.flip_closed p hp,localRule_compl hB⟩

lemma bases_antichain {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B C⦄, B ∈ PrototypeBases P → C ∈ PrototypeBases P → B ⊆ C → B = C := by
  rintro B C ⟨p,hp,hB⟩ ⟨q,hq,hC⟩ hBC
  by_cases he : p = q
  · subst q
    exact localRule_antichain p.2 p.1 hB hC hBC
  · exact (hP.separated p hp q hq he
      (small_sdiff_of_class_subset (localRule_class hB) (localRule_class hC) hBC)).elim

lemma bases_swap {P : Set Prototype} :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → ∀ e ∈ B, ∀ f ∉ B, insert f (B \ {e}) ∈ PrototypeBases P := by
  rintro B ⟨p,hp,hB⟩ e he f hf
  exact ⟨p,hp,localRule_swap hB e he f hf⟩

variable (hK : R.ideal = KIdeal)
include hK
lemma bases_admissible {P : Set Prototype} (hP : R.GoodPrototypes P) :
    ∀ ⦃B⦄, B ∈ PrototypeBases P → R.Admissible B := by
  rintro B ⟨p,hp,hB⟩
  exact R.admissible_sameClass hK (hP.admissible p hp) (localRule_class hB)

end RankModel
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.TransfiniteConstruction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma stage_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    stagePrototypes (f b) ⊆ pastPrototypes f a := by
  intro p hp
  exact mem_iUnion.mpr ⟨⟨b,h⟩,hp⟩
lemma stage_subset_initial {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b ≤ a) :
    stagePrototypes (f b) ⊆ initialPrototypes f a := by
  rcases h.lt_or_eq with h|rfl
  · exact (stage_subset_past h).trans subset_union_left
  · exact subset_union_right
lemma initial_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    initialPrototypes f b ⊆ pastPrototypes f a := by
  rintro p (hp|hp)
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact stage_subset_past (c.2.trans h) hc
  · exact stage_subset_past h hp
lemma initial_subset_all (f : CIndex → Option (Set E0)) (a : CIndex) :
    initialPrototypes f a ⊆ allPrototypes f := by
  rintro p (hp|hp)
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨c,hc⟩
  · exact mem_iUnion.mpr ⟨a,hp⟩
lemma exists_interval_enumeration :
    ∃ e : CIndex → (Set E0 × Set E0), Function.Surjective e := by
  classical
  obtain ⟨e,he⟩ := exists_set_enumeration (E0 × Bool)
  refine ⟨fun a ↦ ({x | (x,false) ∈ e a},{x | (x,true) ∈ e a}),?_⟩
  rintro ⟨I,Y⟩
  obtain ⟨a,ha⟩ := he {p | if p.2 then p.1 ∈ Y else p.1 ∈ I}
  exact ⟨a,by simp [ha]⟩

namespace RankModel
variable (R : RankModel D)

lemma good_past_of_initial (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : ∀ b < a, R.GoodPrototypes (initialPrototypes f b)) :
    R.GoodPrototypes (pastPrototypes f a) := by
  constructor
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact (h b b.2).admissible p (Or.inr hb)
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact initial_subset_past b.2 ((h b b.2).flip_closed p (Or.inr hb))
  · intro p hp q hq hne
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    obtain ⟨c,hc⟩ := mem_iUnion.mp hq
    have hg := h (max b.1 c.1) (max_lt b.2 c.2)
    exact hg.separated p (stage_subset_initial (le_max_left _ _) hb)
      q (stage_subset_initial (le_max_right _ _) hc) hne

lemma good_all_of_initial (f : CIndex → Option (Set E0))
    (h : ∀ a, R.GoodPrototypes (initialPrototypes f a)) :
    R.GoodPrototypes (allPrototypes f) := by
  constructor
  · intro p hp
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    exact (h a).admissible p (Or.inr ha)
  · intro p hp
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    exact initial_subset_all f a ((h a).flip_closed p (Or.inr ha))
  · intro p hp q hq hne
    obtain ⟨a,ha⟩ := mem_iUnion.mp hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hq
    exact (h (max a b)).separated p (stage_subset_initial (le_max_left _ _) ha)
      q (stage_subset_initial (le_max_right _ _) hb) hne

variable (hK : R.ideal = KIdeal)
include hK
lemma assembled_eq (e : CIndex → (Set E0 × Set E0)) (a : CIndex) :
    R.assembled hK e a = R.assemblyStep hK e a (fun b ↦ R.assembled hK e b) :=
  WellFounded.fix_eq _ _ _

lemma assemblyStep_spec (e : CIndex → (Set E0 × Set E0)) (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : R.GoodPrototypes (pastPrototypes f a)) :
    R.GoodPrototypes (pastPrototypes f a ∪ stagePrototypes (R.assemblyStep hK e a (fun b ↦ f b))) ∧
      ((e a).1 ⊆ (e a).2 →
        Meets (PrototypeBases (pastPrototypes f a ∪ stagePrototypes (R.assemblyStep hK e a (fun b ↦ f b))))
          (e a).1 (e a).2) := by
  classical
  unfold pastPrototypes at h ⊢
  simp only [assemblyStep,dite_eq_left h]
  exact Classical.choose_spec (R.exists_stage hK _ h
    (finite_union_small (cindex_predecessors a) _ (fun b ↦ stagePrototypes_finite (f b))) _ _)

lemma assembled_good_initial (e : CIndex → (Set E0 × Set E0)) (a : CIndex) :
    R.GoodPrototypes (initialPrototypes (R.assembled hK e) a) := by
  induction a using (wellFounded_lt (α := CIndex)).induction with
  | h a ih =>
    have hg := R.good_past_of_initial (R.assembled hK e) a ih
    have hs := (R.assemblyStep_spec hK e (R.assembled hK e) a hg).1
    change R.GoodPrototypes (pastPrototypes (R.assembled hK e) a ∪ stagePrototypes (R.assembled hK e a))
    rw [R.assembled_eq hK e a]
    exact hs

lemma assembled_meets (e : CIndex → (Set E0 × Set E0)) (a : CIndex)
    (hIY : (e a).1 ⊆ (e a).2) :
    Meets (PrototypeBases (allPrototypes (R.assembled hK e))) (e a).1 (e a).2 := by
  have hg := R.good_past_of_initial (R.assembled hK e) a
    (fun b _ ↦ R.assembled_good_initial hK e b)
  have hs := (R.assemblyStep_spec hK e (R.assembled hK e) a hg).2 hIY
  rw [← R.assembled_eq hK e a] at hs
  exact meets_mono (prototypeBases_mono (initial_subset_all _ _)) hs

/-- The continuum recursion meets every interval and preserves all old classes. -/
lemma exists_complete_prototypes : ∃ P : Set Prototype,
    R.GoodPrototypes P ∧ ∀ I Y, I ⊆ Y → Meets (PrototypeBases P) I Y := by
  obtain ⟨e,he⟩ := exists_interval_enumeration
  refine ⟨allPrototypes (R.assembled hK e),R.good_all_of_initial _ (R.assembled_good_initial hK e),?_⟩
  intro I Y hIY
  obtain ⟨a,ha⟩ := he (I,Y)
  have hs := R.assembled_meets hK e a (by simpa [ha] using hIY)
  simpa [ha] using hs

lemma exists_basisSystem : ∃ S : BasisSystem E0, ∀ B ∈ S.bases, R.Admissible B := by
  obtain ⟨P,hP,hmeet⟩ := R.exists_complete_prototypes hK
  obtain ⟨B,hB,_⟩ := hmeet ∅ univ (empty_subset _)
  refine ⟨⟨PrototypeBases P,⟨B,hB⟩,R.bases_antichain hP,R.bases_compl_closed hP,
    bases_swap,fun I Y hIY _ ↦ hmeet I Y hIY⟩,?_⟩
  intro B hB
  exact R.bases_admissible hK hP hB

end RankModel
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.RankDescent ----
namespace OAI

section
open Set Filter Matroid
namespace InfiniteMatroidCounterexample

lemma raySlice_central {α : Type*} (I : Set (ℤ × α)) :
    raySlice I (-1) false = (raySlice I 0 false)ᶜ := by
  ext d
  simp [raySlice,assignment,bundleAt]

lemma raySlice_right {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (hn : 0 ≤ n) :
    raySlice I (n+1) false = (raySlice I n true)ᶜ := by
  have hn0 : ¬ n < 0 := not_lt.mpr hn
  have hn1 : ¬ n+1 < 0 := by omega
  by_cases hp : n % 2 = 0
  · have hp' : ¬ (n+1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn0,hn1,hp,hp']
  · have hp' : (n+1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn0,hn1,hp,hp']

lemma raySlice_left {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (hn : n < 0) :
    raySlice I (n-1) false = (raySlice I n true)ᶜ := by
  have hn1 : n-1 < 0 := by omega
  by_cases hp : n % 2 = 0
  · have hp' : ¬ (n-1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn,hn1,hp,hp']
  · have hp' : (n-1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn,hn1,hp,hp']

lemma raySlice_step {α : Type*} (I : Set (ℤ × α)) (left : Bool) (k : ℕ) :
    raySlice I (rayVertex left (k+1)) false = (raySlice I (rayVertex left k) true)ᶜ := by
  cases left with
  | false => simpa only [rayVertex,Bool.false_eq_true,ite_false,Nat.cast_add,Nat.cast_one] using
      raySlice_right I (k : ℤ) (Int.natCast_nonneg k)
  | true =>
    have he : rayVertex true (k+1) = rayVertex true k - 1 := by simp [rayVertex]; ring
    rw [he]
    exact raySlice_left I _ (by simp [rayVertex]; omega)

section Descent
variable {α β : Type*} [LinearOrder β] [WellFoundedLT β]
variable (Q : Matroid (α × Bool)) (U : Ultrafilter α) (ρ : Set α → β)
variable (hanti : ∀ ⦃X Y : Set α⦄, X ∈ U → Y ∈ U → X ⊆ Y → ρ Y ≤ ρ X)
variable (hbasis : ∀ B, Q.IsBase B → (Prod.mk · false) ⁻¹' B ∈ U →
  ((Prod.mk · true) ⁻¹' B)ᶜ ∈ U ∧ ρ ((Prod.mk · true) ⁻¹' B)ᶜ < ρ ((Prod.mk · false) ⁻¹' B))
include hanti hbasis

omit [WellFoundedLT β] in
lemma independent_rank_step {X : Set (α × Bool)} (hX : Q.Indep X)
    (hl : (Prod.mk · false) ⁻¹' X ∈ U) :
    ((Prod.mk · true) ⁻¹' X)ᶜ ∈ U ∧ ρ ((Prod.mk · true) ⁻¹' X)ᶜ < ρ ((Prod.mk · false) ⁻¹' X) := by
  obtain ⟨B,hB,hXB⟩ := hX.exists_isBase_superset
  have hlu : (Prod.mk · false) ⁻¹' B ∈ U := mem_of_superset hl (preimage_mono hXB)
  obtain ⟨hy,hlt⟩ := hbasis B hB hlu
  have hyx : ((Prod.mk · true) ⁻¹' B)ᶜ ⊆ ((Prod.mk · true) ⁻¹' X)ᶜ :=
    compl_subset_compl.mpr (preimage_mono hXB)
  have hr : ((Prod.mk · true) ⁻¹' X)ᶜ ∈ U := mem_of_superset hy hyx
  refine ⟨hr,?_⟩
  exact lt_of_le_of_lt (hanti hy hr hyx)
    (lt_of_lt_of_le hlt (hanti hl hlu (preimage_mono hXB)))

lemma no_independent_partition {I : Set (ℤ × α)} (h0 : (rayMatroid Q false).Indep I)
    (h1 : (rayMatroid Q true).Indep Iᶜ) : False := by
  have hstart : ∃ left : Bool, raySlice I (rayVertex left 0) false ∈ U := by
    by_cases hc : raySlice I 0 false ∈ U
    · exact ⟨false,hc⟩
    · refine ⟨true,?_⟩
      change raySlice I (-1) false ∈ U
      rw [raySlice_central]
      exact Ultrafilter.compl_mem_iff_notMem.mpr hc
  obtain ⟨left,hstart⟩ := hstart
  let x (k : ℕ) := raySlice I (rayVertex left k) false
  have hstep (k : ℕ) (hk : x k ∈ U) : x (k+1) ∈ U ∧ ρ (x (k+1)) < ρ (x k) := by
    have hi := assignment_indep Q h0 h1 (rayVertex left k)
    have hs := independent_rank_step Q U ρ hanti hbasis hi hk
    change (raySlice I (rayVertex left k) true)ᶜ ∈ U ∧
      ρ (raySlice I (rayVertex left k) true)ᶜ < ρ (x k) at hs
    simpa only [x,raySlice_step] using hs
  have hx : ∀ k, x k ∈ U := by
    intro k
    induction k with
    | zero => exact hstart
    | succ k ih => exact (hstep k ih).1
  have hd : ∀ k, ρ (x (k+1)) < ρ (x k) := fun k ↦ (hstep k (hx k)).2
  exact (wellFounded_iff_isEmpty_descending_chain.mp (wellFounded_lt (α := β))).false ⟨fun k ↦ ρ (x k),hd⟩

lemma no_independent_cover (I J : Set (ℤ × α))
    (hI : (rayMatroid Q false).Indep I) (hJ : (rayMatroid Q true).Indep J) : I ∪ J ≠ univ := by
  intro hcover
  have hIJ : Iᶜ ⊆ J := by
    intro x hx
    have hm : x ∈ I ∪ J := hcover.symm ▸ mem_univ x
    exact hm.resolve_left hx
  exact no_independent_partition Q U ρ hanti hbasis hI (hJ.subset hIJ)

end Descent
end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.PackingCovering ----
namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

lemma contraction_indep_compl_spanning {α : Type*} (M : Matroid α) (hM : M.dual = M)
    {C I : Set α} (hI : (contractOnto M C).Indep I) :
    (M ↾ C).Spanning (C \ I) := by
  unfold contractOnto at hI
  rw [hM] at hI
  have h : (M ↾ C).Coindep I := hI
  simpa only [Matroid.restrict_ground_eq] using h.compl_spanning

lemma spanning_union_of_restrictions {α : Type*} (M : Matroid α) (hE : M.E = univ)
    {P C S T : Set α} (hPC : P ∪ C = univ) (hSP : S ⊆ P) (hTC : T ⊆ C)
    (hS : (M ↾ P).Spanning S) (hT : (M ↾ C).Spanning T) : M.Spanning (S ∪ T) := by
  apply (M.spanning_iff_ground_subset_closure (by rw [hE]; exact subset_univ _)).mpr
  have hPg : P ⊆ M.E := by rw [hE]; exact subset_univ _
  have hCg : C ⊆ M.E := by rw [hE]; exact subset_univ _
  have hp := (M.restrict_spanning_iff hSP hPg).mp hS
  have hc := (M.restrict_spanning_iff hTC hCg).mp hT
  rw [hE,←hPC]
  exact union_subset (hp.trans (M.closure_mono subset_union_left))
    (hc.trans (M.closure_mono subset_union_right))

lemma indep_compl_of_selfDual_spanning {α : Type*} (M : Matroid α) (hE : M.E = univ)
    (hM : M.dual = M) {A : Set α} (hA : M.Spanning A) : M.Indep Aᶜ := by
  have h : M.dual.Indep (M.E \ A) := hA.compl_coindep
  simpa only [hM,hE,← Set.compl_eq_univ_sdiff] using h

/-- The mixed packing/covering reduction, not merely the two pure cases. -/
lemma independent_cover_of_packing_covering {α : Type*} (M₀ M₁ : Matroid α)
    (hE₀ : M₀.E = univ) (hE₁ : M₁.E = univ) (hM₀ : M₀.dual = M₀) (hM₁ : M₁.dual = M₁)
    (h : HasPackingCovering M₀ M₁) :
    ∃ J₀ J₁ : Set α, M₀.Indep J₀ ∧ M₁.Indep J₁ ∧ J₀ ∪ J₁ = univ := by
  classical
  obtain ⟨P,C,S₀,S₁,I₀,I₁,hdPC,hPC,_,hS₀P,hS₁P,hdS,hS₀,hS₁,_,_,hI₀,hI₁,hIC⟩ := h
  have hPC' : P ∪ C = univ := hPC.trans hE₀
  have hT₀ := contraction_indep_compl_spanning M₀ hM₀ hI₀
  have hT₁ := contraction_indep_compl_spanning M₁ hM₁ hI₁
  have hA₀ := spanning_union_of_restrictions M₀ hE₀ hPC' hS₀P sdiff_subset hS₀ hT₀
  have hA₁ := spanning_union_of_restrictions M₁ hE₁ hPC' hS₁P sdiff_subset hS₁ hT₁
  have hd : Disjoint (S₀ ∪ (C \ I₀)) (S₁ ∪ (C \ I₁)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact Set.disjoint_left.mp hdS hx hy
    · exact Set.disjoint_left.mp hdPC (hS₀P hx) hy.1
    · exact Set.disjoint_left.mp hdPC (hS₁P hy) hx.1
    · have hm : x ∈ I₀ ∪ I₁ := hIC.symm ▸ hx.1
      exact hm.elim hx.2 hy.2
  refine ⟨_,_,indep_compl_of_selfDual_spanning M₀ hE₀ hM₀ hA₀,
    indep_compl_of_selfDual_spanning M₁ hE₁ hM₁ hA₁,?_⟩
  rw [←Set.compl_inter,hd.inter_eq,Set.compl_empty]

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.Main ----
namespace OAI

section

open Set Filter Matroid
namespace InfiniteMatroidCounterexample

theorem main :
    Countable E ∧ Infinite E ∧
    ∃ M₀ M₁ : Matroid E,
      M₀.E = Set.univ ∧ M₁.E = Set.univ ∧
      M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ HasPackingCovering M₀ M₁ := by
  obtain ⟨R,hK⟩ := exists_concrete_rank
  obtain ⟨S,hS⟩ := R.exists_basisSystem hK
  let Q : Matroid E0 := S.matroid
  have hE : Q.E = Set.univ := S.ground
  have hQ : Q.dual = Q := S.self_dual
  have hanti : ∀ ⦃X Y : Set D⦄, X ∈ R.ultra → Y ∈ R.ultra → X ⊆ Y →
      R.rank Y ≤ R.rank X :=
    fun _ _ hX hY hXY ↦ R.antitone hX hY (R.ideal.modSubset_of_subset hXY)
  have hb : ∀ B, Q.IsBase B → (Prod.mk · false) ⁻¹' B ∈ R.ultra →
      ((Prod.mk · true) ⁻¹' B)ᶜ ∈ R.ultra ∧
      R.rank ((Prod.mk · true) ⁻¹' B)ᶜ < R.rank ((Prod.mk · false) ⁻¹' B) := by
    intro B hB hl
    have ha : R.Admissible B := hS B ((S.isBase_iff B).mp hB)
    rcases ha with ha | ha
    · exact ha.2
    · exact (ha.1 hl).elim
  have hn : ∀ I J : Set E, (rayMatroid Q false).Indep I →
      (rayMatroid Q true).Indep J → I ∪ J ≠ Set.univ :=
    no_independent_cover Q R.ultra R.rank hanti hb
  refine ⟨inferInstance, inferInstance, rayMatroid Q false, rayMatroid Q true,
    rayMatroid_ground Q hE false, rayMatroid_ground Q hE true,
    rayMatroid_selfDual Q hE hQ false, rayMatroid_selfDual Q hE hQ true, hn, ?_⟩
  intro h
  obtain ⟨I,J,hI,hJ,hIJ⟩ := independent_cover_of_packing_covering
    (rayMatroid Q false) (rayMatroid Q true)
    (rayMatroid_ground Q hE false) (rayMatroid_ground Q hE true)
    (rayMatroid_selfDual Q hE hQ false) (rayMatroid_selfDual Q hE hQ true) h
  exact hn I J hI hJ hIJ

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.SeparateCounterexamples ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

theorem separate_covering_packing_counterexamples :
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ CoveringConjectureFor F M) ∧
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ PackingConjectureFor F M) := by
  obtain ⟨_, _, M₀, M₁, hE₀, hE₁, _, _, _, hno⟩ := main
  let M : Bool → Matroid E := fun i ↦ if i then M₁ else M₀
  have hg : ∀ i, (M i).E = univ := by
    intro i
    cases i <;> simp [M, hE₀, hE₁]
  have hn : ¬ HasPackingCovering (M false) (M true) := hno
  obtain ⟨C, N, hN, hnc, hcond⟩ := separate_covering_of_no_packingCovering hg hn
  refine ⟨⟨C, N, hN, fun h ↦ hnc (h.mpr hcond)⟩,
    ⟨C, fun i ↦ (N i).dual, ?_, ?_⟩⟩
  · simpa only [Matroid.dual_ground] using hN
  · exact separate_packing_of_covering_counterexample hN hnc hcond

end InfiniteMatroidCounterexample

end OAI

-- ---- mission target ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid

theorem solution :
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ CoveringConjectureFor F M) ∧
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ PackingConjectureFor F M) := by
  first
    | exact OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples
    | (apply OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples <;> assumption)
    | (intros; apply OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples <;> assumption)
