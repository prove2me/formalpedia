-- Prove2me | solution 1 for OAI.HardSphere.condensation_with_mixed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:30:28.644269+00:00
-- url     : https://prove2.me/submissions/45c9a16e-2698-4c11-abe3-ab9e2768e90f

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_Groups_physical_ground_bad_supply
import Theorems.Thm_OAI_HardSphere_Groups_physical_group_common_comparison
import Theorems.Thm_OAI_HardSphere_Groups_physical_modulus_from_gains
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_probability
import Theorems.Thm_OAI_HardSphere_physical_uniform_phase_error

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadGraph
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma badComponent_eq_of_reachable (G : SimpleGraph V) (B : Finset V) {x y : V}
    (h : (badGraph G B).Reachable x y) : badComponent G B x=badComponent G B y := by
  ext z
  simp only [mem_badComponent]
  exact ⟨fun ⟨hz,hxz⟩ ↦ ⟨hz,h.symm.trans hxz⟩,
    fun ⟨hz,hyz⟩ ↦ ⟨hz,h.trans hyz⟩⟩

lemma badComponents_disjoint (G : SimpleGraph V) (B : Finset V) :
    (↑(badComponents G B) : Set (Finset V)).PairwiseDisjoint id := by
  rw [Finset.pairwiseDisjoint_iff]
  rintro C hC D hD ⟨z,hz⟩
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨hzx,hzy⟩ := Finset.mem_inter.mp hz
  exact badComponent_eq_of_reachable G B
    (((mem_badComponent G B x z).mp hzx).2.trans
      ((mem_badComponent G B y z).mp hzy).2.symm)

lemma badComponents_subset (G : SimpleGraph V) (B : Finset V) {C : Finset V}
    (hC : C∈badComponents G B) : C⊆B := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
  exact badComponent_subset G B x

lemma badComponents_candidate (G : SimpleGraph V) (B : Finset V) :
    badComponents G B ⊆ candidateSets G := by
  intro C hC
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hC
  simp only [candidateSets, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨x,mem_own_badComponent G B hx⟩, ?_⟩
  intro y hy z hz
  have hxy := reachable_inside_component G B ((mem_badComponent G B x y).mp hy).2
  have hxz := reachable_inside_component G B ((mem_badComponent G B x z).mp hz).2
  exact hxy.symm.trans hxz

omit [Fintype V] [DecidableEq V] in
lemma frontierHead_mem (s : ExploreState V) (h : s.2.Nonempty) :
    frontierHead s h ∈ s.2 := h.choose_spec

omit [Fintype V] in
lemma invariant_initial (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) :
    ExploreInvariant G F r (∅,{r}) := by
  simp [ExploreInvariant,hr]

lemma invariant_step (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) : ExploreInvariant G F r (exploreStep G F s) := by
  rcases hs with ⟨h₁,h₂,hd,hr,hclosed⟩
  by_cases h : s.2.Nonempty
  · let x := frontierHead s h
    have hx : x∈s.2 := frontierHead_mem s h
    have hxF : x∈F := h₂ hx
    have hseen : s.1∪s.2 ⊆ (insert x s.1) ∪
        ((s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1) := by
      intro y hy
      by_cases hyp : y∈insert x s.1
      · exact Finset.mem_union_left _ hyp
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ (by
            rcases Finset.mem_union.mp hy with hy|hy
            · exact False.elim (hyp (Finset.mem_insert_of_mem hy))
            · exact hy),hyp⟩)
    simp only [exploreStep,dite_eq_left h,exploreNext]
    change ExploreInvariant G F r
      (insert x s.1, (s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1)
    refine ⟨Finset.insert_subset hxF h₁, ?_, (Finset.disjoint_left.mpr (fun _ hy hz ↦ (Finset.mem_sdiff.mp hz).2 hy)), hseen hr, ?_⟩
    · intro y hy
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hy).1 with hy|hy
      · exact h₂ hy
      · exact (Finset.mem_inter.mp hy).2
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl|hy
      · by_cases hzp : z∈insert x s.1
        · exact Finset.mem_union_left _ hzp
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset x z).mpr hyz,hz⟩),hzp⟩)
      · exact hseen (hclosed y hy z hz hyz)
  · simpa only [exploreStep,dite_eq_right h] using
      (show ExploreInvariant G F r s from ⟨h₁,h₂,hd,hr,hclosed⟩)

lemma exploration_invariant (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) (n : ℕ) :
    ExploreInvariant G F r (exploration G F r n) := by
  induction n with
  | zero => exact invariant_initial G F hr
  | succ n ih => exact invariant_step G F r _ ih

omit [Fintype V] in
lemma invariant_empty_frontier (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) (he : s.2=∅) : s.1=F := by
  apply Finset.Subset.antisymm hs.1
  intro y hy
  have hreach := hconn y hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => simpa only [he,Finset.union_empty] using hs.2.2.2.1
  | @tail y z _ hyz ih =>
      simpa only [he,Finset.union_empty] using hs.2.2.2.2 y (ih hyz.1) z hyz.2.1 hyz.2.2

lemma exploreStep_card (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) (h : s.2.Nonempty) :
    (exploreStep G F s).1.card=s.1.card+1 := by
  have hx := frontierHead_mem s h
  have hn : frontierHead s h ∉ s.1 := fun hh ↦ Finset.disjoint_left.mp hs.2.2.1 hh hx
  simp only [exploreStep,dite_eq_left h,exploreNext]
  exact Finset.card_insert_of_notMem hn

lemma exploration_covers (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) :
    (exploration G F r F.card).1=F := by
  have hprogress (n : ℕ) : n≤(exploration G F r n).1.card ∨ (exploration G F r n).1=F := by
    induction n with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ n ih =>
      have hs := exploration_invariant G F hr n
      by_cases h : (exploration G F r n).2.Nonempty
      · by_cases hc : (exploration G F r n).1=F
        · have hx := frontierHead_mem _ h
          have hp := hs.2.1 hx
          exact False.elim (Finset.disjoint_left.mp hs.2.2.1 (hc.ge hp) hx)
        · refine Or.inl ?_
          obtain hn|hn := ih
          · rw [exploration,exploreStep_card G F r _ hs h]
            omega
          · exact False.elim (hc hn)
      · apply Or.inr
        rw [exploration,exploreStep,dite_eq_right h]
        exact invariant_empty_frontier G F r _ hs hconn (Finset.not_nonempty_iff_eq_empty.mp h)
  rcases hprogress F.card with hc|hc
  · exact Finset.eq_of_subset_of_card_le (exploration_invariant G F hr F.card).1 hc
  · exact hc

lemma exploreStep_mem_possible (G : SimpleGraph V) (F : Finset V) (s : ExploreState V) :
    exploreStep G F s ∈ possibleSteps G s := by
  by_cases h : s.2.Nonempty
  · simp only [exploreStep,possibleSteps,dite_eq_left h]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_powerset.mpr (Finset.inter_subset_left),rfl⟩
  · simp only [exploreStep,possibleSteps,dite_eq_right h,Finset.mem_singleton]

lemma exploration_mem_possible (G : SimpleGraph V) (F : Finset V) (r : V) (n : ℕ) :
    exploration G F r n ∈ possibleStates G r n := by
  induction n with
  | zero => simp only [exploration,possibleStates,Finset.mem_singleton]
  | succ n ih => exact Finset.mem_biUnion.mpr ⟨_,ih,exploreStep_mem_possible G F _⟩

lemma possibleSteps_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (s : ExploreState V) :
    (possibleSteps G s).card ≤ 2^Δ := by
  by_cases h : s.2.Nonempty
  · simp only [possibleSteps,dite_eq_left h]
    calc
      _ ≤ (G.neighborFinset (frontierHead s h)).powerset.card := Finset.card_image_le
      _ = 2^(G.degree (frontierHead s h)) := by rw [Finset.card_powerset]; rfl
      _ ≤ 2^Δ := Nat.pow_le_pow_right (by omega) (hΔ _)
  · simp only [possibleSteps,dite_eq_right h,Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by omega)

lemma possibleStates_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (n : ℕ) :
    (possibleStates G r n).card ≤ (2^Δ)^n := by
  induction n with
  | zero => simp only [possibleStates,Finset.card_singleton,pow_zero,le_refl]
  | succ n ih =>
    calc
      _ ≤ ∑ s∈possibleStates G r n, (possibleSteps G s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s∈possibleStates G r n, 2^Δ :=
        Finset.sum_le_sum fun s _ ↦ possibleSteps_card_le G Δ hΔ s
      _ = (possibleStates G r n).card * 2^Δ := by simp
      _ ≤ (2^Δ)^n * 2^Δ := Nat.mul_le_mul_right _ ih
      _ = (2^Δ)^(n+1) := (pow_succ _ _).symm

lemma rootedAnimals_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (m : ℕ) :
    (rootedAnimals G r m).card ≤ (2^Δ)^m := by
  have hsub : rootedAnimals G r m ⊆ (possibleStates G r m).image Prod.fst := by
    intro F hF
    simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and] at hF
    rcases hF with ⟨hr,hm,hconn⟩
    refine Finset.mem_image.mpr ⟨exploration G F r m, exploration_mem_possible G F r m, ?_⟩
    rw [← hm]
    exact exploration_covers G F hr hconn
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (possibleStates_card_le G Δ hΔ r m))

omit [Fintype V] [DecidableEq V] in
lemma badGraph_mono (G : SimpleGraph V) {S F : Finset V} (h : S⊆F) :
    badGraph G S ≤ badGraph G F := by
  intro x y hxy
  exact ⟨h hxy.1,h hxy.2.1,hxy.2.2⟩

omit [Fintype V] in
lemma internal_boundary (G : SimpleGraph V) (F S : Finset V) {r y : V}
    (hr : r∈S) (hy : y∉S) (hp : (badGraph G F).Reachable r y) :
    ∃ x∈S, ∃ z∈F, z∉S ∧ G.Adj x z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp
  induction hp with
  | refl => exact False.elim (hy hr)
  | @tail y z _ hyz ih =>
      by_cases h : y∈S
      · exact ⟨y,h,z,hyz.2.1,hy,hyz.2.2⟩
      · exact ih h

omit [Fintype V] in
lemma connected_insert (G : SimpleGraph V) (S : Finset V) (r : V)
    (hconn : ∀ y∈S, (badGraph G S).Reachable r y)
    {x z : V} (hx : x∈S) (hxz : G.Adj x z) :
    ∀ y∈insert z S, (badGraph G (insert z S)).Reachable r y := by
  have hmono := badGraph_mono G (Finset.subset_insert z S)
  intro y hy
  rcases Finset.mem_insert.mp hy with he|hy
  · subst y
    exact ((hconn x hx).mono hmono).trans
      (show (badGraph G (insert z S)).Adj x z from
        ⟨Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _,hxz⟩).reachable
  · exact (hconn y hy).mono hmono

lemma exists_rooted_subanimal (G : SimpleGraph V) (F : Finset V) {r : V}
    (hr : r∈F) (hconn : ∀ y∈F, (badGraph G F).Reachable r y)
    (m : ℕ) (hm : 1 ≤ m) (hmF : m ≤ F.card) :
    ∃ S⊆F, S∈rootedAnimals G r m := by
  have hex (k : ℕ) (hk : k+1≤F.card) :
      ∃ S⊆F, r∈S ∧ S.card=k+1 ∧ ∀ y∈S, (badGraph G S).Reachable r y := by
    induction k with
    | zero =>
      refine ⟨{r},Finset.singleton_subset_iff.mpr hr,Finset.mem_singleton_self _,by simp,?_⟩
      intro y hy
      have : y=r := Finset.mem_singleton.mp hy
      subst y
      exact .refl r
    | succ k ih =>
      obtain ⟨S,hSF,hrS,hcard,hSconn⟩ := ih (by omega)
      have hlt : S.card<F.card := by omega
      obtain ⟨y,hyF,hyS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨x,hx,z,hzF,hzS,hxz⟩ := internal_boundary G F S hrS hyS (hconn y hyF)
      refine ⟨insert z S,Finset.insert_subset hzF hSF,Finset.mem_insert_of_mem hrS,
        by rw [Finset.card_insert_of_notMem hzS,hcard],connected_insert G S r hSconn hx hxz⟩
  obtain ⟨S,hS,hrS,hc,hconnS⟩ := hex (m-1) (by omega)
  refine ⟨S,hS,?_⟩
  simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hrS,by omega,hconnS⟩

omit [Fintype V] in
lemma prod_ite_mem (A B : Finset V) (w : V → ℝ≥0∞) :
    (∏ x∈A, if x∈B then w x else 0) = if A⊆B then ∏ x∈A, w x else 0 := by
  by_cases h : A⊆B
  · simp only [ite_eq_left h]
    exact Finset.prod_congr rfl fun x hx ↦ ite_eq_left (h hx)
  · rw [ite_eq_right h]
    obtain ⟨x,hx,hxb⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hx (ite_eq_right hxb)

omit [Fintype V] in

lemma component_event_bound (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (K : Finset V → Finset (Finset V))
    (hdisj : ∀ B, (↑(K B) : Set (Finset V)).PairwiseDisjoint id)
    (hsub : ∀ B F, F∈K B → F⊆B) (A : Finset (Finset V)) :
    (∑' B, if A⊆K B then μ B else 0) ≤ ∏ F∈A, p^F.card := by
  by_cases hex : ∃ B, A⊆K B
  · obtain ⟨B₀,hB₀⟩ := hex
    have hd : (↑A : Set (Finset V)).PairwiseDisjoint id :=
      by
      intro C hC D hD hCD
      exact hdisj B₀ (hB₀ hC) (hB₀ hD) hCD
    have hc : (A.biUnion id).card = ∑ F∈A, F.card := Finset.card_biUnion hd
    calc
      _ ≤ ∑' B, if A.biUnion id⊆B then μ B else 0 := by
        apply ENNReal.tsum_le_tsum
        intro B
        by_cases hB : A⊆K B
        · have hu : A.biUnion id⊆B := by
            intro x hx
            obtain ⟨F,hF,hxF⟩ := Finset.mem_biUnion.mp hx
            exact hsub B F (hB hF) hxF
          simp only [ite_eq_left hB,ite_eq_left hu]
          exact le_rfl
        · simp only [ite_eq_right hB]
          exact zero_le
      _ ≤ p^(A.biUnion id).card := hbad _
      _ = ∏ F∈A, p^F.card := by rw [hc,Finset.prod_pow_eq_pow_sum]
  · have hz : ∀ B, ¬ A⊆K B := by simpa only [not_exists] using hex
    simp only [ite_eq_right (hz _),tsum_zero]
    exact zero_le

theorem environment_product_bound (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (K : Finset V → Finset (Finset V))
    (hdisj : ∀ B, (↑(K B) : Set (Finset V)).PairwiseDisjoint id)
    (hsub : ∀ B F, F∈K B → F⊆B) (C : Finset (Finset V))
    (hC : ∀ B, K B⊆C) (w : Finset V → ℝ≥0∞) :
    (∑' B, μ B * ∏ F∈K B, (1+w F)) ≤ ∏ F∈C, (1+p^F.card*w F) := by
  have hp (B : Finset V) : (∏ F∈K B, (1+w F)) =
      ∏ F∈C, (1+if F∈K B then w F else 0) := by
    calc
      _ = ∏ F∈K B, (1+if F∈K B then w F else 0) :=
        Finset.prod_congr rfl fun F hF ↦ by rw [ite_eq_left hF]
      _ = _ := Finset.prod_subset (hC B) (by
        intro F _ hF
        simp only [ite_eq_right hF,add_zero])
  simp_rw [hp,Finset.prod_one_add,Finset.mul_sum]
  rw [tsum_fintype,Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  rw [← tsum_fintype (L := .unconditional _) (fun B : Finset V ↦ μ B * ∏ i∈A, if i∈K B then w i else 0)]
  simp_rw [prod_ite_mem]
  have he : (∑' B, μ B * if A⊆K B then ∏ F∈A, w F else 0) =
      (∑' B, if A⊆K B then μ B else 0) * ∏ F∈A,w F := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro B
    split_ifs <;> simp
  rw [he,Finset.prod_mul_distrib]
  exact mul_le_mul' (component_event_bound μ p hbad K hdisj hsub A) le_rfl

end HardSphere.Lattice
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Vertex
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

variable {A : Type*} [AddCommGroup A]

lemma coordinateRay_zero (x : Vertex) (i : Fin 3) (d : ℤ) :
    coordinateRay x i d 0=x := by ext j; simp [coordinateRay]

lemma coordinateRay_injective (x : Vertex) (i : Fin 3) (d : ℤ) (hd : d≠0) :
    Function.Injective (coordinateRay x i d) := by
  intro m n h
  have hv := congrFun h i
  simp only [coordinateRay, ite_true] at hv
  have : (m:ℤ)=(n:ℤ) := mul_left_cancel₀ hd (add_left_cancel hv)
  exact_mod_cast this

lemma coordinateRay_step (x : Vertex) (i : Fin 3) (d : ℤ) (hd : |d|=1) (n : ℕ) :
    nearestStep (coordinateRay x i d n) (coordinateRay x i d (n+1)) := by
  refine ⟨i, ?_, ?_⟩
  · simp only [coordinateRay, ite_true, Nat.cast_add, Nat.cast_one]
    have he : x i+d*(n:ℤ)-(x i+d*((n:ℤ)+1)) = -d := by ring
    rw [he, abs_neg, hd]
  · intro j hj
    simp only [coordinateRay, ite_eq_right hj]

lemma coordinateRay_reachable (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) (n : ℕ) :
    avoidingReach C x (coordinateRay x i d n) := by
  induction n with
  | zero => rw [coordinateRay_zero]; exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail ⟨hC n, hC (n+1), coordinateRay_step x i d hd n⟩

lemma coordinateRay_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) : x∈exterior C := by
  have hd0 : d≠0 := by intro h; simp [h] at hd
  refine ⟨by simpa only [coordinateRay_zero] using hC 0, ?_⟩
  have hi := Set.infinite_range_of_injective (coordinateRay_injective x i d hd0)
  exact hi.mono (by
    rintro y ⟨n,rfl⟩
    exact coordinateRay_reachable C x i d hd hC n)

lemma upper_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, c i<x i) : x∈exterior C := by
  apply coordinateRay_exterior C x i 1 (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, one_mul] at h
  omega

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_StarOffsets
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma lower_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, x i < c i) : x∈exterior C := by
  apply coordinateRay_exterior C x i (-1) (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, neg_one_mul] at h
  omega

theorem fill_subset_coordinateBox (C : Finset Vertex) : fill C⊆coordinateBox C := by
  intro x hx i
  change x∉exterior C at hx
  constructor
  · by_contra hn
    push Not at hn
    exact hx (lower_ray_exterior C x i hn)
  · by_contra hn
    push Not at hn
    exact hx (upper_ray_exterior C x i hn)

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AnimalFamily
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma animalFamily_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (m : ℕ) :
    (animalFamily G m).card ≤ Fintype.card V * (2^Δ)^m := by
  calc
    _ ≤ ∑ r : V, (rootedAnimals G r m).card := Finset.card_biUnion_le
    _ ≤ ∑ _r : V, (2^Δ)^m := Finset.sum_le_sum fun r _ ↦ rootedAnimals_card_le G Δ hΔ r m
    _ = _ := by simp

lemma mem_animalFamily_card (G : SimpleGraph V) (m : ℕ) {F : Finset V}
    (hF : F∈animalFamily G m) : F.card=m := by
  obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hF
  exact (Finset.mem_filter.mp hr).2.2.1

lemma largeBadComponent_contains_animal (G : SimpleGraph V) (B : Finset V)
    (m : ℕ) (hm : 1 ≤ m) (hB : LargeBadComponent G B m) :
    ∃ F∈animalFamily G m, F⊆B := by
  obtain ⟨C,hC,hmC⟩ := hB
  have hc := badComponents_candidate G B hC
  simp only [candidateSets,Finset.mem_filter,Finset.mem_univ,true_and] at hc
  obtain ⟨r,hr⟩ := hc.1
  obtain ⟨F,hFC,hF⟩ := exists_rooted_subanimal G C hr (hc.2 r hr) m hm hmC
  exact ⟨F,Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hF⟩,
    hFC.trans (badComponents_subset G B hC)⟩

theorem largeBadComponent_probability (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (m : ℕ) (hm : 1 ≤ m) :
    (∑' B, if LargeBadComponent G B m then μ B else 0) ≤
      (Fintype.card V : ℝ≥0∞) * (((2^Δ:ℕ):ℝ≥0∞)*p)^m := by
  have hpoint (B : Finset V) :
      (if LargeBadComponent G B m then μ B else 0) ≤
      ∑ F∈animalFamily G m, if F⊆B then μ B else 0 := by
    by_cases h : LargeBadComponent G B m
    · obtain ⟨F,hF,hFB⟩ := largeBadComponent_contains_animal G B m hm h
      rw [ite_eq_left h]
      calc
        μ B = if F⊆B then μ B else 0 := (ite_eq_left hFB).symm
        _ ≤ _ := Finset.single_le_sum (f := fun F : Finset V ↦ if F ⊆ B then μ B else 0)
          (fun _ _ ↦ zero_le) hF
    · rw [ite_eq_right h]
      exact zero_le
  calc
    _ ≤ ∑' B, ∑ F∈animalFamily G m, if F⊆B then μ B else 0 :=
      ENNReal.tsum_le_tsum hpoint
    _ = ∑ F∈animalFamily G m, ∑' B, if F⊆B then μ B else 0 := by
      simp only [tsum_fintype]
      exact Finset.sum_comm
    _ ≤ ∑ _F∈animalFamily G m, p^m := by
      apply Finset.sum_le_sum
      intro F hF
      simpa only [mem_animalFamily_card G m hF] using hbad F
    _ = ((animalFamily G m).card:ℝ≥0∞)*p^m := by simp
    _ ≤ ((Fintype.card V*(2^Δ)^m:ℕ):ℝ≥0∞)*p^m := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast animalFamily_card_le G Δ hΔ m
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshEvents
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.coordinateBridge_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits BathSlice
attribute [local irreducible] torusDistance freeTrajectory

lemma noiseSize_nonneg (w : CoordinatePaths 1) : 0 ≤ noiseSize w :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma cubicMean_nonneg : 0 ≤ cubicMean := integral_nonneg (fun w ↦ by have := noiseSize_nonneg w; positivity)

lemma meanCost_nonneg : 0 ≤ meanCost := by
  unfold meanCost
  have he : 0≤Real.exp 1-1 := by have := Real.add_one_le_exp 1; linarith
  exact mul_nonneg he cubicMean_nonneg

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianDensity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma packingConstant_pos : 0<packingConstant := by unfold packingConstant; positivity

end HardSphere.GaussianPacking

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentSimplify
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma hitConstant_pos : 0<hitConstant := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have hk := packingConstant_pos
  unfold hitConstant
  positivity

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeReference
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma densityLower_pos {b : ℝ} (hb : 0<b) (C : ℝ) : 0<densityLower b C := by
  unfold densityLower
  exact mul_pos (pow_pos (Real.sqrt_pos.mpr (div_pos hb Real.pi_pos)) _) (Real.exp_pos _)

end HardSphere.GaussianPacking

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_LocalReference
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma midpointLower_pos {t : ℝ} (ht : 0<t) (C : ℝ) : 0 < midpointLower t C :=
  ENNReal.ofReal_pos.mpr (densityLower_pos (by positivity) C)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusNear
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice

lemma torusNear_refl (K R : ℕ) (x : DiscreteTorus K) : torusNear K R x x := by
  exact ⟨0,fun i ↦ by simp,fun i ↦ by simp⟩

lemma torusNear_symm {K R : ℕ} {x y : DiscreteTorus K} (h : torusNear K R x y) :
    torusNear K R y x := by
  obtain ⟨d,hd,he⟩ := h
  refine ⟨-d,fun i ↦ by simpa using hd i,fun i ↦ ?_⟩
  simp only [Pi.neg_apply,Int.cast_neg,he i]
  abel

lemma torusNear_add {K R S : ℕ} {x y z : DiscreteTorus K}
    (hxy : torusNear K R x y) (hyz : torusNear K S y z) : torusNear K (R+S) x z := by
  obtain ⟨d,hd,he⟩ := hxy
  obtain ⟨e,he',hf⟩ := hyz
  refine ⟨d+e,fun i ↦ ?_,fun i ↦ ?_⟩
  · exact (abs_add_le (d i) (e i)).trans (by simpa only [Nat.cast_add] using add_le_add (hd i) (he' i))
  · simp only [Pi.add_apply,Int.cast_add,hf i,he i,add_assoc]

lemma torusOffsets_card (R : ℕ) : (torusOffsets R).card=(2*R+1)^3 := by
  have hcard : (Finset.Icc (-(R:ℤ)) R).card=2*R+1 := by rw [Int.card_Icc]; omega
  simp only [torusOffsets,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma torusNear_mem_image {K R : ℕ} (x y : DiscreteTorus K) :
    torusNear K R x y ↔ y∈(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
  constructor
  · rintro ⟨d,hd,he⟩
    refine Finset.mem_image.mpr ⟨d,?_,?_⟩
    · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd
    · ext i; exact (he i).symm
  · intro hy
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨d,?_,fun i ↦ rfl⟩
    simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd

lemma torusNear_ball_card {K : ℕ} [NeZero K] (R : ℕ) (x : DiscreteTorus K) :
    (Finset.univ.filter (torusNear K R x)).card≤(2*R+1)^3 := by
  have he : Finset.univ.filter (torusNear K R x)=(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,torusNear_mem_image]
  rw [he]
  exact Finset.card_image_le.trans (torusOffsets_card R).le

lemma torusRange_degree {K : ℕ} [NeZero K] (a : ℕ) (x : DiscreteTorus K) :
    (torusRangeGraph K a).degree x≤(2*a+1)^3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply (Finset.card_le_card (t := Finset.univ.filter (torusNear K a x)) ?_).trans (torusNear_ball_card a x)
  intro y hy
  have hxy : (torusRangeGraph K a).Adj x y := by simpa using hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy.2⟩

open MeasureTheory

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Geometry
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma power_div_identity {D : ℝ} (hD : 0 < D) (p : ℝ) :
    D^p/D = D^(p-1) := by
  rw [Real.rpow_sub hD,Real.rpow_one]

lemma source_geometry_eventually {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧ A/D ≤ 1 ∧ (A/D)^2 ≤ t ∧
      (A/D)*D^(1/12:ℝ) ≤ 1 ∧ 2*A^2 ≤ D ∧ 8*A^2 ≤ D ∧
      26*(A/D) ≤ t ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D) ≤ t ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      A/D+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  have h1 : Tendsto (fun D : ℝ ↦ A/D) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul A
  have h2 : Tendsto (fun D : ℝ ↦ A*D^(-(11/12):ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/12)).const_mul A
  have h3 : Tendsto (fun D : ℝ ↦ 13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ))) atTop (𝓝 0) := by
    simpa using (h1.const_mul 13).add (h2.const_mul (Real.sqrt (2*t)))
  have h4 : Tendsto (fun D : ℝ ↦ D^(-(2/3):ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h5 : Tendsto (fun D : ℝ ↦ D^(1/12:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    (h1.pow 2).eventually (gt_mem_nhds (by simpa using ht)),
    h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop (8*A^2),
    (h1.const_mul 26).eventually (gt_mem_nhds (by simpa using ht)),
    h3.eventually (gt_mem_nhds ht),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < b*t/(96*13))),
    h5.eventually (eventually_ge_atTop (6:ℝ)),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 3*b/(4*A)))] with D hD hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hp : (A/D)*D^(1/12:ℝ)=A*D^(-(11/12):ℝ) := by
    calc
      _ = A*(D^(1/12:ℝ)/D) := by ring
      _ = _ := by rw [power_div_identity hDp]; norm_num
  have hq : D⁻¹ = D^(-(2/3):ℝ)*D^(-(1/3):ℝ) := by
    rw [←Real.rpow_add hDp]
    norm_num [Real.rpow_neg_one]
  refine ⟨hD,hd1.le,hd2.le,by rw [hp]; exact hd3.le,by nlinarith,hd4,hd5.le,?_,?_,by linarith,?_⟩
  · have he : (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D)=
        13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ)) := by rw [←hp]; ring
    rw [he]
    exact hd6.le
  · have hh := (lt_div_iff₀ (by norm_num : (0:ℝ) < 96*13)).mp hd7
    rw [hq]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ht).mpr
    have hmul := mul_le_mul_of_nonneg_right hh.le (by positivity : 0 ≤ D^(-(1/3):ℝ))
    nlinarith
  · have hh := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*A)).mp hd9
    have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < D^(-(1/3):ℝ))
    rw [div_eq_mul_inv,hq]
    nlinarith

lemma source_trial_geometry {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop, ∀α : ℝ,0 < α → α ≤ A →
      let r := α/D
      let n := ⌈t/r^2⌉₊
      1 ≤ D ∧ 0 < n ∧ r ≤ 1 ∧ r*D^(1/12:ℝ) ≤ 1 ∧
      t/(n:ℝ) ≤ r^2 ∧ (n:ℝ)*r^2 ≤ 2*t ∧
      0 ≤ D⁻¹/t ∧ D⁻¹/t ≤ 1 ∧
      2*(t/(n:ℝ)) ≤ D⁻¹ ∧ 8*t ≤ (n:ℝ)*D⁻¹ ∧
      2*13/(n:ℝ) ≤ r ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  filter_upwards [source_geometry_eventually hA hb ht,eventually_ge_atTop t⁻¹] with D h hd
  rcases h with ⟨hD,hA1,hAsq,hAR,hD2,hD8,h26,hQ,hwin,hrelax,hiso⟩
  intro α hα hαA
  dsimp only
  let r := α/D
  let n := ⌈t/r^2⌉₊
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < r := by dsimp [r]; positivity
  have hrA : r ≤ A/D := div_le_div_of_nonneg_right hαA hDp.le
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity : 0 < t/r^2)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnr : t ≤ (n:ℝ)*r^2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp (Nat.le_ceil (t/r^2))
    exact hh
  have hτ : t/(n:ℝ) ≤ r^2 := (div_le_iff₀ hnp).mpr (by nlinarith [hnr])
  have hrs : r^2 ≤ t := (pow_le_pow_left₀ hr.le hrA 2).trans hAsq
  have hup : (n:ℝ)*r^2 ≤ 2*t := by
    have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ t/r^2)).le (sq_nonneg r)
    have he : (t/r^2+1)*r^2=t+r^2 := by field_simp
    rw [he] at hh
    nlinarith
  have hsq : r^2 ≤ D⁻¹/8 := by
    calc
      _ ≤ (A/D)^2 := pow_le_pow_left₀ hr.le hrA 2
      _ ≤ (1/8)/D := by
        apply (le_div_iff₀ hDp).mpr
        have he : (A/D)^2*D=A^2/D := by field_simp
        rw [he]
        exact (div_le_iff₀ hDp).mpr (by linarith)
      _ = _ := by ring
  have htime : D⁻¹/t ≤ 1 := by
    apply (div_le_iff₀ ht).mpr
    simp only [one_mul]
    rw [←one_div]
    apply (div_le_iff₀ hDp).mpr
    have hh := mul_le_mul_of_nonneg_left hd ht.le
    simpa [mul_inv_cancel₀ ht.ne'] using hh
  have hsmall : r*D^(1/12:ℝ) ≤ 1 := (mul_le_mul_of_nonneg_right hrA (by positivity)).trans hAR
  have hdr : 26/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hh : 26*r ≤ t := (mul_le_mul_of_nonneg_left hrA (by norm_num)).trans h26
    nlinarith
  have hdr' : (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hq : 0 ≤ 13+Real.sqrt (2*t)*D^(1/12:ℝ) := by positivity
    have hh := (mul_le_mul_of_nonneg_left hrA hq).trans hQ
    nlinarith
  refine ⟨hD,hn,hrA.trans hA1,hsmall,hτ,hup,by positivity,htime,?_,?_,?_,hdr',hwin,hrelax,?_⟩
  · change 2*(t/(n:ℝ)) ≤ D⁻¹
    nlinarith [inv_pos.mpr hDp]
  · change 8*t ≤ (n:ℝ)*D⁻¹
    have hh := mul_le_mul_of_nonneg_left hsq hnp.le
    nlinarith
  · change 2*13/(n:ℝ) ≤ r
    convert hdr using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  · change r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ)
    linarith

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NumericalSupply
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma boundary_ratio_le {D : ℝ} (hD : 1 ≤ D) :
    D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)  ≤  8*Real.sqrt 2*D^(-(1/4):ℝ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hR : 1 ≤ D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hcube : (1+D^(1/12:ℝ))^3 ≤ 8*D^(1/4:ℝ) := by
    calc
      _  ≤  (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by
        have hp : (D^(1/12:ℝ))^3 = D^(1/4:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hDp.le]
          norm_num
        rw [mul_pow,hp]
        norm_num
  have hs : Real.sqrt (D⁻¹)=D^(-(1/2):ℝ) := by
    rw [Real.sqrt_inv,Real.sqrt_eq_rpow,Real.rpow_neg hDp.le]
  calc
    _ = (1+D^(1/12:ℝ))^3*(D⁻¹/Real.sqrt (D⁻¹))*Real.sqrt 2 := by
      rw [Real.sqrt_div (inv_nonneg.mpr hDp.le)]
      simp only [div_eq_mul_inv,mul_inv,inv_inv]
      ring
    _ = (1+D^(1/12:ℝ))^3*D^(-(1/2):ℝ)*Real.sqrt 2 := by rw [Real.div_sqrt,hs]
    _  ≤  (8*D^(1/4:ℝ))*D^(-(1/2):ℝ)*Real.sqrt 2 := by gcongr
    _ = _ := by
      rw [mul_assoc (8:ℝ),←Real.rpow_add hDp]
      norm_num
      ring

lemma boundary_ratio_tendsto :
    Tendsto (fun D:ℝ  ↦  D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD using boundary_ratio_le hD
  · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).const_mul (8*Real.sqrt 2)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) :
    Measurable (physicalDatum (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u) := by
  unfold physicalDatum
  apply ((continuous_eval_const 0).measurable.comp measurable_fst).prodMk
  apply ((continuous_eval_const 1).measurable.comp measurable_fst).prodMk
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    have h : MeasurableSet {z : ConfigurationPath N L × GridAllocation N K (G*M) |
        ∃v : Fin 3 → Fin K, Eligible m r R C S s₀ u v i z.1} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun v ↦
        (eligible_measurable m r R C S s₀ u v i).preimage measurable_fst
    apply measurable_to_countable'
    intro b
    cases b
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_false_iff_not,←Set.compl_ofPred] using h.compl
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using h
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  apply Measurable.ite
    (measurable_snd ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet))
    measurable_const
  exact (onePathAt_continuous i).measurable.comp measurable_fst

lemma physicalDatumLaw_probability {N K M G : ℕ} {L : Length} (g : Fin G)
    {ψ : Jet N L} {r : ℝ} (hψ : IsGroundVector N L r ψ)
    (m : ℕ) (R C S s₀ T : ℝ) (hT : 0≤T) (u : Time) :
    IsProbabilityMeasure (physicalDatumLaw (K:=K) (M:=M) g ψ m r R C S s₀ T u) := by
  have := hψ.groundPathLaw_probability hT
  unfold physicalDatumLaw
  exact Measure.isProbabilityMeasure_map (physicalDatum_measurable g m r R C S s₀ u).aemeasurable

attribute [local irreducible] TrialCollision

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTargets
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma datumBad_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) :
    Measurable (datumBad (N:=N) (M:=M) hL g m t r R C S u) := by
  apply measurable_to_countable'
  intro f
  change MeasurableSet {d | _ = f}
  have he : {d : PhysicalDatum N K M G L | datumBad hL g m t r R C S u d=f} =
    ⋂v : Fin 3 → Fin K, {d | (2*(datumAccessibleLabels hL g m t r R C S u v d).card<M) ↔ v∈f} := by
    ext d
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rw [Finset.ext_iff]
    simp only [datumBad,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he]
  apply MeasurableSet.iInter
  intro v
  have hh := (datumAccessibleLabels_measurable (M:=M) hL g m t r R C S u v)
    ((Set.to_countable {s : Finset (Fin N) | 2*s.card<M}).measurableSet)
  by_cases hv : v∈f
  · simpa only [hv,iff_true,Set.preimage_ofPred_eq] using hh
  · simpa only [hv,iff_false,Set.preimage_ofPred_eq,←Set.compl_ofPred] using hh.compl

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AddedSites
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma torus_unit_offsets_card : ((torusOffsets 1).erase 0).card=26 := by
  rw [Finset.card_erase_of_mem (by simp [torusOffsets,Fintype.mem_piFinset]),torusOffsets_card]
  norm_num

lemma addedSites_card {K : ℕ} (H : Finset (DiscreteTorus K)) : (addedSites H).card≤26*H.card := by
  calc
    _ ≤ ∑ c∈H, (((torusOffsets 1).erase 0).image (fun d ↦ c+torusProjection K d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _c∈H, 26 := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_image_le.trans torus_unit_offsets_card.le
    _ = 26*H.card := by simp [Nat.mul_comm]

lemma mem_addedSites {K : ℕ} {H : Finset (DiscreteTorus K)} {c x : DiscreteTorus K}
    (hc : c∈H) (hne : c≠x) (hcx : torusNear K 1 c x) : x∈addedSites H := by
  obtain ⟨d,hd,he⟩ := hcx
  apply Finset.mem_biUnion.mpr
  refine ⟨c,hc,Finset.mem_image.mpr ⟨d,Finset.mem_erase.mpr ⟨?_,?_⟩,?_⟩⟩
  · intro heq
    apply hne
    ext i
    have h := he i
    simp only [heq,Pi.zero_apply,Int.cast_zero,add_zero] at h
    exact h.symm
  · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd
  · ext i; exact (he i).symm

end HardSphere.Lattice

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace HardSphere.Lattice
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma mem_encounterSet (e : V → V → Prop) (P Q : Finset V) (x y : V) :
    (x,y)∈encounterSet e P Q ↔ x∈P ∧ y∈Q ∧ e x y := by
  simp only [encounterSet,Finset.mem_filter,Finset.mem_product]
  tauto

lemma encounterSet_card_le (e : V → V → Prop) (D : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D) (P Q : Finset V) :
    (encounterSet e P Q).card≤P.card*D := by
  have hsub : encounterSet e P Q ⊆
      P.biUnion (fun x ↦ (Finset.univ.filter (e x)).image (fun y ↦ (x,y))) := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,_,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨y,by simp [he],rfl⟩⟩
  calc
    _ ≤ (P.biUnion (fun x ↦ (Finset.univ.filter (e x)).image (fun y ↦ (x,y)))).card := Finset.card_le_card hsub
    _ ≤ ∑ x∈P, ((Finset.univ.filter (e x)).image (fun y ↦ (x,y))).card := Finset.card_biUnion_le
    _ ≤ ∑ _x∈P, D := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.card_image_le.trans (hdeg x)
    _ = P.card*D := by simp

lemma encounterSet_card_le_right (e : V → V → Prop) (hsym : ∀ x y, e x y → e y x) (D : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D) (P Q : Finset V) :
    (encounterSet e P Q).card≤Q.card*D := by
  have hsub : encounterSet e P Q ⊆ (encounterSet e Q P).image Prod.swap := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    exact Finset.mem_image.mpr ⟨(y,x),(mem_encounterSet e Q P y x).mpr ⟨hy,hx,hsym x y he⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (encounterSet_card_le e D hdeg Q P))

theorem encounter_charge_bound {H : Type v} [DecidableEq H]
    (e : V → V → Prop) (hsym : ∀ x y, e x y → e y x) (D b : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D)
    (Γ Γ' P Q : Finset V) (Hs : Finset H) (added : H → Finset V) (size : H → ℕ)
    (hsize : ∀ h∈Hs, (added h).card≤b*size h)
    (hcharge : ∀ x∈P, ∀ y∈Q, e x y →
      (x∈Γ ∧ y∈Γ') ∨ ∃ h∈Hs, x∈added h ∨ y∈added h) :
    (encounterSet e P Q).card ≤ (encounterSet e Γ Γ').card+(2*b*D)*∑ h∈Hs, size h := by
  let A := Hs.biUnion (fun h ↦ encounterSet e (added h) Q ∪ encounterSet e P (added h))
  have hsubset : encounterSet e P Q ⊆ encounterSet e Γ Γ' ∪ A := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    rcases hcharge x hx y hy he with hnom|⟨h,hh,hadd⟩
    · exact Finset.mem_union_left A ((mem_encounterSet e Γ Γ' x y).mpr ⟨hnom.1,hnom.2,he⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨h,hh,?_⟩
      rcases hadd with hadd|hadd
      · exact Finset.mem_union_left _ ((mem_encounterSet e (added h) Q x y).mpr ⟨hadd,hy,he⟩)
      · exact Finset.mem_union_right _ ((mem_encounterSet e P (added h) x y).mpr ⟨hx,hadd,he⟩)
  have hA : A.card ≤ (2*b*D)*∑ h∈Hs, size h := by
    calc
      _ ≤ ∑ h∈Hs, (encounterSet e (added h) Q ∪ encounterSet e P (added h)).card := Finset.card_biUnion_le
      _ ≤ ∑ h∈Hs, (2*b*D)*size h := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ ≤ (encounterSet e (added h) Q).card+(encounterSet e P (added h)).card := Finset.card_union_le _ _
          _ ≤ (added h).card*D+(added h).card*D :=
            Nat.add_le_add (encounterSet_card_le e D hdeg _ _) (encounterSet_card_le_right e hsym D hdeg _ _)
          _ ≤ (b*size h)*D+(b*size h)*D := Nat.add_le_add
            (Nat.mul_le_mul_right D (hsize h hh)) (Nat.mul_le_mul_right D (hsize h hh))
          _ = (2*b*D)*size h := by ring
      _ = (2*b*D)*∑ h∈Hs, size h := by rw [Finset.mul_sum]
  exact (Finset.card_le_card hsubset).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hA _))

end HardSphere.Lattice

namespace HardSphere.Lattice

lemma near_badComponent_eq {K R : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    {c d : DiscreteTorus K} (hc : c∈B) (hd : d∈B) (hcd : torusNear K R c d) :
    badComponent (torusRangeGraph K R) B c=badComponent (torusRangeGraph K R) B d := by
  by_cases he : c=d
  · rw [he]
  · apply badComponent_eq_of_reachable
    exact (show (badGraph (torusRangeGraph K R) B).Adj c d from ⟨hc,hd,he,hcd⟩).reachable

lemma shell_encounter_charge {K R : ℕ} [NeZero K]
    (B Γ Γ' : Finset (DiscreteTorus K)) {x y : DiscreteTorus K}
    (hxgood : x∉B) (hxattach : shellAttachment R B Γ x)
    (hy : y∈Γ' ∨ shellAttachment R B Γ' y) (hxy : torusNear K R x y) :
    ∃ H∈badComponents (torusRangeGraph K (R+2)) B,
      torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ' ∧ x∈addedSites H := by
  obtain ⟨c,hc,hcx,z,hz,hzc⟩ := hxattach
  let H := badComponent (torusRangeGraph K (R+2)) B c
  have hcH : c∈H := mem_own_badComponent _ _ hc
  refine ⟨H,Finset.mem_image.mpr ⟨c,hc,rfl⟩,?_,?_,?_⟩
  · exact ⟨z,hzc,z,hz,torusNear_refl _ _ _⟩
  · rcases hy with hy|hy
    · exact ⟨c,hcH,y,hy,torusNear_mono (by omega) (torusNear_add hcx hxy)⟩
    · obtain ⟨d,hd,hdy,w,hw,hwd⟩ := hy
      have hcd : torusNear K (R+2) c d := by
        convert torusNear_add (torusNear_add hcx hxy) (torusNear_symm hdy) using 1; omega
      have he := near_badComponent_eq B hc hd hcd
      have hwH : w∈H := by dsimp [H]; rw [he]; exact hwd
      exact ⟨w,hwH,w,hw,torusNear_refl _ _ _⟩
  · exact mem_addedSites hcH (fun he ↦ hxgood (he ▸ hc)) hcx

theorem torus_detour_charge {K : ℕ} [NeZero K] (R : ℕ)
    (B Γ Γ' P Q : Finset (DiscreteTorus K))
    (hP : ∀ x∈P, x∉B ∧ (x∈Γ ∨ shellAttachment R B Γ x))
    (hQ : ∀ y∈Q, y∉B ∧ (y∈Γ' ∨ shellAttachment R B Γ' y)) :
    (encounterSet (torusNear K R) P Q).card ≤
      (encounterSet (torusNear K R) Γ Γ').card+
      (52*(2*R+1)^3)*∑ H∈(badComponents (torusRangeGraph K (R+2)) B).filter
        (fun H ↦ torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ'), H.card := by
  apply encounter_charge_bound (torusNear K R) (fun _ _ h ↦ torusNear_symm h)
    ((2*R+1)^3) 26 (torusNear_ball_card R) Γ Γ' P Q
    ((badComponents (torusRangeGraph K (R+2)) B).filter
      (fun H ↦ torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ')) addedSites Finset.card
  · intro H _
    exact addedSites_card H
  · intro x hx y hy hxy
    have hx' := hP x hx
    have hy' := hQ y hy
    rcases hx'.2 with hxnom|hxattach
    · rcases hy'.2 with hynom|hyattach
      · exact Or.inl ⟨hxnom,hynom⟩
      · obtain ⟨H,hH,hHΓ',hHΓ,hyH⟩ := shell_encounter_charge B Γ' Γ hy'.1 hyattach
          (Or.inl hxnom) (torusNear_symm hxy)
        exact Or.inr ⟨H,Finset.mem_filter.mpr ⟨hH,hHΓ,hHΓ'⟩,Or.inr hyH⟩
    · obtain ⟨H,hH,hHΓ,hHΓ',hxH⟩ := shell_encounter_charge B Γ Γ' hx'.1 hxattach hy'.2 hxy
      exact Or.inr ⟨H,Finset.mem_filter.mpr ⟨hH,hHΓ,hHΓ'⟩,Or.inl hxH⟩

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointsExterior
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
lemma bad_reachable_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) {x y : V} (hx : x∈S) (hy : y∈S)
    (h : (badGraph G S).Reachable x y) :
    (G.induce (↑S)).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  obtain ⟨p⟩ := h
  revert hx
  induction p with
  | nil => intro hx; exact .refl _
  | @cons x z y he p ih =>
    intro hx
    exact (show (G.induce (↑S)).Adj ⟨x,hx⟩ ⟨z,he.2.1⟩ from he.2.2).reachable.trans (ih hy he.2.1)

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupported
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma routeDensityBound_ne_top {t : ℝ} (ht : 0<t) : routeDensityBound t≠⊤ := by
  have ha : (ENNReal.ofReal (9/10:ℝ))≠0 := by positivity
  have hb : (ENNReal.ofReal (49/50:ℝ))≠0 := by positivity
  have hc := (midpointLower_pos ht 13).ne'
  simp only [routeDensityBound,ne_eq,max_eq_top]
  exact not_or.mpr ⟨by norm_num,ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb) (ENNReal.inv_ne_top.mpr hc))⟩

lemma one_le_routeDensityBound (t : ℝ) : 1 ≤ routeDensityBound t :=
  le_trans (by norm_num) (le_max_left _ _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusBall
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma shortest_representative {K : ℕ} {h d : ℤ}
    (hh : 2*|h|≤K) (he : (h:ZMod K)=(d:ZMod K)) : |h|≤|d| := by
  by_contra hn
  have hd : |d| < |h| := by omega
  have hab : |h-d| ≤ |h|+|d| := by simpa using abs_sub_le h 0 d
  have hsmall : |h-d|<(K:ℤ) := by omega
  have hz := small_multiple_zero (show ((h-d:ℤ):ZMod K)=0 by simp only [Int.cast_sub,he,sub_self]) hsmall
  have heq : h=d := sub_eq_zero.mp hz
  rw [heq] at hd
  exact lt_irrefl _ hd

lemma projection_near {K R : ℕ} {x y : Vertex} (h : ∀ i, |x i-y i|≤R) :
    torusNear K R (torusProjection K x) (torusProjection K y) := by
  refine ⟨y-x,fun i ↦ ?_,fun i ↦ ?_⟩
  · simpa only [Pi.sub_apply,abs_sub_comm] using h i
  · simp only [torusProjection,Pi.sub_apply,Int.cast_sub]
    abel

lemma nominal_index_bound {K n D : ℕ} (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    {i j : Fin (n+1)} (hnear : torusNear K D (torusProjection K (U i)) (torusProjection K (U' j))) :
    |(i.val:ℤ)-j.val|≤D := by
  obtain ⟨d,hd,he⟩ := hnear
  have h0 := he 0
  simp only [torusProjection,hfirst,hfirst',Int.cast_add,Int.cast_natCast] at h0
  have heq : (((j.val:ℤ)-i.val:ℤ):ZMod K)=(d 0:ZMod K) := by push_cast; linear_combination h0
  have hsmall : 2*|(j.val:ℤ)-i.val|≤(K:ℤ) := by
    have hi := i.isLt
    have hj := j.isLt
    have hb : |(j.val:ℤ)-i.val|≤n := abs_le.mpr ⟨by omega,by omega⟩
    omega
  rw [abs_sub_comm]
  exact (shortest_representative hsmall heq).trans (hd 0)

lemma nominal_equal_index {K n D : ℕ} (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    {i j : Fin (n+1)} (hnear : torusNear K D (torusProjection K (U i)) (torusProjection K (U' j))) :
    torusNear K (4*D) (torusProjection K (U i)) (torusProjection K (U' i)) := by
  have hij := nominal_index_bound hnK U U' b hfirst hfirst' hnear
  have hnear' : torusNear K (3*D) (torusProjection K (U' j)) (torusProjection K (U' i)) := by
    apply projection_near
    intro k
    have h := hspeed j i k
    rw [abs_sub_comm (j.val:ℤ) (i.val:ℤ)] at h
    push_cast
    omega
  convert torusNear_add hnear hnear' using 1; omega

lemma mem_torusBall {K : ℕ} [NeZero K] (R : ℕ) (x y : DiscreteTorus K) :
    y∈torusBall R x ↔ torusNear K R x y := by simp [torusBall]

theorem nominal_encounter_bound {K n : ℕ} [NeZero K] (R : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x) :
    (encounterSet (torusNear K R) Γ Γ').card ≤
      (343*(2*R+1)^3)*
      (Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card := by
  let I := Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))
  have hsub : encounterSet (torusNear K R) Γ Γ' ⊆
      I.biUnion (fun i ↦ encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ') := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet _ _ _ _ _).mp hxy
    obtain ⟨i,hi⟩ := hcover x hx
    obtain ⟨j,hj⟩ := hcover' y hy
    have hnear : torusNear K (R+6) (torusProjection K (U i)) (torusProjection K (U' j)) := by
      convert torusNear_add (torusNear_add hi he) (torusNear_symm hj) using 1; omega
    have hiI : i∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      nominal_equal_index hnK U U' b hfirst hfirst' hspeed hnear⟩
    exact Finset.mem_biUnion.mpr ⟨i,hiI,(mem_encounterSet _ _ _ _ _).mpr
      ⟨(mem_torusBall _ _ _).mpr hi,hy,he⟩⟩
  calc
    _ ≤ (I.biUnion (fun i ↦ encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ')).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i∈I, (encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ').card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i∈I, 343*(2*R+1)^3 := by
      apply Finset.sum_le_sum
      intro i _
      exact (encounterSet_card_le _ _ (torusNear_ball_card R) _ _).trans
        (Nat.mul_le_mul_right _ (by simpa [torusBall] using torusNear_ball_card 3 (torusProjection K (U i))))
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul]; rw [Nat.mul_comm]

lemma candidate_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {F : Finset V} (hF : F∈candidateSets G) : F.Nonempty :=
  (Finset.mem_filter.mp hF).2.1

lemma candidate_reach {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {F : Finset V} (hF : F∈candidateSets G)
    {x y : V} (hx : x∈F) (hy : y∈F) : (badGraph G F).Reachable x y :=
  (Finset.mem_filter.mp hF).2.2 x hx y hy

lemma candidate_diameter {K : ℕ} [NeZero K] (a : ℕ) {F : Finset (DiscreteTorus K)}
    (hF : F∈candidateSets (torusRangeGraph K a)) {x y : DiscreteTorus K}
    (hx : x∈F) (hy : y∈F) : torusNear K (a*(F.card-1)) x y := by
  obtain ⟨w⟩ := bad_reachable_induce _ F hx hy (candidate_reach _ hF hx hy)
  let p := w.toPath
  have hwalk : ∀ {u v : (↑F : Set (DiscreteTorus K))}
      (w : ((torusRangeGraph K a).induce (↑F)).Walk u v), torusNear K (a*w.length) u.val v.val := by
    intro u v w
    induction w with
    | nil => exact torusNear_refl _ _ _
    | @cons u v w he p ih =>
      simpa only [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        torusNear_add (show torusNear K a u.val v.val from he.2) ih
  have hlen : p.val.length<F.card := by simpa using p.isPath.length_lt
  exact torusNear_mono (Nat.mul_le_mul_left _ (by omega)) (hwalk p.val)

lemma candidate_contact_root {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    {F : Finset (DiscreteTorus K)} (hF : F∈candidateSets (torusRangeGraph K a))
    (hcontact : torusContact a F Γ) (hcontact' : torusContact a F Γ') :
    ∃ i, torusNear K ((12*a+24)*F.card) (torusProjection K (U i)) (torusProjection K (U' i)) ∧
      ∃ c∈torusBall (a+3) (torusProjection K (U i)), F∈rootedAnimals (torusRangeGraph K a) c F.card := by
  obtain ⟨c,hc,x,hx,hcx⟩ := hcontact
  obtain ⟨d,hd,y,hy,hdy⟩ := hcontact'
  obtain ⟨i,hi⟩ := hcover x hx
  obtain ⟨j,hj⟩ := hcover' y hy
  have hic : torusNear K (a+3) (torusProjection K (U i)) c := by
    convert torusNear_add hi (torusNear_symm hcx) using 1; omega
  have hdj : torusNear K (a+3) d (torusProjection K (U' j)) := torusNear_add hdy (torusNear_symm hj)
  have hm : 1≤F.card := Finset.card_pos.mpr (candidate_nonempty _ hF)
  have hnear : torusNear K ((3*a+6)*F.card) (torusProjection K (U i)) (torusProjection K (U' j)) := by
    apply torusNear_mono (show (a+3)+a*(F.card-1)+(a+3)≤(3*a+6)*F.card from ?_)
      (torusNear_add (torusNear_add hic (candidate_diameter a hF hc hd)) hdj)
    have h1 := Nat.mul_le_mul_left a (show F.card-1≤F.card by omega)
    have h2 := Nat.mul_le_mul_left (2*a+6) hm
    nlinarith
  refine ⟨i,?_,c,(mem_torusBall _ _ _).mpr hic,?_⟩
  · convert nominal_equal_index hnK U U' b hfirst hfirst' hspeed hnear using 1; ring
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,rfl,fun y hy ↦ candidate_reach _ hF hc hy⟩

theorem contact_candidates_card {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    (m : ℕ) (hm : 1 ≤ m) :
    ((candidateSets (torusRangeGraph K a)).filter (fun F ↦ F.card=m ∧
      torusContact a F Γ ∧ torusContact a F Γ')).card ≤
      ((2*(a+3)+1)^3*2^((2*a+1)^3))^m *
      (Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*m)
        (torusProjection K (U i)) (torusProjection K (U' i)))).card := by
  let I := Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*m)
        (torusProjection K (U i)) (torusProjection K (U' i)))
  let G := torusRangeGraph K a
  have hsub : (candidateSets G).filter (fun F ↦ F.card=m ∧ torusContact a F Γ ∧ torusContact a F Γ') ⊆
      I.biUnion (fun i ↦ (torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m)) := by
    intro F hF
    obtain ⟨hFc,hmF,hFΓ,hFΓ'⟩ := Finset.mem_filter.mp hF
    obtain ⟨i,hi,c,hc,hroot⟩ := candidate_contact_root a hnK U U' b hfirst hfirst' hspeed Γ Γ' hcover hcover' hFc hFΓ hFΓ'
    rw [hmF] at hi hroot
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
      Finset.mem_biUnion.mpr ⟨c,hc,hroot⟩⟩
  have hp : (2*(a+3)+1)^3≤((2*(a+3)+1)^3)^m := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (I.biUnion (fun i ↦ (torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i∈I, ((torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i∈I, ((2*(a+3)+1)^3*2^((2*a+1)^3))^m := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ c∈torusBall (a+3) (torusProjection K (U i)), (rootedAnimals G c m).card := Finset.card_biUnion_le
        _ ≤ ∑ _c∈torusBall (a+3) (torusProjection K (U i)), (2^((2*a+1)^3))^m :=
          Finset.sum_le_sum fun _ _ ↦ rootedAnimals_card_le G _ (torusRange_degree a) _ _
        _ = (torusBall (a+3) (torusProjection K (U i))).card*(2^((2*a+1)^3))^m := by simp
        _ ≤ (2*(a+3)+1)^3*(2^((2*a+1)^3))^m :=
          Nat.mul_le_mul_right _ (torusNear_ball_card _ _)
        _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_right _ hp
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul]; rw [Nat.mul_comm]

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EnnrealTsumFinset
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
open scoped ENNReal

lemma ennreal_tsum_finset {ι α : Type*} (S : Finset ι) (f : α → ι → ℝ≥0∞) :
    (∑' n, ∑ i∈S, f n i) = ∑ i∈S, ∑' n, f n i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi, ENNReal.tsum_add, ih]

lemma cardinal_weight_sum {V : Type*} [DecidableEq V] (S : Finset (Finset V))
    (hS : ∀ F∈S, F.Nonempty) (t : ℝ≥0∞) :
    (∑ F∈S, t^F.card) = ∑' m : ℕ, ((S.filter (fun F ↦ F.card=m+1)).card:ℝ≥0∞)*t^(m+1) := by
  have hsingle (F : Finset V) (hF : F∈S) :
      (∑' m : ℕ, if F.card=m+1 then t^(m+1) else 0)=t^F.card := by
    have hpos := Finset.card_pos.mpr (hS F hF)
    rw [tsum_eq_single (F.card-1) (by intro m hm; exact ite_eq_right (by omega))]
    have he : F.card-1+1=F.card := by omega
    simp [he]
  have he (m : ℕ) :
      ((S.filter (fun F ↦ F.card=m+1)).card:ℝ≥0∞)*t^(m+1) =
      ∑ F∈S, if F.card=m+1 then t^(m+1) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [he]
  rw [ennreal_tsum_finset]
  exact Finset.sum_congr rfl fun F hF ↦ (hsingle F hF).symm

theorem contact_candidate_potential {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    (t : ℝ≥0∞) :
    (∑ F∈candidateSets (torusRangeGraph K a),
      if torusContact a F Γ ∧ torusContact a F Γ' then t^F.card else 0) ≤
      ∑ i : Fin (n+1), ∑' m : ℕ,
        if torusNear K ((12*a+24)*(m+1)) (torusProjection K (U i)) (torusProjection K (U' i))
        then ((((2*(a+3)+1)^3*2^((2*a+1)^3):ℕ):ℝ≥0∞)*t)^(m+1) else 0 := by
  let S := (candidateSets (torusRangeGraph K a)).filter
    (fun F ↦ torusContact a F Γ ∧ torusContact a F Γ')
  have hS : ∀ F∈S, F.Nonempty := fun F hF ↦ candidate_nonempty _ (Finset.mem_filter.mp hF).1
  rw [← Finset.sum_filter]
  change (∑ F∈S, t^F.card)≤_
  rw [cardinal_weight_sum S hS t]
  rw [← ennreal_tsum_finset]
  apply ENNReal.tsum_le_tsum
  intro m
  have hcard := contact_candidates_card a hnK U U' b hfirst hfirst' hspeed Γ Γ' hcover hcover' (m+1) (by omega)
  have he : S.filter (fun F ↦ F.card=m+1) =
      (candidateSets (torusRangeGraph K a)).filter
      (fun F ↦ F.card=m+1 ∧ torusContact a F Γ ∧ torusContact a F Γ') := by
    ext F; simp only [S,Finset.mem_filter]; tauto
  rw [he]
  calc
    _ ≤ (((((2*(a+3)+1)^3*2^((2*a+1)^3))^(m+1))*
      (Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*(m+1))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card : ℕ):ℝ≥0∞)*t^(m+1) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast hcard
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,Nat.cast_mul,Nat.cast_pow,mul_pow]
      ring

end HardSphere.Lattice

open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NominalDrift
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

lemma torusNear_least_iff {K R : ℕ} (x y : Vertex)
    (hsmall : ∀ k, 2*|x k-y k|≤K) :
    torusNear K R (torusProjection K x) (torusProjection K y) ↔ ∀ k, |x k-y k|≤R := by
  constructor
  · rintro ⟨d,hd,he⟩ k
    have hcast : (((y k-x k):ℤ):ZMod K)=(d k:ZMod K) := by
      have h := he k
      simp only [torusProjection,Int.cast_sub] at h ⊢
      linear_combination h
    rw [abs_sub_comm]
    exact (shortest_representative (by simpa only [abs_sub_comm] using hsmall k) hcast).trans (hd k)
  · exact projection_near

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CandidateConstant
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

lemma candidateConstant_growth (a : ℕ) :
    (2*(a+3)+1)^3*2^((2*a+1)^3) ≤ candidateConstant a := Nat.le_add_right _ _

lemma candidateConstant_radius (a : ℕ) : 12*a+24 ≤ candidateConstant a := Nat.le_add_left _ _

lemma encounterConstant_detour (R : ℕ) : 52*(2*R+1)^3≤encounterConstant R := by
  exact Nat.mul_le_mul_right _ (by norm_num)

end HardSphere.Lattice

open scoped ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
omit [Fintype V] in

lemma prod_one_add_ofReal_le_exp_sum  {I : Type*} (Q : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ Q, 0 ≤ w i) :
    ∏ i ∈ Q, (1 + ENNReal.ofReal (w i)) ≤
      ENNReal.ofReal (Real.exp (∑ i ∈ Q, w i)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert i Q hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hwi := hw i (Finset.mem_insert_self i Q)
    have hQ : ∀ j ∈ Q, 0 ≤ w j := fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)
    apply mul_le_mul' _ (ih hQ)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hwi]
    exact ENNReal.ofReal_le_ofReal (by simpa [add_comm] using Real.add_one_le_exp (w i))

theorem badComponents_exponential_bound (G : SimpleGraph V)
    (μ : PMF (Finset V)) (p β : ℝ) (hp : 0 ≤ p)
    (hbad : JointBadLaw μ (ENNReal.ofReal p)) (P : Finset V → Prop) :
    (∑' B, μ B * ENNReal.ofReal (Real.exp
      (β * ∑ F∈badComponents G B, if P F then (F.card:ℝ) else 0))) ≤
      ENNReal.ofReal (Real.exp (∑ F∈candidateSets G,
        if P F then (p * Real.exp β)^F.card else 0)) := by
  let w : Finset V → ℝ≥0∞ := fun F ↦ if P F then
    ENNReal.ofReal (Real.exp (β * (F.card:ℝ))) else 0
  have hpoint (B : Finset V) :
      ENNReal.ofReal (Real.exp
        (β * ∑ F∈badComponents G B, if P F then (F.card:ℝ) else 0)) ≤
      ∏ F∈badComponents G B, (1+w F) := by
    rw [Finset.mul_sum, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    apply Finset.prod_le_prod'
    intro F _
    by_cases h : P F
    · simp only [ite_eq_left h,w]
      exact le_add_self
    · simp only [ite_eq_right h,w,mul_zero,Real.exp_zero,ENNReal.ofReal_one,add_zero]
      exact le_rfl
  calc
    _ ≤ ∑' B, μ B * ∏ F∈badComponents G B, (1+w F) := by
      exact ENNReal.tsum_le_tsum fun B ↦ mul_le_mul' le_rfl (hpoint B)
    _ ≤ ∏ F∈candidateSets G, (1+(ENNReal.ofReal p)^F.card*w F) :=
      environment_product_bound μ _ hbad (badComponents G)
        (badComponents_disjoint G) (fun B F hF ↦ badComponents_subset G B hF)
        (candidateSets G) (badComponents_candidate G) w
    _ = ∏ F∈candidateSets G,
        (1+ENNReal.ofReal (if P F then (p*Real.exp β)^F.card else 0)) := by
      apply Finset.prod_congr rfl
      intro F _
      dsimp only [w]
      by_cases h : P F
      · simp only [ite_eq_left h]
        rw [← ENNReal.ofReal_pow hp,← ENNReal.ofReal_mul (pow_nonneg hp _),
          mul_comm β (F.card:ℝ),Real.exp_nat_mul,mul_pow]
      · simp only [ite_eq_right h,mul_zero,ENNReal.ofReal_zero]
    _ ≤ _ := prod_one_add_ofReal_le_exp_sum _ _ (by
      intro F _
      split_ifs
      · exact pow_nonneg (mul_nonneg hp (Real.exp_pos _).le) _
      · exact le_rfl)

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointDanger
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

lemma fill_endpoint_danger {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (r x : Vertex) (hr : torusProjection K r∈B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K r)).card<K)
    (C : Finset Vertex)
    (hC : (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r)
    (hx : x∉exterior C) : endpointDanger B (torusProjection K x) := by
  let F := badComponent (torusRangeGraph K 1) B (torusProjection K r)
  have hrF : torusProjection K r∈F := mem_own_badComponent _ _ hr
  obtain ⟨D,hD,_,hspan⟩ := small_periodic_lifts (a:=1) (by simpa using hK) F
    (by simpa using hsmall) (badComponent_preconnected _ _ _) r hrF
  have hCD : C=D := Finset.coe_injective (hC.trans hD.symm)
  subst D
  have hrC : r∈C := by change r∈(↑C:Set Vertex); rw [hC]; exact ⟨hrF,.refl⟩
  have hbox := fill_subset_coordinateBox C (show x∈fill C from hx)
  have hbound (i : Fin 3) : |x i-r i|≤F.card := by
    obtain ⟨⟨l,hl,hlx⟩,⟨u,hu,hxu⟩⟩ := hbox i
    have hlow := hspan l hl r hrC i
    have hhigh := hspan u hu r hrC i
    obtain ⟨hlow₁,hlow₂⟩ := abs_le.mp hlow
    obtain ⟨hhigh₁,hhigh₂⟩ := abs_le.mp hhigh
    exact abs_le.mpr ⟨by omega,by omega⟩
  refine ⟨F,badComponents_candidate _ B (Finset.mem_image.mpr ⟨torusProjection K r,hr,rfl⟩),
    badComponent_subset _ B _,torusProjection K r,hrF,projection_near hbound⟩

lemma endpointsExterior_of_no_danger {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hsmall : ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K)
    (hv : ¬endpointDanger B (torusProjection K v)) (hw : ¬endpointDanger B (torusProjection K w)) :
    endpointsExterior B v w := by
  intro r hr C hC
  constructor
  · by_contra hn
    exact hv (fill_endpoint_danger hK B r v hr (hsmall _ hr) C hC hn)
  · by_contra hn
    exact hw (fill_endpoint_danger hK B r w hr (hsmall _ hr) C hC hn)

lemma rejection_subset {K a : ℕ} [NeZero K] (hK : 2<K) (ha : 1≤a)
    (B : Finset (DiscreteTorus K)) (v w : Vertex) (hE : ¬acceptedEnvironment a B v w) :
    LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) ∨
      endpointDanger B (torusProjection K v) ∨ endpointDanger B (torusProjection K w) := by
  by_contra h
  push Not at h
  apply hE
  exact ⟨h.1,endpointsExterior_of_no_danger hK B v w (small_star_of_no_large ha B h.1) h.2.1 h.2.2⟩

lemma endpointAnimals_card {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ) :
    (endpointAnimals x m).card≤(2*m+1)^3*(2^27)^m := by
  calc
    _ ≤ ∑ c∈torusBall m x, (rootedAnimals (torusRangeGraph K 1) c m).card := Finset.card_biUnion_le
    _ ≤ ∑ _c∈torusBall m x, (2^27)^m := by
      apply Finset.sum_le_sum
      intro c _
      exact rootedAnimals_card_le _ 27 (by simpa using torusRange_degree (K:=K) 1) c m
    _ = (torusBall m x).card*(2^27)^m := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (torusNear_ball_card _ _)

lemma mem_endpointAnimals_card {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ)
    {F : Finset (DiscreteTorus K)} (hF : F∈endpointAnimals x m) : F.card=m := by
  obtain ⟨c,_,hF⟩ := Finset.mem_biUnion.mp hF
  exact (Finset.mem_filter.mp hF).2.2.1

lemma danger_contains_endpointAnimal {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    (x : DiscreteTorus K) (h : endpointDanger B x) :
    ∃ m : ℕ, ∃ F∈endpointAnimals x (m+1), F⊆B := by
  obtain ⟨F,hF,hFB,c,hc,hxc⟩ := h
  have hpos := Finset.card_pos.mpr (candidate_nonempty _ hF)
  have hcard : F.card-1+1=F.card := by omega
  refine ⟨F.card-1,F,?_,hFB⟩
  rw [hcard]
  exact Finset.mem_biUnion.mpr ⟨c,(mem_torusBall _ _ _).mpr hxc,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,rfl,fun y hy ↦ candidate_reach _ hF hc hy⟩⟩

theorem endpointDanger_probability {K : ℕ} [NeZero K]
    (μ : PMF (Finset (DiscreteTorus K))) (p : ℝ≥0∞) (hbad : JointBadLaw μ p) (x : DiscreteTorus K) :
    (∑' B, if endpointDanger B x then μ B else 0) ≤
      ∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*(((2^27:ℕ):ℝ≥0∞)*p)^(m+1) := by
  have hpoint (B : Finset (DiscreteTorus K)) :
      (if endpointDanger B x then μ B else 0) ≤
      ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), if F⊆B then μ B else 0 := by
    by_cases h : endpointDanger B x
    · obtain ⟨m,F,hF,hFB⟩ := danger_contains_endpointAnimal B x h
      rw [ite_eq_left h]
      exact le_trans (by
        simpa only [ite_eq_left hFB] using
          (Finset.single_le_sum (f := fun F : Finset (DiscreteTorus K) ↦ if F⊆B then μ B else 0)
            (fun _ _ ↦ zero_le) hF)) (ENNReal.le_tsum m)
    · rw [ite_eq_right h]; exact zero_le
  calc
    _ ≤ ∑' B, ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), if F⊆B then μ B else 0 := ENNReal.tsum_le_tsum hpoint
    _ = ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), ∑' B, if F⊆B then μ B else 0 := by
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun m ↦ ennreal_tsum_finset _ _
    _ ≤ ∑' m : ℕ, ∑ _F∈endpointAnimals x (m+1), p^(m+1) := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply Finset.sum_le_sum
      intro F hF
      simpa only [mem_endpointAnimals_card x (m+1) hF] using hbad F
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro m
      simp only [Finset.sum_const,nsmul_eq_mul]
      calc
        _ ≤ (((2*(m+1)+1)^3*(2^27)^(m+1):ℕ):ℝ≥0∞)*p^(m+1) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast endpointAnimals_card x (m+1)
        _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

open scoped NNReal
lemma endpoint_polynomial_le (m : ℕ) : (2*(m+1)+1)^3≤27*8^m := by
  have hs : m+1≤2^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      have hp := Nat.one_le_pow m 2 (by norm_num)
      omega
  calc
    _ ≤ (3*2^m)^3 := Nat.pow_le_pow_left (by nlinarith) 3
    _ = _ := by rw [mul_pow,← pow_mul,Nat.mul_comm m 3,pow_mul]; norm_num

lemma endpoint_series_le (q : ℝ≥0∞) (hq : q≤1/16) :
    (∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*q^(m+1))≤54*q := by
  have h8 : (8:ℝ≥0∞)*q≤1/2 := by
    calc
      _ ≤ 8*(1/16:ℝ≥0∞) := mul_le_mul' le_rfl hq
      _ = _ := by
        have h : (8:ℝ≥0)*(1/16)=1/2 := by norm_num
        have hh := congrArg (fun x : ℝ≥0 ↦ (x:ℝ≥0∞)) h
        simpa only [ENNReal.coe_mul,ENNReal.coe_div (show (16:ℝ≥0)≠0 by norm_num),
          ENNReal.coe_div (show (2:ℝ≥0)≠0 by norm_num),ENNReal.coe_ofNat,ENNReal.coe_one] using hh
  calc
    _ ≤ ∑' m : ℕ, 27*q*((1/2:ℝ≥0∞)^m) := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ (27*8^m:ℝ≥0∞)*q^(m+1) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast endpoint_polynomial_le m
        _ = 27*q*((8*q)^m) := by rw [pow_succ,mul_pow]; ring
        _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' h8 m)
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]; norm_num; ring

lemma rejection_probability {K a : ℕ} [NeZero K] (hK : 2<K) (ha : 1≤a)
    (hm : 1≤K/(10*a)) (μ : PMF (Finset (DiscreteTorus K))) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (v w : Vertex) :
    (∑' B, if ¬acceptedEnvironment a B v w then μ B else 0)≤
      (K:ℝ≥0∞)^3*(((2^((2*a+1)^3):ℕ):ℝ≥0∞)*p)^(K/(10*a))+
      2*∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*(((2^27:ℕ):ℝ≥0∞)*p)^(m+1) := by
  have hpoint (B : Finset (DiscreteTorus K)) :
      (if ¬acceptedEnvironment a B v w then μ B else 0)≤
      (if LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) then μ B else 0)+
      (if endpointDanger B (torusProjection K v) then μ B else 0)+
      (if endpointDanger B (torusProjection K w) then μ B else 0) := by
    by_cases hE : ¬acceptedEnvironment a B v w
    · rw [ite_eq_left hE]
      rcases rejection_subset hK ha B v w hE with h|h|h
      · rw [ite_eq_left h]; exact le_add_of_le_left le_self_add
      · rw [ite_eq_left h]; exact le_add_of_le_left le_add_self
      · rw [ite_eq_left h]; exact le_add_self
    · rw [ite_eq_right hE]; exact zero_le
  calc
    _ ≤ _ := ENNReal.tsum_le_tsum hpoint
    _ = _ := by rw [ENNReal.tsum_add,ENNReal.tsum_add]
    _ ≤ _ := add_le_add (add_le_add
      (largeBadComponent_probability (torusRangeGraph K a) ((2*a+1)^3)
        (torusRange_degree a) μ p hbad (K/(10*a)) hm)
      (endpointDanger_probability μ p hbad (torusProjection K v)))
      (endpointDanger_probability μ p hbad (torusProjection K w))
    _ = _ := by
      simp only [DiscreteTorus,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow]
      ring

lemma large_rejection_eventually (a : ℕ) (ha : 1≤a) :
    ∀ᶠ K : ℕ in Filter.atTop, (K:ℝ)^3*(1/2:ℝ)^(K/(10*a))≤1/4 := by
  let d := 10*a
  have hd : 0<d := by dsimp [d]; omega
  have hl := tendsto_pow_const_mul_const_pow_of_lt_one 3 (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hlim : Filter.Tendsto (fun j : ℕ ↦ ((2*d:ℕ):ℝ)^3*((j:ℝ)^3*(1/2:ℝ)^j)) Filter.atTop (nhds 0) := by
    simpa using hl.const_mul (((2*d:ℕ):ℝ)^3)
  have hSmall : ∀ᶠ j : ℕ in Filter.atTop,
      ((2*d:ℕ):ℝ)^3*((j:ℝ)^3*(1/2:ℝ)^j)≤1/4 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ h ↦ h.le)
  have hdiv := Nat.tendsto_div_const_atTop (ne_of_gt hd)
  filter_upwards [hdiv.eventually hSmall,Filter.eventually_ge_atTop d] with K hsm hKd
  have hj : 1≤K/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hKd)
  have hK : K≤(2*d)*(K/d) := by
    have hb := Nat.lt_mul_div_succ K hd
    nlinarith
  calc
    _ ≤ (((2*d:ℕ):ℝ)*(K/d:ℕ))^3*(1/2:ℝ)^(K/d) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hK
    _ = ((2*d:ℕ):ℝ)^3*((K/d:ℕ)^3*(1/2:ℝ)^(K/d)) := by ring
    _ ≤ _ := hsm

lemma pmf_complement_half {α : Type*} (μ : PMF α) (E : α → Prop)
    (h : (∑' x, if ¬E x then μ x else 0)≤(1/2:ℝ≥0∞)) :
    (1/2:ℝ≥0∞)≤∑' x, if E x then μ x else 0 := by
  have he : (∑' x, if E x then μ x else 0)+(∑' x, if ¬E x then μ x else 0)=1 := by
    rw [← ENNReal.tsum_add]
    convert μ.tsum_coe using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr
    intro x
    by_cases hx : E x <;> simp [hx]
  have hn : (∑' x, if ¬E x then μ x else 0)≠∞ := ne_of_lt (h.trans_lt (by norm_num))
  calc
    (1/2:ℝ≥0∞)=1-(1/2) := by norm_num
    _ ≤ 1-(∑' x, if ¬E x then μ x else 0) := tsub_le_tsub_left h 1
    _ = _ := by rw [← he,ENNReal.add_sub_cancel_right hn]

theorem acceptedEnvironment_mass (a : ℕ) (ha : 1≤a) :
    ∃ p₀ : ℝ, 0<p₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ, 0≤p → p≤p₀ →
      JointBadLaw μ (ENNReal.ofReal p) → ∀ v w : Vertex,
      (1/2:ℝ≥0∞)≤∑' B, if acceptedEnvironment a B v w then μ B else 0 := by
  let A : ℝ := (2:ℝ)^((2*a+1)^3)
  let D : ℝ := (2:ℝ)^27
  have hA : 0<A := by dsimp [A]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  let p₀ : ℝ := min ((1/432)/D) ((1/2)/A)
  have hp₀ : 0<p₀ := lt_min (div_pos (by norm_num) hD) (div_pos (by norm_num) hA)
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (large_rejection_eventually a ha)
  refine ⟨p₀,hp₀,max M (10*a+3),?_⟩
  intro K hK inst μ p hp hpp hbad v w
  have hKM : M≤K := (le_max_left _ _).trans hK
  have hKd : 10*a+3≤K := (le_max_right _ _).trans hK
  have hK2 : 2<K := by omega
  have hm : 1≤K/(10*a) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hqD : D*p≤1/432 := by
    have h := (le_div_iff₀ hD).mp (hpp.trans (min_le_left _ _))
    nlinarith
  have hqA : A*p≤1/2 := by
    have h := (le_div_iff₀ hA).mp (hpp.trans (min_le_right _ _))
    nlinarith
  have hDeq : ((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p=ENNReal.ofReal (D*p) := by
    rw [ENNReal.ofReal_mul hD.le]
    simp only [D,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  have hAeq : ((2^((2*a+1)^3):ℕ):ℝ≥0∞)*ENNReal.ofReal p=ENNReal.ofReal (A*p) := by
    rw [ENNReal.ofReal_mul hA.le]
    simp only [A,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  have hqDen : ENNReal.ofReal (D*p)≤1/16 := by
    calc
      _ ≤ ENNReal.ofReal (1/16:ℝ) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  have hseries : (∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*
      (((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p)^(m+1))≤ENNReal.ofReal (1/8:ℝ) := by
    rw [hDeq]
    refine (endpoint_series_le _ hqDen).trans ?_
    calc
      _ = ENNReal.ofReal (54*(D*p)) := by rw [ENNReal.ofReal_mul (p:=54) (q:=D*p) (by norm_num),ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have hlarge : (K:ℝ≥0∞)^3*(((2^((2*a+1)^3):ℕ):ℝ≥0∞)*ENNReal.ofReal p)^(K/(10*a))≤
      ENNReal.ofReal (1/4:ℝ) := by
    rw [hAeq]
    calc
      _ ≤ (K:ℝ≥0∞)^3*(ENNReal.ofReal (1/2:ℝ))^(K/(10*a)) :=
        mul_le_mul' le_rfl (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hqA) _)
      _ = ENNReal.ofReal ((K:ℝ)^3*(1/2:ℝ)^(K/(10*a))) := by
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hM K hKM)
  apply pmf_complement_half μ (fun B ↦ acceptedEnvironment a B v w)
  refine (rejection_probability hK2 ha hm μ _ hbad v w).trans ?_
  refine (add_le_add hlarge (mul_le_mul' le_rfl hseries)).trans_eq ?_
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos]

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathEncounter
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

lemma accepted_charge_environment_bound {K : ℕ} [NeZero K] (R : ℕ)
    (μ : PMF (Finset (DiscreteTorus K))) (p κ C N : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (Γ Γ' : Finset (DiscreteTorus K)) (E : Finset (DiscreteTorus K) → Prop)
    (J : Finset (DiscreteTorus K) → ℝ)
    (hJ : ∀ B, E B → J B≤N+C*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
      if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0) :
    (∑' B, μ B*(if E B then ENNReal.ofReal (Real.exp (κ*J B)) else 0))≤
      ENNReal.ofReal (Real.exp (κ*N+∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (p*Real.exp (κ*C))^F.card else 0)) := by
  have henv := badComponents_exponential_bound (torusRangeGraph K (R+2)) μ p (κ*C) hp hbad
    (fun F ↦ torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ')
  let S (B : Finset (DiscreteTorus K)) : ℝ := ∑ F∈badComponents (torusRangeGraph K (R+2)) B,
    if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0
  calc
    _ ≤ ∑' B, μ B*ENNReal.ofReal (Real.exp (κ*N+κ*C*S B)) := by
      apply ENNReal.tsum_le_tsum
      intro B
      apply mul_le_mul' le_rfl
      by_cases hB : E B
      · rw [ite_eq_left hB]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        calc
          κ*J B ≤ κ*(N+C*S B) := mul_le_mul_of_nonneg_left (hJ B hB) hκ
          _ = _ := by ring
      · rw [ite_eq_right hB]; exact zero_le
    _ = ENNReal.ofReal (Real.exp (κ*N)) *
        ∑' B, μ B*ENNReal.ofReal (Real.exp (κ*C*S B)) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro B
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      ring
    _ ≤ ENNReal.ofReal (Real.exp (κ*N))*
        ENNReal.ofReal (Real.exp (∑ F∈candidateSets (torusRangeGraph K (R+2)),
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (p*Real.exp (κ*C))^F.card else 0)) := by
      apply mul_le_mul' le_rfl
      change (∑' B, μ B * ENNReal.ofReal (Real.exp ((κ*C) * S B))) ≤ _
      convert henv using 1
      · congr 1
        funext B
        congr 3
        congr 1
        dsimp only [S]
        apply Finset.sum_congr rfl
        intro F hF
        split_ifs <;> rfl
      · congr 2
        apply Finset.sum_congr rfl
        intro F hF
        split_ifs <;> rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SimplePath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice
open MeasureTheory ProbabilityTheory

lemma pmf_lintegral_discrete {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : PMF α) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ.toMeasure)=∑' x, μ x*f x := by
  rw [lintegral_countable']
  apply tsum_congr
  intro x
  rw [μ.toMeasure_apply_singleton x (measurableSet_singleton x),mul_comm]

lemma pmf_event_discrete {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (E : α → Prop) [DecidablePred E] :
    μ.toMeasure {x | E x}=∑' x, if E x then μ x else 0 := by
  rw [μ.toMeasure_apply MeasurableSet.of_discrete]
  apply tsum_congr
  intro x
  exact Set.indicator_apply _ _ _

lemma mapped_bad_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (b : Ω → Finset (DiscreteTorus K)) (hb : Measurable b)
    (p : ℝ≥0∞) (hbad : ∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤p^A.card) :
    let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
    JointBadLaw (P.map b).toPMF p := by
  dsimp only
  let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
  intro A
  rw [← pmf_event_discrete (P.map b).toPMF (fun B ↦ A⊆B),Measure.toPMF_toMeasure,
    Measure.map_apply (μ := P) hb MeasurableSet.of_discrete]
  exact hbad A

lemma finite_datum_expectation {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Countable α] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : Ω → α) (hb : Measurable b) (f : α → ℝ≥0∞) :
    let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
    (∫⁻ d, f (b d) ∂P)=∑' a, (P.map b).toPMF a*f a := by
  dsimp only
  let := (Measure.isProbabilityMeasure_map_iff (μ := P) hb.aemeasurable).mpr inferInstance
  rw [← pmf_lintegral_discrete,Measure.toPMF_toMeasure,lintegral_map Measurable.of_discrete hb]

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchEstimates
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

lemma latticeDatumBad_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) :
    Measurable (latticeDatumBad (N:=N) (M:=M) hL g m t r R C S u) :=
  (measurable_of_countable (fun A : Finset (Fin 3→Fin K) ↦ A.image indexSite)).comp
    (datumBad_measurable hL g m t r R C S u)
lemma mem_latticeDatumBad {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (d : PhysicalDatum N K M G L)
    (v : DiscreteTorus K) : v∈latticeDatumBad hL g m t r R C S u d ↔
      siteIndex v∈datumBad hL g m t r R C S u d := by
  change v∈Finset.image _ _ ↔ _
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    simpa only [siteIndex_indexSite] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨siteIndex v,hv,indexSite_siteIndex v⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhaseTransfer
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace HardSphere.Phase

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma integral_mul_le_sqrt (f g : X → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    ∫ x, f x * g x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) *
      Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

lemma integral_norm_sq_le [IsFiniteMeasure ν] {f : X → ℂ} (hf : MemLp f 2 ν) :
    (∫ x, ‖f x‖ ∂ν)^2 ≤ ν.real univ * ∫ x, ‖f x‖ ^ 2 ∂ν := by
  have h := integral_mul_le_sqrt (fun _ : X ↦ 1) (fun x ↦ ‖f x‖)
    (memLp_const 1) hf.norm (Eventually.of_forall fun _ ↦ zero_le_one)
    (Eventually.of_forall fun _ ↦ norm_nonneg _)
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at h
  have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hm : 0 ≤ ∫ x, ‖f x‖^2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have hs := (sq_le_sq₀ ha (by positivity)).2 h
  simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm] using hs

end HardSphere.Phase

namespace HardSphere.Phase

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

lemma memLp_slices {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun x ↦ f (y,x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

lemma memLp_integral_norm {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν) 2 μ := by
  have hm := hf.aestronglyMeasurable.norm.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).2
  have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  apply (hi.const_mul (ν.real univ)).mono' (hm.pow 2)
  filter_upwards [memLp_slices hf] with y hy
  change ‖(∫ x, ‖f (y,x)‖ ∂ν)^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact integral_norm_sq_le hy

end HardSphere.Phase

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_BathPhase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere

lemma cons_preserving {n : ℕ} (L : Length) :
    MeasurePreserving (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1)
      (volume.prod volume) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hh := h.comp (measurePreserving_swap (μ:= (volume : Measure (Configuration n L))) (ν:=volume))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p i
  simp [MeasurableEquiv.piFinSuccAbove]

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_FirstCoordinate
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HardSphere
lemma insertFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
    MeasurePreserving (fun p : Torus L×Configuration (N-1) L ↦ insertFirst hN p.1 p.2)
      ((volume : Measure (Torus L)).prod volume) volume := by
  cases N with
  | zero => omega
  | succ n =>
    unfold insertFirst
    have h := (cons_preserving (n:=n) L).comp
      (Measure.measurePreserving_swap (μ:=(volume : Measure (Torus L))) (ν:=volume))
    convert h using 1 <;> simp [Function.comp_def]

lemma bathFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
    MeasurePreserving (fun p : Configuration (N-1) L×Torus L ↦ insertFirst hN p.2 p.1)
      ((volume : Measure (Configuration (N-1) L)).prod volume) volume :=
  (insertFirst_preserving hN L).comp (Measure.measurePreserving_swap)

lemma ground_slice_memLp {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
    MemLp (fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)) 2
      ((volume : Measure (Configuration (N-1) L)).prod volume) :=
  (Lp.memLp ψ).comp_measurePreserving (bathFirst_preserving hN L)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_Affinity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_mul_le_sqrt (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) *
      Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

lemma memLp_sqrt {f : α → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    MemLp (fun x ↦ Real.sqrt (f x)) 2 μ := by
  refine (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).2 ?_
  apply hf.congr
  filter_upwards [hf0] with x hx
  exact (Real.sq_sqrt hx).symm

lemma affinity_nonneg (p q : α → ℝ) : 0 ≤ affinity μ p q := by
  exact integral_nonneg fun x ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma affinity_integrable {p q : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) :
    Integrable (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)) μ := by
  exact (memLp_sqrt hp hp0).integrable_mul (memLp_sqrt hq hq0)

lemma sqrt_ratio_product {p q s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hsp : p = 0 → s = 0) (hsq : q = 0 → s = 0) :
    Real.sqrt (s / Real.sqrt p * (s / Real.sqrt q)) *
      Real.sqrt (Real.sqrt p * Real.sqrt q) = s := by
  by_cases hpz : p = 0
  · simp [hpz, hsp hpz]
  by_cases hqz : q = 0
  · simp [hqz, hsq hqz]
  have hp' : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hp (Ne.symm hpz)))
  have hq' : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hqz)))
  have hprod : (s / Real.sqrt p * (s / Real.sqrt q)) *
      (Real.sqrt p * Real.sqrt q) = s ^ 2 := by
    field_simp
  rw [← Real.sqrt_mul (mul_nonneg (div_nonneg hs (Real.sqrt_nonneg p))
    (div_nonneg hs (Real.sqrt_nonneg q))), hprod, Real.sqrt_sq hs]

lemma common_density_bound {p q s : α → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) (hs0 : 0 ≤ᵐ[μ] s)
    (hsp : ∀ᵐ x ∂μ, p x = 0 → s x = 0)
    (hsq : ∀ᵐ x ∂μ, q x = 0 → s x = 0)
    (hP : MemLp (fun x ↦ s x / Real.sqrt (p x)) 2 μ)
    (hQ : MemLp (fun x ↦ s x / Real.sqrt (q x)) 2 μ) :
    (∫ x, s x ∂μ) ^ 2 ≤
      Real.sqrt (∫ x, (s x / Real.sqrt (p x)) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (s x / Real.sqrt (q x)) ^ 2 ∂μ) * affinity μ p q := by
  let a := fun x ↦ s x / Real.sqrt (p x)
  let b := fun x ↦ s x / Real.sqrt (q x)
  let c := fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)
  have ha0 : 0 ≤ᵐ[μ] a := hs0.mono fun x hx ↦ div_nonneg hx (Real.sqrt_nonneg _)
  have hb0 : 0 ≤ᵐ[μ] b := hs0.mono fun x hx ↦ div_nonneg hx (Real.sqrt_nonneg _)
  have hab : Integrable (fun x ↦ a x * b x) μ := hP.integrable_mul hQ
  have hab0 : 0 ≤ᵐ[μ] (fun x ↦ a x * b x) := by
    filter_upwards [ha0, hb0] with x hx hy using mul_nonneg hx hy
  have hc : Integrable c μ := affinity_integrable hp hq hp0 hq0
  have hc0 : 0 ≤ᵐ[μ] c := Eventually.of_forall fun x ↦ by dsimp [c]; positivity
  have hs : (fun x ↦ Real.sqrt (a x * b x) * Real.sqrt (c x)) =ᵐ[μ] s := by
    filter_upwards [hp0, hq0, hs0, hsp, hsq] with x hp' hq' hs' hsp' hsq'
    exact sqrt_ratio_product hp' hq' hs' hsp' hsq'
  have h₁ := integral_mul_le_sqrt (fun x ↦ Real.sqrt (a x * b x))
    (fun x ↦ Real.sqrt (c x)) (memLp_sqrt hab hab0) (memLp_sqrt hc hc0)
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _) (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _)
  have habsq : (∫ x, Real.sqrt (a x * b x) ^ 2 ∂μ) = ∫ x, a x * b x ∂μ := by
    apply integral_congr_ae
    exact hab0.mono fun _ h ↦ Real.sq_sqrt h
  have hcsq : (∫ x, Real.sqrt (c x) ^ 2 ∂μ) = affinity μ p q := by
    apply integral_congr_ae
    exact hc0.mono fun _ h ↦ Real.sq_sqrt h
  rw [integral_congr_ae hs, habsq, hcsq] at h₁
  have h₂ : (∫ x, s x ∂μ) ^ 2 ≤ (∫ x, a x * b x ∂μ) * affinity μ p q := by
    have h := (sq_le_sq₀ (integral_nonneg_of_ae hs0) (by positivity)).2 h₁
    simpa only [mul_pow, Real.sq_sqrt (integral_nonneg_of_ae hab0),
      Real.sq_sqrt (affinity_nonneg p q)] using h
  exact h₂.trans (mul_le_mul_of_nonneg_right
    (integral_mul_le_sqrt a b hP hQ ha0 hb0) (affinity_nonneg p q))

lemma ratio_sqrt_sq {s p : ℝ} (hp : 0 ≤ p) :
    (s / Real.sqrt p) ^ 2 = s ^ 2 / p := by
  rw [div_pow, Real.sq_sqrt hp]

lemma memLp_ratio_sqrt {s p : α → ℝ} (hs : AEStronglyMeasurable s μ)
    (hp : AEStronglyMeasurable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (h : Integrable (fun x ↦ s x ^ 2 / p x) μ) :
    MemLp (fun x ↦ s x / Real.sqrt (p x)) 2 μ := by
  refine (memLp_two_iff_integrable_sq
    ((hs.aemeasurable.div (Real.continuous_sqrt.measurable.comp_aemeasurable hp.aemeasurable)).aestronglyMeasurable)).2 ?_
  apply h.congr
  exact hp0.mono fun x hx ↦ (ratio_sqrt_sq hx).symm

theorem common_density_affinity {p q s : α → ℝ} {C_P C_Q : ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ) (hs : Integrable s μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) (hs0 : 0 ≤ᵐ[μ] s)
    (hsp : ∀ᵐ x ∂μ, p x = 0 → s x = 0)
    (hsq : ∀ᵐ x ∂μ, q x = 0 → s x = 0)
    (hPi : Integrable (fun x ↦ s x ^ 2 / p x) μ)
    (hQi : Integrable (fun x ↦ s x ^ 2 / q x) μ)
    (hP : (∫ x, s x ^ 2 / p x ∂μ) ≤ C_P)
    (hQ : (∫ x, s x ^ 2 / q x ∂μ) ≤ C_Q)
    (hm : 0 < ∫ x, s x ∂μ) :
    (∫ x, s x ∂μ) ^ 2 / Real.sqrt (C_P * C_Q) ≤ affinity μ p q := by
  have hP' := memLp_ratio_sqrt hs.1 hp.1 hp0 hPi
  have hQ' := memLp_ratio_sqrt hs.1 hq.1 hq0 hQi
  have hPeq : (∫ x, (s x / Real.sqrt (p x)) ^ 2 ∂μ) =
      ∫ x, s x ^ 2 / p x ∂μ :=
    integral_congr_ae (hp0.mono fun x hx ↦ ratio_sqrt_sq hx)
  have hQeq : (∫ x, (s x / Real.sqrt (q x)) ^ 2 ∂μ) =
      ∫ x, s x ^ 2 / q x ∂μ :=
    integral_congr_ae (hq0.mono fun x hx ↦ ratio_sqrt_sq hx)
  have hP0 : 0 ≤ ∫ x, s x ^ 2 / p x ∂μ := by
    rw [← hPeq]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hQ0 : 0 ≤ ∫ x, s x ^ 2 / q x ∂μ := by
    rw [← hQeq]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hCP0 := hP0.trans hP
  have hCQ0 := hQ0.trans hQ
  have h := common_density_bound hp hq hp0 hq0 hs0 hsp hsq hP' hQ'
  rw [hPeq, hQeq] at h
  have h' : (∫ x, s x ∂μ) ^ 2 ≤ Real.sqrt (C_P * C_Q) * affinity μ p q := by
    rw [Real.sqrt_mul hCP0]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.sqrt_le_sqrt hP) (Real.sqrt_le_sqrt hQ)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (affinity_nonneg p q))
  have hden : 0 < Real.sqrt (C_P * C_Q) := by
    by_contra hn
    have hz : Real.sqrt (C_P * C_Q) = 0 :=
      le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
    rw [hz, zero_mul] at h'
    nlinarith
  exact (div_le_iff₀ hden).2 (by simpa only [mul_comm] using h')

lemma real_rnDeriv_chain {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ] (hνP : ν ≪ P) :
    (fun x ↦ (ν.rnDeriv P x).toReal * (P.rnDeriv ξ x).toReal) =ᵐ[ξ]
      (fun x ↦ (ν.rnDeriv ξ x).toReal) := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ξ) hνP] with x hx
  exact ENNReal.toReal_mul.symm.trans (congrArg ENNReal.toReal hx)

lemma sq_mul_div (a b : ℝ) : (a * b) ^ 2 / b = b * a ^ 2 := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp

lemma rnDeriv_density_moment {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ]
    (hνP : ν ≪ P) (hPξ : P ≪ ξ) :
    (∫ x, (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal ∂ξ) =
      ∫ x, (ν.rnDeriv P x).toReal ^ 2 ∂P := by
  calc
    (∫ x, (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal ∂ξ) =
        ∫ x, (P.rnDeriv ξ x).toReal * (ν.rnDeriv P x).toReal ^ 2 ∂ξ := by
      apply integral_congr_ae
      filter_upwards [real_rnDeriv_chain (ξ := ξ) hνP] with x hx
      rw [← hx, sq_mul_div]
    _ = _ := integral_toReal_rnDeriv_mul hPξ

lemma integrable_rnDeriv_density_moment {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ]
    (hνP : ν ≪ P) (hPξ : P ≪ ξ)
    (h : Integrable (fun x ↦ (ν.rnDeriv P x).toReal ^ 2) P) :
    Integrable (fun x ↦ (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal) ξ := by
  apply ((integrable_toReal_rnDeriv_mul_iff hPξ).2 h).congr
  filter_upwards [real_rnDeriv_chain (ξ := ξ) hνP] with x hx
  rw [← hx, sq_mul_div]

theorem common_measure_affinity {ν P Q : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {C_P C_Q : ℝ} (hνP : ν ≪ P) (hνQ : ν ≪ Q)
    (hm : 0 < ν.real univ)
    (hPi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal ^ 2) P)
    (hQi : Integrable (fun x ↦ (ν.rnDeriv Q x).toReal ^ 2) Q)
    (hP : (∫ x, (ν.rnDeriv P x).toReal ^ 2 ∂P) ≤ C_P)
    (hQ : (∫ x, (ν.rnDeriv Q x).toReal ^ 2 ∂Q) ≤ C_Q) :
    (ν.real univ) ^ 2 / Real.sqrt (C_P * C_Q) ≤ measureAffinity P Q := by
  have hPξ : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQξ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hνξ := hνP.trans hPξ
  have chainP := real_rnDeriv_chain (ξ := P + Q) hνP
  have chainQ := real_rnDeriv_chain (ξ := P + Q) hνQ
  have hsp : ∀ᵐ x ∂(P + Q), (P.rnDeriv (P + Q) x).toReal = 0 →
      (ν.rnDeriv (P + Q) x).toReal = 0 := by
    filter_upwards [chainP] with x hx hz
    rw [← hx, hz, mul_zero]
  have hsq : ∀ᵐ x ∂(P + Q), (Q.rnDeriv (P + Q) x).toReal = 0 →
      (ν.rnDeriv (P + Q) x).toReal = 0 := by
    filter_upwards [chainQ] with x hx hz
    rw [← hx, hz, mul_zero]
  have h := common_density_affinity (C_P := C_P) (C_Q := C_Q)
    (μ := P + Q) (p := fun x ↦ (P.rnDeriv (P + Q) x).toReal)
    (q := fun x ↦ (Q.rnDeriv (P + Q) x).toReal)
    (s := fun x ↦ (ν.rnDeriv (P + Q) x).toReal)
    Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
    Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    hsp hsq
    (integrable_rnDeriv_density_moment hνP hPξ hPi)
    (integrable_rnDeriv_density_moment hνQ hQξ hQi)
    (by rwa [rnDeriv_density_moment hνP hPξ])
    (by rwa [rnDeriv_density_moment hνQ hQξ])
    (by rwa [Measure.integral_toReal_rnDeriv hνξ])
  simpa only [Measure.integral_toReal_rnDeriv hνξ, measureAffinity] using h

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalAffinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

lemma actual_common_gain {X : Type*} [MeasurableSpace X] (σ P Q : Measure X)
    [IsFiniteMeasure σ] [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {B : ℝ} (hB : 1 ≤ B) (hm : (1/2:ℝ≥0∞) ≤ σ univ)
    (hp : σ≪P) (hq : σ≪Q)
    (hip : Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P)
    (hiq : Integrable (fun z ↦ (σ.rnDeriv Q z).toReal^2) Q)
    (hmp : (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ 2*B)
    (hmq : (∫z,(σ.rnDeriv Q z).toReal^2 ∂Q) ≤ 2*B) :
    1/(8*B) ≤ measureAffinity P Q := by
  have hm' : (1/2:ℝ) ≤ σ.real univ := by
    have H := ENNReal.toReal_mono (measure_ne_top σ univ) hm
    norm_num [Measure.real] at H ⊢
    exact H
  have h := common_measure_affinity hp hq (by linarith : 0 < σ.real univ) hip hiq hmp hmq
  rw [show (2*B)*(2*B)=(2*B)^2 by ring,Real.sqrt_sq (by linarith : 0 ≤ 2*B)] at h
  refine le_trans ?_ h
  apply (div_le_div_iff₀ (by linarith : 0 < 8*B) (by linarith : 0 < 2*B)).mpr
  have hm2 : (1/4:ℝ) ≤ (σ.real univ)^2 := by nlinarith
  nlinarith

end HardSphere.Comparison

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Density_DensityOperators
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}

lemma Operator.root_positive (T : Operator H) : T.root.IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)

lemma Operator.root_sq (T : Operator H) : T.root*T.root=T.toCLM :=
  CFC.sqrt_mul_sqrt_self _ T.positive

lemma Operator.root_norm_sq (T : Operator H) (x : H) :
    ‖T.root x‖^2=(inner ℂ x (T.toCLM x)).re := by
  calc
    _ = (inner ℂ (T.root x) (T.root x)).re := by exact norm_sq_eq_re_inner (𝕜:=ℂ) _
    _ = (inner ℂ x (T.root (T.root x))).re := congrArg Complex.re (T.root_positive.isSymmetric x (T.root x))
    _ = _ := by rw [←mul_apply_eq_comp,T.root_sq]

lemma Operator.root_hasSum (T : Operator H) :
    HasSum (fun i : basisSet H ↦ ‖T.root (basis H i)‖^2) 1 := by
  simpa only [T.root_norm_sq] using T.trace_one

lemma Operator.root_mem_support (T : Operator H) (x : H) :
    T.root x∈T.toCLM.kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  have hy0 : T.toCLM y=0 := hy
  have hr : T.root y=0 := by
    have hh := T.root_norm_sq y
    rw [hy0,inner_zero_right,Complex.zero_re] at hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hs : inner ℂ (T.root x) y=inner ℂ x (T.root y) := T.root_positive.isSymmetric x y
  rw [hs,hr,inner_zero_right]

end HardSphere.Density

namespace HardSphere.Density
open ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
lemma parseval {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i ↦ ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  simpa [HilbertBasis.repr_apply_apply] using lp.hasSum_norm (p:=2) (by norm_num) (b.repr x)

omit [CompleteSpace K] in
lemma Operator.image_summable (T : Operator H) (A : H →L[ℂ] K) :
    Summable (fun i : basisSet H ↦ ‖A (T.root (basis H i))‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    (fun i ↦ ?_) (T.root_hasSum.summable.mul_left (‖A‖^2))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (T.root (basis H i))) 2


omit [CompleteSpace K] in
lemma Operator.entry_row {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (i : basisSet H) :
    HasSum (T.entry A b i) (‖A (T.root (basis H i))‖^2) :=
  parseval (H:=K) b (A (T.root (basis H i)))

lemma Operator.entry_col {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (j : ι) :
    HasSum (fun i ↦ T.entry A b i j) (‖T.root (A.adjoint (b j))‖^2) := by
  have hh := parseval (basis H) (T.root (A.adjoint (b j)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  dsimp only [Operator.entry]
  have ha : inner ℂ (b j) (A (T.root (basis H i)))=
      inner ℂ (A.adjoint (b j)) (T.root (basis H i)) := (A.adjoint_inner_left _ _).symm
  have ht : inner ℂ (A.adjoint (b j)) (T.root (basis H i))=
      inner ℂ (T.root (A.adjoint (b j))) (basis H i) := (T.root_positive.isSymmetric _ _).symm
  rw [ha,ht,norm_inner_symm]

omit [CompleteSpace K] in
lemma Operator.entry_summable {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) : Summable (Function.uncurry (T.entry A b)) := by
  apply (summable_prod_of_nonneg (fun p ↦ sq_nonneg _)).mpr
  refine ⟨fun i ↦ (T.entry_row A b i).summable,?_⟩
  convert T.image_summable A using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact (T.entry_row A b i).tsum_eq

lemma Operator.trace_basis_identity {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) :
    (∑' i : basisSet H,‖A (T.root (basis H i))‖^2)=
      ∑' j : ι,(inner ℂ (A.adjoint (b j)) (T.toCLM (A.adjoint (b j)))).re := by
  calc
    _ = ∑' i : basisSet H,∑' j : ι,T.entry A b i j :=
      tsum_congr fun i ↦ (T.entry_row A b i).tsum_eq.symm
    _ = ∑' j : ι,∑' i : basisSet H,T.entry A b i j := (T.entry_summable A b).tsum_comm.symm
    _ = ∑' j : ι,‖T.root (A.adjoint (b j))‖^2 :=
      tsum_congr fun j ↦ (T.entry_col A b j).tsum_eq
    _ = _ := by simp only [T.root_norm_sq]

lemma Operator.compressionTrace_eq (T : Operator H) (A : H →L[ℂ] K) :
    T.compressionTrace A=∑' i : basisSet H,‖A (T.root (basis H i))‖^2 :=
  (T.trace_basis_identity A (basis K)).symm

end HardSphere.Density
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Density_DensityBounds
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
lemma quadratic_lower_of_unit (V : Submodule ℂ H) (A : H →L[ℂ] K) {c : ℝ}
    (h : ∀x∈V,‖x‖=1 → c≤‖A x‖^2) {x : H} (hx : x∈V) :
    c*‖x‖^2≤‖A x‖^2 := by
  by_cases hz : x=0
  · simp [hz]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hz
  have hv : (‖x‖⁻¹:ℝ) • x∈V := by
    exact V.smul_mem ((‖x‖⁻¹:ℝ):ℂ) hx
  have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  have hh := h _ hv hu
  rw [A.map_smul_of_tower,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),mul_pow] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
  calc
    _ ≤ (‖x‖⁻¹)^2*‖A x‖^2*‖x‖^2 := hm
    _ = _ := by field_simp

lemma Operator.compressionTrace_lower (T : Operator H) (A : H →L[ℂ] K) {c : ℝ}
    (h : ∀x∈T.toCLM.kerᗮ,‖x‖=1 → c≤‖A x‖^2) :
    c≤T.compressionTrace A := by
  rw [T.compressionTrace_eq]
  have hs := T.root_hasSum.mul_left c
  calc
    c = ∑' i : basisSet H,c*‖T.root (basis H i)‖^2 := by simpa using hs.tsum_eq.symm
    _ ≤ _ := hs.summable.tsum_le_tsum (fun i ↦ quadratic_lower_of_unit _ A h (T.root_mem_support _))
      (T.image_summable A)

lemma Operator.compressionTrace_upper (T : Operator H) (A : H →L[ℂ] K)
    (h : ∀x,‖A x‖≤‖x‖) : T.compressionTrace A≤1 := by
  rw [T.compressionTrace_eq,←T.root_hasSum.tsum_eq]
  exact (T.image_summable A).tsum_le_tsum (fun i ↦ pow_le_pow_left₀ (norm_nonneg _) (h _) 2)
    T.root_hasSum.summable

end HardSphere.Density
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_Index
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace HardSphere.DyadicSkeleton

lemma uniform_abs_le (ω : Noise) (j : Fin 2) (ℓ k : ℕ) :
    |uniform ω j ℓ k| ≤ 1 := by
  have h := (ω (j,ℓ,k)).property
  simp only [uniform, abs_le]
  constructor <;> linarith [h.1,h.2]

lemma decay_pos : 0 < decay := Real.rpow_pos_of_pos (by norm_num) _
lemma decay_lt_one : decay < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
lemma cvel_pos : 0 < cvel := by unfold cvel; linarith [decay_lt_one]

lemma summable_velocity (ω : Noise) (j : Fin 2) (i : ℕ) :
    Summable (fun ℓ : ℕ ↦ decay^ℓ * uniform ω j ℓ (i/2^ℓ)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one decay_pos.le decay_lt_one)
  intro ℓ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg decay_pos.le _)]
  exact (mul_le_mul_of_nonneg_left (uniform_abs_le ω j ℓ _) (pow_nonneg decay_pos.le _)).trans_eq (mul_one _)

lemma velocity_abs_le (ω : Noise) (j : Fin 2) (i : ℕ) :
    |velocity ω j i| ≤ 1/2 := by
  have hsum : |∑' ℓ : ℕ, decay^ℓ * uniform ω j ℓ (i/2^ℓ)| ≤
      ∑' ℓ : ℕ, decay^ℓ := by
    apply (norm_tsum_le_tsum_norm (summable_velocity ω j i).norm).trans
    apply Summable.tsum_le_tsum _ (summable_velocity ω j i).norm
      (summable_geometric_of_lt_one decay_pos.le decay_lt_one)
    intro ℓ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg decay_pos.le _)]
    simpa using mul_le_mul_of_nonneg_left (uniform_abs_le ω j ℓ _) (pow_nonneg decay_pos.le _)
  rw [tsum_geometric_of_lt_one decay_pos.le decay_lt_one] at hsum
  rw [velocity,abs_mul,abs_of_pos cvel_pos]
  calc
    _ ≤ cvel * (1-decay)⁻¹ := mul_le_mul_of_nonneg_left hsum cvel_pos.le
    _ = 1/2 := by
      unfold cvel
      have hd : 1-decay ≠ 0 := ne_of_gt (sub_pos.mpr decay_lt_one)
      field_simp

lemma position_succ (ω : Noise) (j : Fin 2) (t : ℕ) :
    position ω j (t+1) = position ω j t + velocity ω j t := by
  exact Finset.sum_range_succ _ _

lemma exists_fresh_block (t k : ℕ) (hk : 0 < k) :
    ∃ ℓ b : ℕ, t ≤ b*2^ℓ ∧ (b+1)*2^ℓ ≤ t+k ∧ k ≤ 4*2^ℓ := by
  by_cases hk1 : k=1
  · subst k
    exact ⟨0,t,by simp,by simp,by norm_num⟩
  have hk2 : 1 ≤ k/2 := by omega
  let ℓ := Nat.log 2 (k/2)
  let d := 2^ℓ
  have hd : 0 < d := by dsimp [d]; positivity
  have hdle : d ≤ k/2 := Nat.pow_log_le_self 2 (by omega)
  have hdgt : k/2 < 2*d := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (k/2)
    simpa only [Nat.pow_succ,Nat.mul_comm] using h
  refine ⟨ℓ,t/d+1,?_,?_,?_⟩
  · change t ≤ (t/d+1)*d
    have h₁ := Nat.mod_lt t hd
    have h₂ := Nat.mod_add_div t d
    nlinarith
  · change (t/d+1+1)*d ≤ t+k
    have h := Nat.div_mul_le_self t d
    have h₂ : 2*d ≤ k := by omega
    nlinarith
  · change k ≤ 4*d
    omega

lemma resample_preserving (q : Index) :
    MeasurePreserving (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2)
      (law.prod volume) law := by
  classical
  refine ⟨measurable_update', ?_⟩
  apply Measure.eq_infinitePi
  intro s A hA
  rw [Measure.map_apply measurable_update' (.pi s.countable_toSet fun i _ ↦ hA i)]
  by_cases hq : q ∈ s
  · have he : (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2) ⁻¹'
        ((s : Set Index).pi A) = ((s.erase q : Set Index).pi A) ×ˢ A q := by
      ext z
      simp only [mem_preimage,Set.mem_pi,Finset.mem_coe,mem_prod,Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi ↦ ?_, ?_⟩
        · simpa [Function.update_of_ne hi.1] using h i hi.2
        · simpa using h q hq
      · rintro ⟨h,h'⟩ i hi
        by_cases hiq : i=q
        · subst i; simpa using h'
        · simpa [Function.update_of_ne hiq] using h i ⟨hiq,hi⟩
    rw [he,Measure.prod_prod,law,Measure.infinitePi_pi _ (fun i _ ↦ hA i)]
    exact Finset.prod_erase_mul s (fun i ↦ volume (A i)) hq
  · have he : (fun z : Noise × unitInterval ↦ Function.update z.1 q z.2) ⁻¹'
        ((s : Set Index).pi A) = ((s : Set Index).pi A) ×ˢ univ := by
      ext z
      simp only [mem_preimage,Set.mem_pi,Finset.mem_coe,mem_prod,mem_univ,and_true]
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      have hiq : i≠q := by intro he; subst i; exact hq hi
      rw [Function.update_of_ne hiq]
    rw [he,Measure.prod_prod,measure_univ,mul_one,law,
      Measure.infinitePi_pi _ (fun i _ ↦ hA i)]

lemma lintegral_resample (q : Index) (f : Noise → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂law) =
      ∫⁻ ω, ∫⁻ x : unitInterval, f (Function.update ω q x) ∂volume ∂law := by
  rw [← (resample_preserving q).lintegral_comp hf]
  exact lintegral_prod _ (hf.comp measurable_update').aemeasurable

lemma velocity_update_sub (ω : Noise) (j : Fin 2) (ℓ b i : ℕ)
    (x : unitInterval) :
    velocity (Function.update ω (j,ℓ,b) x) j i - velocity ω j i =
      if i/2^ℓ=b then cvel * decay^ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) else 0 := by
  classical
  rw [velocity,velocity,←mul_sub,← (summable_velocity _ j i).tsum_sub
    (summable_velocity ω j i)]
  have he : (fun a ↦ decay^a * uniform (Function.update ω (j,ℓ,b) x) j a (i/2^a) -
      decay^a * uniform ω j a (i/2^a)) =
      (fun a ↦ if a=ℓ then decay^ℓ *
        (if i/2^ℓ=b then 2*((x:ℝ)-(ω (j,ℓ,b):ℝ)) else 0) else 0) := by
    funext a
    by_cases ha : a=ℓ
    · subst a
      by_cases hi : i/2^ℓ=b
      · simp [hi,uniform]
        ring
      · simp [hi,uniform]
    · simp [ha,uniform]
  rw [he,tsum_ite_eq]
  split_ifs <;> ring

lemma position_update_past (ω : Noise) (j : Fin 2) (ℓ b t : ℕ)
    (ht : t ≤ b*2^ℓ) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j t = position ω j t := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < b*2^ℓ := (Finset.mem_range.mp hi).trans_le ht
  have hn : i/2^ℓ ≠ b := by
    intro he
    have hd := Nat.div_mul_le_self i (2^ℓ)
    rw [he] at hd
    omega
  have h := velocity_update_sub ω j ℓ b i x
  rw [ite_eq_right hn] at h
  linarith

lemma block_filter (ℓ b n : ℕ) (hn : (b+1)*2^ℓ ≤ n) :
    (Finset.range n).filter (fun i ↦ i/2^ℓ=b) =
      Finset.Ico (b*2^ℓ) ((b+1)*2^ℓ) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  constructor
  · rintro ⟨hi,hd⟩
    have hlo := Nat.div_mul_le_self i (2^ℓ)
    have hhi := Nat.mod_lt i (by positivity : 0 < 2^ℓ)
    have he := Nat.mod_add_div i (2^ℓ)
    rw [hd] at hlo he
    constructor
    · exact hlo
    · nlinarith
  · rintro ⟨hlo,hhi⟩
    exact ⟨hhi.trans_le hn,Nat.div_eq_of_lt_le hlo hhi⟩

lemma position_update_future (ω : Noise) (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j n - position ω j n =
      (2^ℓ:ℕ) * cvel * decay^ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) := by
  classical
  rw [position,position,← Finset.sum_sub_distrib]
  simp_rw [velocity_update_sub]
  rw [← Finset.sum_filter,block_filter ℓ b n hn]
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
  have he : (b+1)*2^ℓ-b*2^ℓ=2^ℓ := by rw [Nat.add_mul,one_mul,Nat.add_sub_cancel_left]
  rw [he]
  ring

lemma position_update_other (ω : Noise) (j j' : Fin 2) (hjj : j' ≠ j)
    (ℓ b n : ℕ) (x : unitInterval) :
    position (Function.update ω (j,ℓ,b) x) j' n = position ω j' n := by
  unfold position velocity
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply tsum_congr
  intro a
  have hn : (j',a,i/2^a) ≠ (j,ℓ,b) := by
    intro h; exact hjj (congrArg Prod.fst h)
  simp only [uniform,Function.update_of_ne hn]

lemma affine_interval_volume (A B y R : ℝ) (hA : 0 < A) :
    volume {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} ≤ ENNReal.ofReal (2*R/A) := by
  rw [unitInterval.volume_apply]
  have hs : Subtype.val '' {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} ⊆
      Icc ((y-B-R)/A) ((y-B+R)/A) := by
    rintro z ⟨x,hx,rfl⟩
    change |A*(x:ℝ)+B-y| ≤ R at hx
    have hx' := abs_le.mp hx
    constructor
    · rw [div_le_iff₀ hA]
      nlinarith
    · rw [le_div_iff₀ hA]
      nlinarith
  refine (measure_mono hs).trans_eq ?_
  rw [Real.volume_Icc]
  congr 1
  ring

lemma coordinateTest_update_other (ω : Noise) (j j' : Fin 2) (hjj : j' ≠ j)
    (ℓ b n : ℕ) (y R : ℝ) (x : unitInterval) :
    coordinateTest j' n y R (Function.update ω (j,ℓ,b) x) =
      coordinateTest j' n y R ω := by
  simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,
    position_update_other ω j j' hjj ℓ b n x]

lemma coordinateTest_update_past (ω : Noise) (j j' : Fin 2)
    (ℓ b n : ℕ) (hn : n ≤ b*2^ℓ) (y R : ℝ) (x : unitInterval) :
    coordinateTest j' n y R (Function.update ω (j,ℓ,b) x) =
      coordinateTest j' n y R ω := by
  by_cases hjj : j'=j
  · subst j'
    simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,
      position_update_past ω j ℓ b n hn x]
  · exact coordinateTest_update_other ω j j' hjj ℓ b n y R x

lemma freshScale_pos (ℓ : ℕ) : 0 < freshScale ℓ := by
  unfold freshScale
  exact mul_pos (mul_pos (by positivity) cvel_pos) (pow_pos decay_pos _)

lemma fresh_coordinate_integral (ω : Noise) (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (y R : ℝ) :
    (∫⁻ x : unitInterval, coordinateTest j n y R (Function.update ω (j,ℓ,b) x)) ≤
      ENNReal.ofReal (R/freshScale ℓ) := by
  let A := 2*freshScale ℓ
  let B := position ω j n - 2*freshScale ℓ*(ω (j,ℓ,b):ℝ)
  have he (x : unitInterval) : position (Function.update ω (j,ℓ,b) x) j n =
      A*(x:ℝ)+B := by
    have h := position_update_future ω j ℓ b n hn x
    change _ = freshScale ℓ * (2*((x:ℝ)-(ω (j,ℓ,b):ℝ))) at h
    dsimp only [A,B]
    linarith
  have hm : MeasurableSet {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R} := by
    apply measurableSet_le _ measurable_const
    fun_prop
  simp only [coordinateTest,Set.indicator_apply,Set.mem_ofPred_eq,he]
  change (∫⁻ x : unitInterval,
    {x : unitInterval | |A*(x:ℝ)+B-y| ≤ R}.indicator (fun _ ↦ 1) x) ≤ _
  rw [lintegral_indicator hm]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  refine (affine_interval_volume A B y R (mul_pos (by norm_num) (freshScale_pos ℓ))).trans_eq ?_
  congr 1
  dsimp only [A]
  field_simp

lemma fresh_weighted_coordinate (j : Fin 2) (ℓ b n : ℕ)
    (hn : (b+1)*2^ℓ ≤ n) (y R : ℝ) (H : Noise → ℝ≥0∞) (hH : Measurable H)
    (hinv : ∀ ω x, H (Function.update ω (j,ℓ,b) x) = H ω) :
    (∫⁻ ω, H ω * coordinateTest j n y R ω ∂law) ≤
      ENNReal.ofReal (R/freshScale ℓ) * ∫⁻ ω, H ω ∂law := by
  rw [lintegral_resample (j,ℓ,b) (fun ω ↦ H ω * coordinateTest j n y R ω)
    (hH.mul (measurable_coordinateTest j n y R))]
  simp_rw [hinv]
  calc
    _ = ∫⁻ ω, H ω * ∫⁻ x : unitInterval,
        coordinateTest j n y R (Function.update ω (j,ℓ,b) x) ∂volume ∂law := by
      apply lintegral_congr
      intro ω
      exact lintegral_const_mul _ ((measurable_coordinateTest j n y R).comp
        (measurable_update ω))
    _ ≤ ∫⁻ ω, H ω * ENNReal.ofReal (R/freshScale ℓ) ∂law := by
      apply lintegral_mono
      intro ω
      exact mul_le_mul_right (fresh_coordinate_integral ω j ℓ b n hn y R) (H ω)
    _ = _ := by rw [lintegral_mul_const _ hH,mul_comm]

lemma nearTest_le_one (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) :
    nearTest n y R ω ≤ 1 := by
  unfold nearTest coordinateTest
  simp only [Set.indicator_apply]
  split_ifs <;> simp_all

lemma nearTest_pastInvariant (n t : ℕ) (hnt : n ≤ t) (y : Fin 2 → ℝ) (R : ℝ) :
    PastInvariant t (nearTest n y R) := by
  intro j ℓ b hb ω x
  simp only [nearTest,coordinateTest_update_past ω j 0 ℓ b n (hnt.trans hb),
    coordinateTest_update_past ω j 1 ℓ b n (hnt.trans hb)]

lemma fresh_weighted_pair (ℓ b n : ℕ) (hn : (b+1)*2^ℓ ≤ n)
    (y : Fin 2 → ℝ) (R : ℝ) (H : Noise → ℝ≥0∞) (hH : Measurable H)
    (hinv : ∀ j : Fin 2, ∀ ω x, H (Function.update ω (j,ℓ,b) x) = H ω) :
    (∫⁻ ω, H ω * nearTest n y R ω ∂law) ≤
      ENNReal.ofReal (R/freshScale ℓ)^2 * ∫⁻ ω, H ω ∂law := by
  let a := ENNReal.ofReal (R/freshScale ℓ)
  calc
    _ = ∫⁻ ω, (H ω * coordinateTest 1 n (y 1) R ω) *
        coordinateTest 0 n (y 0) R ω ∂law := by
      apply lintegral_congr; intro ω; simp only [nearTest]; ring
    _ ≤ a * ∫⁻ ω, H ω * coordinateTest 1 n (y 1) R ω ∂law :=
      fresh_weighted_coordinate 0 ℓ b n hn (y 0) R _
        (hH.mul (measurable_coordinateTest 1 n (y 1) R)) (by
          intro ω x
          rw [hinv 0,coordinateTest_update_other ω 0 1 (by decide)])
    _ ≤ a * (a * ∫⁻ ω, H ω ∂law) :=
      mul_le_mul_right (fresh_weighted_coordinate 1 ℓ b n hn (y 1) R H hH (hinv 1)) a
    _ = _ := by ring

lemma freshScale_eq_rpow (ℓ : ℕ) :
    freshScale ℓ = cvel * ((2:ℝ)^ℓ)^((3:ℝ)/4) := by
  have hd : decay^ℓ = ((2:ℝ)^ℓ)^(-(1:ℝ)/4) := by
    rw [decay,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [freshScale,Nat.cast_pow,Nat.cast_ofNat,hd]
  calc
    _ = cvel * (((2:ℝ)^ℓ)^((1:ℝ)) * ((2:ℝ)^ℓ)^(-(1:ℝ)/4)) := by
      rw [Real.rpow_one]; ring
    _ = cvel * ((2:ℝ)^ℓ)^((1:ℝ)+(-(1:ℝ)/4)) := by
      rw [Real.rpow_add (by positivity)]
    _ = _ := by norm_num

lemma freshScale_sq (ℓ : ℕ) :
    freshScale ℓ ^ 2 = cvel^2 * ((2:ℝ)^ℓ)^((3:ℝ)/2) := by
  rw [freshScale_eq_rpow,mul_pow,← Real.rpow_mul_natCast (by positivity)]
  norm_num

lemma freshScale_gap_bound (k ℓ : ℕ) (hk : 0 < k) (hkℓ : k ≤ 4*2^ℓ) (R : ℝ) :
    (R/freshScale ℓ)^2 ≤ (16*R^2/cvel^2) * (k:ℝ)^(-(3:ℝ)/2) := by
  have hd : 0 < (2:ℝ)^ℓ := by positivity
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hpow : (k:ℝ)^((3:ℝ)/2) ≤ 16*((2:ℝ)^ℓ)^((3:ℝ)/2) := by
    have hg : (k:ℝ) ≤ 4*(2:ℝ)^ℓ := by exact_mod_cast hkℓ
    calc
      _ ≤ (4*(2:ℝ)^ℓ)^((3:ℝ)/2) :=
        Real.rpow_le_rpow hk'.le hg (by norm_num)
      _ = (4:ℝ)^((3:ℝ)/2) * ((2:ℝ)^ℓ)^((3:ℝ)/2) :=
        Real.mul_rpow (by norm_num) hd.le
      _ ≤ 16 * ((2:ℝ)^ℓ)^((3:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
          (by norm_num : (3:ℝ)/2 ≤ 2)
        norm_num at h ⊢
  have hc2 : 0 < cvel^2 := sq_pos_of_pos cvel_pos
  have hd2 : 0 < ((2:ℝ)^ℓ)^((3:ℝ)/2) := Real.rpow_pos_of_pos hd _
  have hk2 : 0 < (k:ℝ)^((3:ℝ)/2) := Real.rpow_pos_of_pos hk' _
  rw [div_pow,freshScale_sq]
  rw [show -(3:ℝ)/2 = -((3:ℝ)/2) by ring,Real.rpow_neg hk'.le,← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos hc2 hd2) hk2).mpr
  calc
    _ ≤ R^2 * (16*((2:ℝ)^ℓ)^((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg R)
    _ = _ := by field_simp [ne_of_gt cvel_pos]

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_TimeGaps
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma weighted_gap_concentration (t k : ℕ) (hk : 0 < k)
    (y : Fin 2 → ℝ) (R : ℝ) (hR : 0 ≤ R) (H : Noise → ℝ≥0∞)
    (hH : Measurable H) (hinv : PastInvariant t H) :
    (∫⁻ ω, H ω * nearTest (t+k) y R ω ∂law) ≤
      ENNReal.ofReal ((16*R^2/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) *
        ∫⁻ ω, H ω ∂law := by
  obtain ⟨ℓ,b,ht,hf,hkℓ⟩ := exists_fresh_block t k hk
  refine (fresh_weighted_pair ℓ b (t+k) hf y R H hH
    (fun j ↦ hinv j ℓ b ht)).trans ?_
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_pow (div_nonneg hR (freshScale_pos ℓ).le)]
  exact ENNReal.ofReal_le_ofReal (freshScale_gap_bound k ℓ hk hkℓ R)

lemma timeGaps_castSucc {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.castSucc = timeGaps (Fin.init t) i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact Fin.cases rfl (fun _ ↦ rfl) i

lemma timeGaps_injective {n : ℕ} :
    Function.Injective (fun t : {t : Fin n → ℕ // Monotone t} ↦ timeGaps t.val) := by
  intro t s h
  apply Subtype.ext
  funext i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.induction ?_ (fun j ih ↦ ?_) i
    · exact congrFun h 0
    · have he := congrFun h j.succ
      simp only [timeGaps_succ] at he
      have ht := t.property (Fin.castSucc_le_succ j)
      have hs := s.property (Fin.castSucc_le_succ j)
      omega

lemma tsum_vector_prod {n : ℕ} (f : Fin n → ℕ → ℝ≥0∞) :
    (∑' g : Fin n → ℕ, ∏ i, f i (g i)) = ∏ i, ∑' k, f i k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (splitVectorEquiv n ℕ).symm.tsum_eq]
    change (∑' v : ℕ × (Fin n → ℕ), ∏ i, f i (Fin.cases v.1 v.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right]

lemma ordered_gap_sum_bound (T n : ℕ) (b : ℕ → ℝ≥0∞) :
    (∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}, ∏ i, b (timeGaps t.val i)) ≤
      (∑' k, b k)^n := by
  let g : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T} → (Fin n → ℕ) :=
    fun t ↦ timeGaps t.val
  have hg : Function.Injective g := by
    intro t s he
    have hv := timeGaps_injective (a₁ := ⟨t.val,t.property.1.monotone⟩)
      (a₂ := ⟨s.val,s.property.1.monotone⟩) he
    exact Subtype.ext (congrArg (fun q : {f : Fin n → ℕ // Monotone f} ↦ q.val) hv)
  have h := ENNReal.tsum_comp_le_tsum_of_injective hg (fun v : Fin n → ℕ ↦ ∏ i, b (v i))
  simpa only [g, tsum_vector_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

lemma decode_encode (T : ℕ) (s : TimeSubset T) : decodeTimes (encodeTimeSubset T s) = s.val := by
  exact s.val.image_orderEmbOfFin_univ rfl

lemma encodeTimeSubset_injective (T : ℕ) : Function.Injective (encodeTimeSubset T) := by
  intro s t h
  apply Subtype.ext
  simpa only [decode_encode] using congrArg decodeTimes h

lemma prod_encode (T : ℕ) (s : TimeSubset T) (f : ℕ → ℝ≥0∞) :
    (∏ i, f ((encodeTimeSubset T s).2.val i)) = ∏ u ∈ s.val, f u := by
  change (∏ i, f (s.val.orderEmbOfFin rfl i)) = _
  conv_rhs => rw [← s.val.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

lemma prod_one_add_le_ordered_series (T : ℕ) (f : ℕ → ℝ≥0∞) :
    (∏ u ∈ Finset.range (T+1), (1+f u)) ≤
      ∑' n, ∑' t : BoundedTimes T n, ∏ i, f (t.val i) := by
  rw [Finset.prod_one_add]
  calc
    _ = ∑' s : TimeSubset T, ∏ u ∈ s.val, f u := by
      rw [tsum_fintype]
      exact (Finset.sum_attach _ _).symm
    _ = ∑' s : TimeSubset T, ∏ i, f ((encodeTimeSubset T s).2.val i) := by
      apply tsum_congr
      intro s
      exact (prod_encode T s f).symm
    _ ≤ ∑' v : Σ n, BoundedTimes T n, ∏ i, f (v.2.val i) :=
      ENNReal.tsum_comp_le_tsum_of_injective (encodeTimeSubset_injective T)
        (fun v : Σ n, BoundedTimes T n ↦ ∏ i, f (v.2.val i))
    _ = _ := ENNReal.tsum_sigma' _

lemma radiusFactor_one_le (R : ℝ) (hR : 0 ≤ R) : 1 ≤ radiusFactor R := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma weighted_gap_radius (t k : ℕ) (hk : 0 < k)
    (y : Fin 2 → ℝ) (R : ℝ) (hR : 0 ≤ R) (H : Noise → ℝ≥0∞)
    (hH : Measurable H) (hinv : PastInvariant t H) :
    (∫⁻ ω, H ω * nearTest (t+k) y R ω ∂law) ≤
      radiusFactor R * gapKernel k * ∫⁻ ω, H ω ∂law := by
  refine (weighted_gap_concentration t k hk y R hR H hH hinv).trans ?_
  apply mul_le_mul_left
  rw [gapKernel,ite_eq_right (ne_of_gt hk),radiusFactor,
    ← ENNReal.ofReal_mul (sq_nonneg (1+R))]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2) := by positivity
  calc
    _ = R^2 * ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hp

lemma encounter_append_bound (u s : ℕ) (hus : u < s)
    {n : ℕ} (t : Fin n → ℕ) (r : Fin n → ℝ) (y : ℕ → Fin 2 → ℝ)
    (ht : ∀ i, t i ≤ u) (R : ℝ) (hR : 0 ≤ R) :
    encounterMass (Fin.snoc t s) (Fin.snoc r R) y ≤
      radiusFactor R * gapKernel (s-u) * encounterMass t r y := by
  have h := weighted_gap_radius u (s-u) (by omega) (y s) R hR
    (fun ω ↦ ∏ i, nearTest (t i) (y (t i)) (r i) ω) (by fun_prop) (by
      intro j ℓ b hb ω x
      apply Finset.prod_congr rfl
      intro i _
      exact nearTest_pastInvariant (t i) u (ht i) (y (t i)) (r i) j ℓ b hb ω x)
  rw [Nat.add_sub_of_le hus.le] at h
  simpa only [encounterMass,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last] using h

lemma encounter_singleton_bound (s : ℕ) (R : ℝ) (hR : 0 ≤ R) (y : ℕ → Fin 2 → ℝ) :
    encounterMass (fun _ : Fin 1 ↦ s) (fun _ ↦ R) y ≤ radiusFactor R * gapKernel s := by
  by_cases h0 : s=0
  · subst s
    refine le_trans ?_ (by simpa [gapKernel] using radiusFactor_one_le R hR)
    calc
      _ ≤ ∫⁻ _ : Noise, 1 ∂law := by
        apply lintegral_mono
        intro ω
        simpa only [Fin.prod_univ_one] using nearTest_le_one 0 (y 0) R ω
      _ = 1 := by simp
  · have h := weighted_gap_radius 0 s (by omega) (y s) R hR
      (fun _ ↦ 1) measurable_const (by intro j ℓ b hb ω x; rfl)
    simpa [encounterMass,Fin.prod_univ_one] using h

lemma encounterMass_le_gap_prod (n : ℕ) (t : Fin n → ℕ) (r : Fin n → ℝ)
    (y : ℕ → Fin 2 → ℝ) (ht : StrictMono t) (hr : ∀ i, 0 ≤ r i) :
    encounterMass t r y ≤ ∏ i, radiusFactor (r i) * gapKernel (timeGaps t i) := by
  induction n with
  | zero => simp [encounterMass]
  | succ n ih =>
    cases n with
    | zero =>
      have h := encounter_singleton_bound (t 0) (r 0) (hr 0) y
      have he : (fun _ : Fin 1 ↦ t 0) = t := by
        funext i; exact congrArg t (Fin.ext (by omega))
      have hl : (fun _ : Fin 1 ↦ r 0) = r := by
        funext i; exact congrArg r (Fin.ext (by omega))
      rw [he, hl] at h
      rw [Fin.prod_univ_one, timeGaps_zero]
      exact h
    | succ n =>
      have hin : StrictMono (Fin.init t) := ht.comp (Fin.strictMono_castSucc)
      have hb := ih (Fin.init t) (Fin.init r) hin (fun i ↦ hr i.castSucc)
      have hlt : t (Fin.last n).castSucc < t (Fin.last (n+1)) := ht (by simp)
      have ha := encounter_append_bound (t (Fin.last n).castSucc) (t (Fin.last (n+1)))
        hlt (Fin.init t) (Fin.init r) y
        (fun i ↦ ht.monotone (by exact_mod_cast Fin.le_last i))
        (r (Fin.last (n+1))) (hr _)
      rw [Fin.snoc_init_self, Fin.snoc_init_self] at ha
      refine ha.trans ?_
      rw [Fin.prod_univ_castSucc]
      calc
        _ ≤ radiusFactor (r (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc) *
            ∏ i, radiusFactor (Fin.init r i) * gapKernel (timeGaps (Fin.init t) i) :=
          mul_le_mul' le_rfl hb
        _ = _ := by
          simp_rw [timeGaps_castSucc]
          change _ = _ * (radiusFactor (r (Fin.last (n+1))) *
            gapKernel (t (Fin.last (n+1))-t (Fin.last n).castSucc))
          exact mul_comm _ _

lemma gapKernel_sum_ne_top : (∑' k, gapKernel k) ≠ ∞ := by
  have hs : Summable (fun k : ℕ ↦ (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  have he : (∑' k : ℕ, ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2))) =
      ENNReal.ofReal (∑' k : ℕ, (16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs).symm
  have hb : (∑' k, gapKernel k) ≤
      1 + ∑' k : ℕ, ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)) := by
    calc
      _ ≤ (∑' k : ℕ, ((if k=0 then 1 else 0) +
          ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2)))) := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases h : k=0 <;> simp [gapKernel,h]
      _ = _ := by rw [ENNReal.tsum_add]; simp
  rw [he] at hb
  exact ne_top_of_le_ne_top (by finiteness) hb

lemma orderedEncounterConstant_cast : ENNReal.ofReal orderedEncounterConstant = ∑' k, gapKernel k :=
  ENNReal.ofReal_toReal gapKernel_sum_ne_top

lemma ordered_encounter_sum (T n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (y : ℕ → Fin 2 → ℝ) :
    (∑' t : BoundedTimes T n, encounterMass t.val r y) ≤
      ∏ i, ENNReal.ofReal orderedEncounterConstant * radiusFactor (r i) := by
  calc
    _ ≤ ∑' t : BoundedTimes T n, ∏ i, radiusFactor (r i) * gapKernel (timeGaps t.val i) :=
      ENNReal.tsum_le_tsum fun t ↦ encounterMass_le_gap_prod n t.val r y t.property.1 hr
    _ = (∏ i, radiusFactor (r i)) *
        ∑' t : BoundedTimes T n, ∏ i, gapKernel (timeGaps t.val i) := by
      simp_rw [Finset.prod_mul_distrib,ENNReal.tsum_mul_left]
    _ ≤ (∏ i, radiusFactor (r i)) * (∑' k, gapKernel k)^n :=
      mul_le_mul' le_rfl (ordered_gap_sum_bound T n gapKernel)
    _ = _ := by
      rw [Finset.prod_mul_distrib,orderedEncounterConstant_cast]
      simp [mul_comm]

lemma radiusEnvelope_prod {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) (ω : Noise) :
    (∏ i, radiusEnvelope a (t i) (y (t i)) ω) =
      ∑' l : Fin n → ℕ, (∏ i, a (l i)) * ∏ i, nearTest (t i) (y (t i)) (l i : ℝ) ω := by
  unfold radiusEnvelope
  rw [← tsum_vector_prod]
  apply tsum_congr
  intro l
  exact Finset.prod_mul_distrib

lemma weightedEncounterMass_eq {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    weightedEncounterMass t a y =
      ∑' l : Fin n → ℕ, (∏ i, a (l i)) * encounterMass t (fun i ↦ (l i : ℝ)) y := by
  unfold weightedEncounterMass
  simp_rw [radiusEnvelope_prod]
  rw [lintegral_tsum (fun l ↦ by fun_prop)]
  apply tsum_congr
  intro l
  exact lintegral_const_mul _ (by fun_prop)

lemma weighted_ordered_sum_bound (T n : ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    (∑' t : BoundedTimes T n, weightedEncounterMass t.val a y) ≤ (radiusActivity a)^n := by
  simp_rw [weightedEncounterMass_eq]
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∑' t : BoundedTimes T n, encounterMass t.val (fun i ↦ (l i : ℝ)) y := by
      apply tsum_congr
      intro l
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' l : Fin n → ℕ, (∏ i, a (l i)) *
        ∏ i, ENNReal.ofReal orderedEncounterConstant * radiusFactor (l i : ℝ) :=
      ENNReal.tsum_le_tsum fun l ↦ mul_le_mul' le_rfl
        (ordered_encounter_sum T n (fun i ↦ (l i : ℝ)) (fun i ↦ Nat.cast_nonneg _) y)
    _ = ∑' l : Fin n → ℕ, ∏ i,
        ENNReal.ofReal orderedEncounterConstant * (a (l i) * radiusFactor (l i : ℝ)) := by
      apply tsum_congr
      intro l
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [tsum_vector_prod (fun (_ : Fin n) k ↦
        ENNReal.ofReal orderedEncounterConstant * (a k * radiusFactor (k:ℝ)))]
      simp only [ENNReal.tsum_mul_left,radiusActivity,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin]

lemma ordered_product_bound_envelope (T : ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) :
    (∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+radiusEnvelope a u (y u) ω) ∂law) ≤
      (1-radiusActivity a)⁻¹ := by
  calc
    _ ≤ ∫⁻ ω, ∑' n, ∑' t : BoundedTimes T n,
        ∏ i, radiusEnvelope a (t.val i) (y (t.val i)) ω ∂law :=
      lintegral_mono fun ω ↦ prod_one_add_le_ordered_series T
        (fun u ↦ radiusEnvelope a u (y u) ω)
    _ = ∑' n, ∑' t : BoundedTimes T n, weightedEncounterMass t.val a y := by
      rw [lintegral_tsum (fun n ↦ (Measurable.tsum (fun t ↦ by fun_prop)).aemeasurable)]
      apply tsum_congr
      intro n
      rw [lintegral_tsum (fun t ↦ by fun_prop)]
      rfl
    _ ≤ ∑' n, (radiusActivity a)^n :=
      ENNReal.tsum_le_tsum (fun n ↦ weighted_ordered_sum_bound T n a y)
    _ = _ := ENNReal.tsum_geometric _

lemma ordered_product_bound (T : ℕ) (a : ℕ → ℝ≥0∞) (y : ℕ → Fin 2 → ℝ)
    (f : ℕ → Noise → ℝ≥0∞) (hf : ∀ n ω, f n ω ≤ radiusEnvelope a n (y n) ω) :
    (∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+f u ω) ∂law) ≤ (1-radiusActivity a)⁻¹ := by
  refine le_trans (lintegral_mono (fun ω ↦ ?_)) (ordered_product_bound_envelope T a y)
  exact Finset.prod_le_prod' (fun u _ ↦ add_le_add_right (hf u ω) 1)

lemma exp_sub_one_le_slope {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) :
    Real.exp x - 1 ≤ Real.exp B * x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have he : Real.exp x ≤ Real.exp B := Real.exp_le_exp.mpr hB
  nlinarith [mul_le_mul_of_nonneg_right he hx]

lemma radiusEnvelope_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (n : ℕ)
    (y : Fin 2 → ℝ) (ω : Noise) :
    radiusEnvelope (fun l ↦ c*a l) n y ω = c*radiusEnvelope a n y ω := by
  unfold radiusEnvelope
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  ring

lemma radiusActivity_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    radiusActivity (fun l ↦ c*a l) = c*radiusActivity a := by
  unfold radiusActivity
  simp only [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  ac_rfl

lemma ofReal_exp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (Real.exp (∑ i ∈ s, f i)) = ∏ i ∈ s, ENNReal.ofReal (Real.exp (f i)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (Real.exp_pos _).le

lemma radius_exponential_bound (T : ℕ) (a : ℕ → ℝ≥0∞) (y : ℕ → Fin 2 → ℝ)
    (U : ℕ → Noise → ℝ) (hU0 : ∀ n ω, 0 ≤ U n ω) (hU1 : ∀ n ω, U n ω ≤ 1)
    (hUa : ∀ n ω, ENNReal.ofReal (U n ω) ≤ radiusEnvelope a n (y n) ω)
    (ha : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U u ω)) ∂law) ≤ 2 := by
  let c := ENNReal.ofReal (2*Real.exp 2)
  let b := fun l ↦ c*a l
  let f := fun n ω ↦ ENNReal.ofReal (Real.exp (2*U n ω)-1)
  have hba : radiusActivity b ≤ (1/2:ℝ≥0∞) := by
    simpa only [b,radiusActivity_smul,c] using ha
  have hbf : ∀ n ω, f n ω ≤ radiusEnvelope b n (y n) ω := by
    intro n ω
    calc
      f n ω ≤ ENNReal.ofReal (2*Real.exp 2 * U n ω) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc,mul_left_comm,mul_comm] using
          exp_sub_one_le_slope (by linarith [hU0 n ω] : 0 ≤ 2*U n ω)
            (by linarith [hU1 n ω] : 2*U n ω ≤ 2)
      _ = c * ENNReal.ofReal (U n ω) := by rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ c * radiusEnvelope a n (y n) ω := mul_le_mul' le_rfl (hUa n ω)
      _ = radiusEnvelope b n (y n) ω := (radiusEnvelope_smul c a n (y n) ω).symm
  have he (n : ℕ) (ω : Noise) : 1+f n ω = ENNReal.ofReal (Real.exp (2*U n ω)) := by
    have hx : 0 ≤ Real.exp (2*U n ω)-1 := by
      have := Real.one_le_exp_iff.mpr (by linarith [hU0 n ω] : 0 ≤ 2*U n ω)
      linarith
    change 1+ENNReal.ofReal (Real.exp (2*U n ω)-1) = _
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) hx]
    congr 1
    ring
  have h := ordered_product_bound T b y f hbf
  have hh : (∫⁻ ω, ENNReal.ofReal
      (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U u ω)) ∂law) =
      ∫⁻ ω, ∏ u ∈ Finset.range (T+1), (1+f u ω) ∂law := by
    apply lintegral_congr
    intro ω
    rw [Finset.mul_sum,ofReal_exp_finset_sum]
    exact Finset.prod_congr rfl (fun u _ ↦ (he _ _).symm)
  rw [hh]
  refine h.trans ?_
  have hd : (1/2:ℝ≥0∞) ≤ 1-radiusActivity b := by
    simpa using tsub_le_tsub_left hba (1:ℝ≥0∞)
  exact (ENNReal.inv_le_inv.mpr hd).trans_eq (by norm_num)

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_NearPotential
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma transverseDistance_nonneg (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    0 ≤ transverseDistance n y ω := (abs_nonneg _).trans (le_max_left _ _)
lemma nearTest_eq_one (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise)
    (h : transverseDistance n y ω ≤ R) : nearTest n y R ω = 1 := by
  have h' := max_le_iff.mp h
  simp [nearTest,coordinateTest,h'.1,h'.2]

lemma softPotential_nonneg (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    0 ≤ softPotential B n y ω := (Real.exp_pos _).le
lemma softPotential_le_one (B : ℝ) (hB : 0 < B) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    softPotential B n y ω ≤ 1 :=
  Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by
    linarith [transverseDistance_nonneg n y ω]) hB.le)
lemma softPotential_envelope (B : ℝ) (hB : 0 < B) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    ENNReal.ofReal (softPotential B n y ω) ≤ radiusEnvelope (softWeights B) n y ω := by
  let l := ⌈transverseDistance n y ω⌉₊
  have hl : transverseDistance n y ω ≤ (l:ℝ) := Nat.le_ceil _
  have hl' : (l:ℝ) < transverseDistance n y ω+1 :=
    Nat.ceil_lt_add_one (transverseDistance_nonneg n y ω)
  refine le_trans ?_ (ENNReal.le_tsum (f := fun k : ℕ ↦
    softWeights B k * nearTest n y (k:ℝ) ω) l)
  rw [nearTest_eq_one n y (l:ℝ) ω hl,mul_one]
  change ENNReal.ofReal (Real.exp (-transverseDistance n y ω/B)) ≤
    ENNReal.ofReal (Real.exp ((1-(l:ℝ))/B))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by linarith) hB.le

lemma soft_activity_ne_top (B : ℝ) (hB : 0 < B) : radiusActivity (softWeights B) ≠ ∞ := by
  let q := Real.exp (-1/B)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hB
  have hs0 : Summable (fun l : ℕ ↦ q^l) := summable_geometric_of_norm_lt_one hq
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  have hs : Summable (fun l : ℕ ↦ Real.exp ((1-(l:ℝ))/B)*(1+(l:ℝ))^2) := by
    have h := ((hs2.add (hs1.mul_left 2)).add hs0).mul_left (Real.exp (1/B))
    apply h.congr
    intro l
    have he : Real.exp ((1-(l:ℝ))/B) = Real.exp (1/B) * q^l := by
      rw [show (1-(l:ℝ))/B = 1/B + (l:ℝ)*(-1/B) by ring,Real.exp_add,Real.exp_nat_mul]
    rw [he]
    simp only [pow_one]
    ring
  have he : (∑' l : ℕ, softWeights B l * radiusFactor (l:ℝ)) =
      ENNReal.ofReal (∑' l : ℕ, Real.exp ((1-(l:ℝ))/B)*(1+(l:ℝ))^2) := by
    simp only [softWeights,radiusFactor,← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun l ↦ by positivity) hs).symm
  unfold radiusActivity
  rw [he]
  finiteness

lemma same_time_soft_moment (B : ℝ) (hB : 0 < B) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ (T : ℕ) (y : ℕ → Fin 2 → ℝ),
    (∫⁻ ω, ENNReal.ofReal (Real.exp (ξ *
      ∑ u ∈ Finset.range (T+1), softPotential B u (y u) ω)) ∂law) ≤ 2 := by
  let A := (radiusActivity (softWeights B)).toReal
  let δ := (4*Real.exp 2*(1+A))⁻¹
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hAc : ENNReal.ofReal A = radiusActivity (softWeights B) :=
    ENNReal.ofReal_toReal (soft_activity_ne_top B hB)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    have he : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith
  refine ⟨2*δ,by positivity,?_⟩
  intro T y
  let a := fun l ↦ ENNReal.ofReal δ * softWeights B l
  have hsmall : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞) := by
    rw [show radiusActivity a = ENNReal.ofReal δ * radiusActivity (softWeights B) from
      radiusActivity_smul _ _,← hAc,← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.exp 2)]
    calc
      _ ≤ ENNReal.ofReal (1/2:ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [δ]
        have he := Real.exp_pos 2
        field_simp
        nlinarith
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]
  have h := radius_exponential_bound T a y
    (fun n ω ↦ δ * softPotential B n (y n) ω)
    (fun n ω ↦ mul_nonneg hd.le (softPotential_nonneg B n (y n) ω))
    (fun n ω ↦ (mul_le_mul_of_nonneg_left (softPotential_le_one B hB n (y n) ω) hd.le).trans
      (by simpa using hd1))
    (by
      intro n ω
      rw [ENNReal.ofReal_mul hd.le]
      exact (mul_le_mul_right (softPotential_envelope B hB n (y n) ω) (ENNReal.ofReal δ)).trans_eq
        (radiusEnvelope_smul _ _ n (y n) ω).symm) hsmall
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro ω
  congr 2
  rw [← Finset.mul_sum]
  ring

lemma two_copy_soft_moment (B : ℝ) (hB : 0 < B) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ T : ℕ,
    (∫⁻ z, ENNReal.ofReal (Real.exp (ξ *
      ∑ u ∈ Finset.range (T+1), Real.exp (-twoCopyDistance u z / B)))
      ∂law.prod law) ≤ 2 := by
  obtain ⟨ξ,hξ,h⟩ := same_time_soft_moment B hB
  refine ⟨ξ,hξ,fun T ↦ ?_⟩
  rw [lintegral_prod_symm _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : Noise, (2:ℝ≥0∞) ∂law := lintegral_mono (fun ω ↦
      h T (fun u j ↦ position ω j u))
    _ = 2 := by simp

lemma position_lipschitz (ω : Noise) (j : Fin 2) (s t : ℕ) :
    |position ω j s-position ω j t| ≤ |(s:ℝ)-t|/2 := by
  have hinc (a k : ℕ) : |position ω j (a+k)-position ω j a| ≤ (k:ℝ)/2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, position_succ]
      calc
        _ = |(position ω j (a+k)-position ω j a)+velocity ω j (a+k)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ (k:ℝ)/2+1/2 := add_le_add ih (velocity_abs_le ω j (a+k))
        _ = _ := by push_cast; ring
  rcases le_total t s with h | h
  · have hs : 0 ≤ (s:ℝ)-t := sub_nonneg.mpr (by exact_mod_cast h)
    rw [abs_of_nonneg hs]
    simpa only [Nat.add_sub_of_le h,Nat.cast_sub h] using hinc t (s-t)
  · have hs : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (by exact_mod_cast h)
    rw [abs_sub_comm (s:ℝ),abs_of_nonneg hs,abs_sub_comm (position ω j s)]
    simpa only [Nat.add_sub_of_le h,Nat.cast_sub h] using hinc s (t-s)

lemma position_abs_le (ω : Noise) (j : Fin 2) (t : ℕ) :
    |position ω j t| ≤ (t:ℝ)/2 := by
  simpa [position,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) t)] using position_lipschitz ω j t 0

lemma fold_time_lipschitz (n s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) :
    |((min s (n-s):ℕ):ℝ)-((min t (n-t):ℕ):ℝ)| ≤ |(s:ℝ)-t| := by
  have h := abs_min_sub_min_le_max (s:ℝ) ((n:ℝ)-s) (t:ℝ) ((n:ℝ)-t)
  have he : |((n:ℝ)-s)-((n:ℝ)-t)| = |(s:ℝ)-t| := by
    rw [sub_sub_sub_cancel_left,abs_sub_comm]
  simpa only [Nat.cast_min,Nat.cast_sub hs,Nat.cast_sub ht,he,max_self] using h

lemma drift_rate_le (n : ℕ) (hn : 0 < n) (d : ℤ) (hd : |d| ≤ n) :
    |(d:ℝ)/(n:ℝ)| ≤ 1 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hn',div_le_one hn']
  exact_mod_cast hd

lemma baseTrans_lipschitz (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) (j : Fin 2) :
    |baseTrans n d ω s j-baseTrans n d ω t j| ≤ (3/2)*|(s:ℝ)-t| := by
  have hp := (position_lipschitz ω j (min s (n-s)) (min t (n-t))).trans
    (div_le_div_of_nonneg_right (fold_time_lipschitz n s t hs ht) (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ = |((s:ℝ)-t)*((d j:ℝ)/(n:ℝ))+
        (position ω j (min s (n-s))-position ω j (min t (n-t)))| := by
      unfold baseTrans; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ |(s:ℝ)-t| + |(s:ℝ)-t|/2 := add_le_add (by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (drift_rate_le n hn (d j) (hd j))
        (abs_nonneg _)).trans_eq (mul_one _)) hp
    _ = _ := by ring

lemma floor_abs_sub_le_two (x y : ℝ) (h : |x-y| ≤ 3/2) :
    |⌊x⌋-⌊y⌋| ≤ (2:ℤ) := by
  have hf := Int.floor_le x
  have hg := Int.lt_floor_add_one y
  have hf' := Int.floor_le y
  have hg' := Int.lt_floor_add_one x
  obtain ⟨hl,hu⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · by_contra hn
    have h' : ⌊y⌋-⌊x⌋ ≥ (3:ℤ) := by omega
    have hh : (3:ℝ) ≤ (⌊y⌋:ℝ)-(⌊x⌋:ℝ) := by exact_mod_cast h'
    linarith
  · by_contra hn
    have h' : ⌊x⌋-⌊y⌋ ≥ (3:ℤ) := by omega
    have hh : (3:ℝ) ≤ (⌊x⌋:ℝ)-(⌊y⌋:ℝ) := by exact_mod_cast h'
    linarith

lemma baseVertex_step (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (t : ℕ) (ht : t < n) (j : Fin 3) :
    |baseVertex n d ω (t+1) j-baseVertex n d ω t j| ≤ 2 := by
  have hh (i : Fin 2) : |⌊baseTrans n d ω (t+1) i⌋-⌊baseTrans n d ω t i⌋| ≤ (2:ℤ) := by
    apply floor_abs_sub_le_two
    have h := baseTrans_lipschitz n hn d hd ω (t+1) t (by omega) (by omega) i
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,abs_one,mul_one] using h
  fin_cases j
  · norm_num [baseVertex]
  · exact hh 0
  · exact hh 1

lemma axisSteps_between (a b c : ℤ) (hc : c ∈ axisSteps a b) :
    min a b ≤ c ∧ c ≤ max a b := by
  unfold axisSteps at hc
  split_ifs at hc with h
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    simp only [min_eq_left h,max_eq_right h]
    omega
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    simp only [min_eq_right (by omega : b ≤ a),max_eq_left (by omega : b ≤ a)]
    omega

lemma axisSteps_near_final (a b c : ℤ) (hc : c ∈ axisSteps a b) :
    |c-b| ≤ |a-b| := by
  obtain ⟨hl,hu⟩ := axisSteps_between a b c hc
  rcases le_total a b with h|h
  · rw [min_eq_left h] at hl
    rw [max_eq_right h] at hu
    rw [abs_of_nonpos (by omega : a-b ≤ 0),abs_of_nonpos (by omega : c-b ≤ 0)]
    omega
  · rw [min_eq_right h] at hl
    rw [max_eq_left h] at hu
    rw [abs_of_nonneg (by omega : 0 ≤ a-b),abs_of_nonneg (by omega : 0 ≤ c-b)]
    omega

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_LevelList
attribute [-instance] _root_.OAI.HardSphere.DyadicSkeleton.finsetVertexDiscreteMeasurableSpace _root_.OAI.HardSphere.DyadicSkeleton.finsetVertexMeasurableSpace _root_.OAI.HardSphere.DyadicSkeleton.instCountableConnectedSkeleton _root_.OAI.HardSphere.DyadicSkeleton.instDiscreteMeasurableSpaceConnectedSkeleton _root_.OAI.HardSphere.DyadicSkeleton.instMeasurableSpaceConnectedSkeleton _root_.OAI.HardSphere.DyadicSkeleton.listVertexDiscreteMeasurableSpace _root_.OAI.HardSphere.DyadicSkeleton.listVertexMeasurableSpace _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma refineStep_mem (a b x : Vertex) (hx : x ∈ refineStep a b) :
    x 0 = b 0 ∧ ∀j, |x j-b j| ≤ |a j-b j| := by
  simp only [refineStep,List.mem_append,List.mem_singleton,List.mem_map] at hx
  rcases hx with (rfl|⟨c,hc,rfl⟩)|⟨c,hc,rfl⟩
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j <;> simp
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j
    · simp
    · exact axisSteps_near_final _ _ _ hc
    · simp
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j
    · simp
    · simp
    · exact axisSteps_near_final _ _ _ hc

lemma levelList_mem (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (t : ℕ) (ht : t ≤ n)
    (x : Vertex) (hx : x ∈ levelList n d ω t) :
    x 0 = (t:ℤ) ∧ ∀j, |x j-baseVertex n d ω t j| ≤ 2 := by
  cases t with
  | zero =>
    have he : x = baseVertex n d ω 0 := by simpa only [levelList,List.mem_singleton] using hx
    subst x
    simp [baseVertex]
  | succ t =>
    obtain ⟨h0,hb⟩ := refineStep_mem _ _ x hx
    refine ⟨h0,fun j ↦ (hb j).trans ?_⟩
    rw [abs_sub_comm]
    exact baseVertex_step n hn d hd ω t (by omega) j

lemma integer_step_lipschitz (f : ℕ → ℤ) (H : ℕ) (L : ℤ)
    (hstep : ∀ i<H, |f (i+1)-f i|≤L) {i j : ℕ} (hi : i≤H) (hj : j≤H) :
    |f i-f j|≤L*|(i:ℤ)-j| := by
  have hforward : ∀ a b, a≤b → b≤H → |f b-f a|≤L*((b:ℤ)-a) := by
    intro a b hab hb
    induction b,hab using Nat.le_induction with
    | base => simp
    | @succ b hab ih =>
      have h := hstep b (by omega)
      have hh := ih (by omega)
      calc
        |f (b+1)-f a| ≤ |f (b+1)-f b|+|f b-f a| := abs_sub_le _ _ _
        _ ≤ L+L*((b:ℤ)-a) := add_le_add h hh
        _ = _ := by push_cast; ring
  rcases le_total i j with h|h
  · rw [abs_sub_comm (f i),abs_sub_comm (i:ℤ),abs_of_nonneg (by omega : 0≤(j:ℤ)-i)]
    exact hforward i j h hj
  · rw [abs_of_nonneg (by omega : 0≤(i:ℤ)-j)]
    exact hforward j i h hi

lemma baseVertex_lipschitz (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) (j : Fin 3) :
    |baseVertex n d ω s j-baseVertex n d ω t j| ≤ 2*|(s:ℤ)-t| :=
  integer_step_lipschitz (fun u ↦ baseVertex n d ω u j) n 2
    (fun k hk ↦ baseVertex_step n hn d hd ω k hk j) hs ht

lemma real_sub_floor_le (x y : ℝ) : |x-y| ≤ |(⌊x⌋:ℝ)-(⌊y⌋:ℝ)|+1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hl := neg_abs_le ((⌊x⌋:ℝ)-(⌊y⌋:ℝ))
  have hu := le_abs_self ((⌊x⌋:ℝ)-(⌊y⌋:ℝ))
  apply abs_le.mpr
  constructor <;> linarith

lemma floor_sub_real_le (x y : ℝ) : |(⌊x⌋:ℝ)-(⌊y⌋:ℝ)| ≤ |x-y|+1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hl := neg_abs_le (x-y)
  have hu := le_abs_self (x-y)
  apply abs_le.mpr
  constructor <;> linarith

lemma same_time_position_bound (n t : ℕ) (ht : t ≤ n) (ω ω' : Noise) (j : Fin 2) :
    |position ω j (min t (n-t))-position ω' j (min t (n-t))| ≤ (n:ℝ)/2 := by
  have hu : 2*(min t (n-t)) ≤ n := by omega
  have hu' : 2*((min t (n-t):ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hu
  calc
    _ ≤ |position ω j (min t (n-t))|+|position ω' j (min t (n-t))| := abs_sub _ _
    _ ≤ ((min t (n-t):ℕ):ℝ)/2+((min t (n-t):ℕ):ℝ)/2 :=
      add_le_add (position_abs_le ω j _) (position_abs_le ω' j _)
    _ ≤ _ := by linarith

lemma same_time_floor_bound (n t : ℕ) (ht : t ≤ n) (d : Fin 2 → ℤ)
    (ω ω' : Noise) (j : Fin 3) :
    |(baseVertex n d ω t j:ℝ)-(baseVertex n d ω' t j:ℝ)| ≤ (n:ℝ)/2+1 := by
  have hh (i : Fin 2) : |(⌊baseTrans n d ω t i⌋:ℝ)-(⌊baseTrans n d ω' t i⌋:ℝ)| ≤
      (n:ℝ)/2+1 := by
    have h := floor_sub_real_le (baseTrans n d ω t i) (baseTrans n d ω' t i)
    have he : baseTrans n d ω t i-baseTrans n d ω' t i =
        position ω i (min t (n-t))-position ω' i (min t (n-t)) := by unfold baseTrans; ring
    rw [he] at h
    exact h.trans (add_le_add (same_time_position_bound n t ht ω ω' i) le_rfl)
  fin_cases j
  · change |(t:ℝ)-(t:ℝ)| ≤ _
    rw [sub_self,abs_zero]
    positivity
  · exact hh 0
  · exact hh 1

lemma periodicDistance_le (K : ℕ) (x y : Vertex) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀j, |(x j:ℝ)-(y j:ℝ)| ≤ r) : periodicDistance K x y ≤ r := by
  apply (dist_pi_le_iff hr).mpr
  intro j
  change dist ((x j:ℝ):AddCircle (K:ℝ)) ((y j:ℝ):AddCircle (K:ℝ)) ≤ r
  rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm.trans (by simpa only [Real.norm_eq_abs] using h j)

lemma periodicDistance_coord (K : ℕ) (hK : 0 < K) (x y : Vertex) (j : Fin 3)
    (h : |(x j:ℝ)-(y j:ℝ)| ≤ (K:ℝ)/2) :
    |(x j:ℝ)-(y j:ℝ)| ≤ periodicDistance K x y := by
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  have he : dist ((x j:ℝ):AddCircle (K:ℝ)) ((y j:ℝ):AddCircle (K:ℝ)) =
      |(x j:ℝ)-(y j:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
    exact (AddCircle.norm_coe_eq_abs_iff (K:ℝ) (ne_of_gt hK')).mpr
      (by simpa only [abs_of_pos hK'] using h)
  rw [← he]
  exact dist_le_pi_dist (periodicProjection K x) (periodicProjection K y) j

lemma same_time_deviation_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (ω ω' : Noise) (t : ℕ) (ht : t ≤ n) :
    twoCopyDistance (min t (n-t)) (ω,ω') ≤
      periodicDistance K (baseVertex n d ω t) (baseVertex n d ω' t)+1 := by
  have hK : 0 < K := by omega
  have htrans (i : Fin 2) (j : Fin 3)
      (he : baseVertex n d ω t j = ⌊baseTrans n d ω t i⌋)
      (he' : baseVertex n d ω' t j = ⌊baseTrans n d ω' t i⌋) :
      |position ω i (min t (n-t))-position ω' i (min t (n-t))| ≤
        periodicDistance K (baseVertex n d ω t) (baseVertex n d ω' t)+1 := by
    have hp := periodicDistance_coord K hK (baseVertex n d ω t) (baseVertex n d ω' t) j
      ((same_time_floor_bound n t ht d ω ω' j).trans (by
        have hnr : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        have hkr : 8*(n:ℝ) ≤ (K:ℝ) := by exact_mod_cast hnK
        linarith))
    rw [he,he'] at hp
    have hh := real_sub_floor_le (baseTrans n d ω t i) (baseTrans n d ω' t i)
    have heq : baseTrans n d ω t i-baseTrans n d ω' t i =
        position ω i (min t (n-t))-position ω' i (min t (n-t)) := by unfold baseTrans; ring
    rw [heq] at hh
    exact hh.trans (add_le_add hp le_rfl)
  exact max_le (htrans 0 1 rfl rfl) (htrans 1 2 rfl rfl)

lemma foldIndex_value (n : ℕ) (j : Fin (n+1)) :
    (foldIndex n j).1.val = min j.val (n-j.val) := by
  unfold foldIndex
  split_ifs with h <;> simp only
  · omega
  · omega

lemma foldIndex_injective (n : ℕ) : Function.Injective (foldIndex n) := by
  intro i j h
  have h₁ := congrArg (fun x : Fin (n/2+1) × Bool ↦ x.1.val) h
  have h₂ := congrArg Prod.snd h
  unfold foldIndex at h₁ h₂
  split_ifs at h₁ h₂ <;> simp_all only
  all_goals apply Fin.ext; omega

lemma folded_sum_le (n : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range (n+1), f (min j (n-j))) ≤
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
  let g : Fin (n/2+1) × Bool → ℝ := fun x ↦ f x.1.val
  have hs : (∑ x ∈ Finset.univ.image (foldIndex n), g x) ≤ ∑ x, g x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ ↦ hf _)
  rw [Finset.sum_image (fun i _ j _ hij ↦ foldIndex_injective n hij)] at hs
  have hleft : (∑ i : Fin (n+1), g (foldIndex n i)) =
      ∑ j ∈ Finset.range (n+1), f (min j (n-j)) := by
    simp only [g, foldIndex_value]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ f (min j (n-j))) (n+1)
  have hright : (∑ x : Fin (n/2+1) × Bool, g x) =
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, g, ← two_mul, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range]
  simpa only [hleft, hright] using hs

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_LiftedSkeleton
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma connectedDetour_spec {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    ∀ x∈(connectedDetour hK R B v w hB Γ).val.support, x∉B ∧
      (x∈Γ.val.image (torusProjection K) ∨ shellAttachment R B (Γ.val.image (torusProjection K)) x) := by
  intro x hx
  exact ⟨(Classical.choose (exists_connected_detour hK R B v w hB Γ)).property.2 x hx,
    Classical.choose_spec (exists_connected_detour hK R B v w hB Γ) x hx⟩

lemma dyadicDetour_spec {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω : Noise) :
    ∀ x∈(dyadicDetour hK R hn d v B hB ω).val.support, x∉B ∧
      (x∈(liftedSkeleton n d v ω).image (torusProjection K) ∨
        shellAttachment R B ((liftedSkeleton n d v ω).image (torusProjection K)) x) :=
  connectedDetour_spec hK R B v _ hB _

lemma nominalBase_first (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) (i : Fin (n+1)) :
    nominalBase n d v ω i 0 = v 0+i.val := by rfl

lemma nominalBase_speed (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (ω : Noise) (i j : Fin (n+1)) (k : Fin 3) :
    |nominalBase n d v ω i k-nominalBase n d v ω j k|≤3*|(i.val:ℤ)-j.val| := by
  simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
  have h := baseVertex_lipschitz n hn d hd ω i.val j.val (by omega) (by omega) k
  have hp := abs_nonneg ((i.val:ℤ)-j.val)
  omega

lemma projectedSkeleton_cover (K n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j|≤n) (v : Vertex) (ω : Noise) :
    ∀ x∈projectedSkeleton K n d v ω,
      ∃ i, torusNear K 3 (torusProjection K (nominalBase n d v ω i)) x := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z,hz,rfl⟩ := (liftedSkeleton_mem _ _ _ _).mp hy
  obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
  have ht' : t≤n := by have := List.mem_range.mp ht; omega
  refine ⟨⟨t,by omega⟩,projection_near (fun j ↦ ?_)⟩
  simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
  rw [abs_sub_comm]
  exact (levelList_mem n hn d hd ω t ht' z hz).2 j |>.trans (by norm_num)

lemma nominalBase_near_deviation {K n r : ℕ} (hn : 0<n) (hnK : 8*n≤K)
    (d : Fin 2 → ℤ) (v : Vertex) (ω ω' : Noise) (i : Fin (n+1))
    (hnear : torusNear K r (torusProjection K (nominalBase n d v ω i))
      (torusProjection K (nominalBase n d v ω' i))) :
    twoCopyDistance (min i.val (n-i.val)) (ω,ω') ≤ (r:ℝ)+1 := by
  have hsmall (j : Fin 3) : 2*|nominalBase n d v ω i j-nominalBase n d v ω' i j|≤(K:ℤ) := by
    have h := same_time_floor_bound n i.val (by omega) d ω ω' j
    have hn' : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    have hK' : 8*(n:ℝ)≤(K:ℝ) := by exact_mod_cast hnK
    simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
    have hh : 2*|(baseVertex n d ω i.val j:ℝ)-(baseVertex n d ω' i.val j:ℝ)|≤(K:ℝ) := by linarith
    exact_mod_cast hh
  have hb := (torusNear_least_iff _ _ hsmall).mp hnear
  have hdist : periodicDistance K (baseVertex n d ω i.val) (baseVertex n d ω' i.val)≤(r:ℝ) := by
    apply periodicDistance_le _ _ _ _ (by positivity)
    intro j
    have h := hb j
    simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub] at h
    exact_mod_cast h
  exact (same_time_deviation_le K n hn hnK d ω ω' i.val (by omega)).trans (by linarith)

lemma dyadicDetour_charge {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω ω' : Noise) :
    (simpleEncounter R (dyadicDetour hK R hn d v B hB ω)
      (dyadicDetour hK R hn d v B hB ω'):ℝ) ≤
    ((encounterSet (torusNear K R) (projectedSkeleton K n d v ω)
      (projectedSkeleton K n d v ω')).card:ℝ)+
      (encounterConstant R:ℝ)*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
        if torusContact (R+2) F (projectedSkeleton K n d v ω) ∧
          torusContact (R+2) F (projectedSkeleton K n d v ω') then (F.card:ℝ) else 0 := by
  let u := dyadicDetour hK R hn d v B hB ω
  let u' := dyadicDetour hK R hn d v B hB ω'
  have h := torus_detour_charge R B (projectedSkeleton K n d v ω) (projectedSkeleton K n d v ω')
    u.val.support.toFinset u'.val.support.toFinset
    (fun x hx ↦ dyadicDetour_spec hK R hn d v B hB ω x (List.mem_toFinset.mp hx))
    (fun x hx ↦ dyadicDetour_spec hK R hn d v B hB ω' x (List.mem_toFinset.mp hx))
  have h' := h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (encounterConstant_detour R)) _)
  have hr := (Nat.cast_le (α:=ℝ)).mpr h'
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Finset.sum_filter,Nat.cast_ite,
    Nat.cast_zero,simpleEncounter,u,u'] using hr

lemma geometric_term_soft {B δ q : ℝ} (hB : 0<B) (hq : 0≤q)
    (hqsmall : q*Real.exp 1≤1/2) (m : ℕ) (hδ : δ≤B*((m+1:ℕ):ℝ)) :
    q^(m+1) ≤ (q*Real.exp 1*Real.exp (-δ/B))*(1/2:ℝ)^m := by
  have he : Real.exp (-((m+1:ℕ):ℝ))≤Real.exp (-δ/B) := by
    apply Real.exp_le_exp.mpr
    have h : δ/B≤((m+1:ℕ):ℝ) := (div_le_iff₀ hB).mpr (by simpa [mul_comm] using hδ)
    simpa only [neg_div] using neg_le_neg h
  have hcancel : Real.exp (-((m+1:ℕ):ℝ))*Real.exp (((m+1:ℕ):ℝ)) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    q^(m+1) = q^(m+1)*(Real.exp (-((m+1:ℕ):ℝ))*Real.exp (((m+1:ℕ):ℝ))) := by rw [hcancel,mul_one]
    _ ≤ q^(m+1)*(Real.exp (-δ/B)*Real.exp (((m+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) (pow_nonneg hq _)
    _ = (q*Real.exp 1*Real.exp (-δ/B))*(q*Real.exp 1)^m := by
      have hm : Real.exp (m:ℝ)=(Real.exp 1)^m := by rw [← Real.exp_nat_mul,mul_one]
      rw [Nat.cast_add,Nat.cast_one,Real.exp_add,hm,mul_pow,pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hq (Real.exp_pos _).le) hqsmall m)
      (by positivity)

lemma geometric_soft_sum {B δ q : ℝ} (hB : 0<B) (hq : 0≤q)
    (hqsmall : q*Real.exp 1≤1/2) (r : ℕ → ℝ) (hr : ∀m, r m≤B*((m+1:ℕ):ℝ)) :
    (∑' m : ℕ, if δ ≤ r m then (ENNReal.ofReal q)^(m+1) else 0)≤
      ENNReal.ofReal (2*q*Real.exp 1*Real.exp (-δ/B)) := by
  calc
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (q*Real.exp 1*Real.exp (-δ/B))*(1/2:ℝ≥0∞)^m := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h
      · have hb := ENNReal.ofReal_le_ofReal (geometric_term_soft hB hq hqsmall m (h.trans (hr m)))
        simpa only [ENNReal.ofReal_mul (by positivity : 0≤q*Real.exp 1*Real.exp (-δ/B)),
          ENNReal.ofReal_pow hq,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hb
      · exact zero_le
    _ = ENNReal.ofReal (q*Real.exp 1*Real.exp (-δ/B))*2 := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      norm_num
    _ = _ := by rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma exp_soft_dominates_one {B δ : ℝ} (hB : 0<B) (hδ : δ≤B) :
    1≤Real.exp 1*Real.exp (-δ/B) := by
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have h := (div_le_one hB).mpr hδ
  rw [neg_div]; linarith

lemma dyadicRadius_pos (R : ℕ) : 0<dyadicRadius R := by unfold dyadicRadius; omega

lemma dyadic_nominal_potential {K n : ℕ} [NeZero K] (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (ω ω' : Noise) (κ t : ℝ) (hκ : 0≤κ) (ht : 0≤t)
    (hq : ((candidateConstant (R+2):ℝ)*t)*Real.exp 1≤1/2) :
    κ*((encounterSet (torusNear K R) (projectedSkeleton K n d v ω)
      (projectedSkeleton K n d v ω')).card:ℝ)+
      (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F (projectedSkeleton K n d v ω) ∧
          torusContact (R+2) F (projectedSkeleton K n d v ω') then t^F.card else 0) ≤
    Real.exp 1*((encounterConstant R:ℝ)*κ+2*((candidateConstant (R+2):ℝ)*t))*
      ∑ j∈Finset.range (n+1), Real.exp
        (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ)) := by
  let U := nominalBase n d v ω
  let U' := nominalBase n d v ω'
  let Γ := projectedSkeleton K n d v ω
  let Γ' := projectedSkeleton K n d v ω'
  let A := candidateConstant (R+2)
  let b : ℝ := dyadicRadius R
  let δ (i : Fin (n+1)) := twoCopyDistance (min i.val (n-i.val)) (ω,ω')
  let f (i : Fin (n+1)) := Real.exp (-δ i/b)
  have hb : 0<b := by dsimp [b]; exact_mod_cast dyadicRadius_pos R
  have hfirst := nominalBase_first n d v ω
  have hfirst' := nominalBase_first n d v ω'
  have hspeed := nominalBase_speed n hn d hd v ω'
  have hcover := projectedSkeleton_cover K n hn d hd v ω
  have hcover' := projectedSkeleton_cover K n hn d hd v ω'
  have hnear (r : ℕ) (i : Fin (n+1)) : torusNear K r (torusProjection K (U i))
      (torusProjection K (U' i)) → δ i≤(r:ℝ)+1 :=
    nominalBase_near_deviation hn hnK d v ω ω' i
  have hN := nominal_encounter_bound R (by omega : 2*n≤K) U U' (v 0)
    hfirst hfirst' hspeed Γ Γ' hcover hcover'
  have hcard : ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ) ≤ Real.exp 1*∑ i, f i := by
    have he : ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ)=
        ∑ i : Fin (n+1), if torusNear K (4*(R+6)) (torusProjection K (U i))
          (torusProjection K (U' i)) then (1:ℝ) else 0 := by
      rw [← Finset.sum_filter]; simp
    rw [he,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · apply exp_soft_dominates_one hb
      exact (hnear _ i hi).trans (by
        dsimp [b]
        exact_mod_cast (show 4*(R+6)+1≤dyadicRadius R by unfold dyadicRadius; omega))
    · exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hNr : κ*((encounterSet (torusNear K R) Γ Γ').card:ℝ)≤
      ((encounterConstant R:ℝ)*κ)*Real.exp 1*∑ i,f i := by
    have hh : ((encounterSet (torusNear K R) Γ Γ').card:ℝ)≤(encounterConstant R:ℝ)*
      ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ) := by exact_mod_cast hN
    have hc := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg (encounterConstant R) : (0:ℝ)≤_)
    have hh' := mul_le_mul_of_nonneg_left (hh.trans hc) hκ
    nlinarith [hh']
  have hF := contact_candidate_potential (R+2) (by omega : 2*n≤K) U U' (v 0)
    hfirst hfirst' hspeed Γ Γ' hcover hcover' (ENNReal.ofReal t)
  have hFe : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
      if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)≤
      ∑ i : Fin (n+1), ENNReal.ofReal (2*((A:ℝ)*t)*Real.exp 1*f i) := by
    have hcast : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)=
        ∑ F∈candidateSets (torusRangeGraph K (R+2)),
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (ENNReal.ofReal t)^F.card else 0 := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intro F _; split_ifs <;> positivity)]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp [ENNReal.ofReal_pow ht]
    rw [hcast]
    refine hF.trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine le_trans (ENNReal.tsum_le_tsum (fun m ↦ ?_))
      (geometric_soft_sum hb (mul_nonneg (Nat.cast_nonneg A) ht) hq
        (fun m ↦ (((12*(R+2)+24)*(m+1):ℕ):ℝ)+1) (fun m ↦ ?_))
    · by_cases h : torusNear K ((12*(R+2)+24)*(m+1))
          (torusProjection K (U i)) (torusProjection K (U' i))
      · rw [ite_eq_left h,ite_eq_left (hnear _ i h)]
        apply pow_le_pow_left'
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg A),ENNReal.ofReal_natCast]
        exact mul_le_mul' (by exact_mod_cast candidateConstant_growth (R+2)) le_rfl
      · rw [ite_eq_right h]; exact zero_le
    · have ha := candidateConstant_radius (R+2)
      have ha' : (12*(R+2)+24)*(m+1)+1≤dyadicRadius R*(m+1) := by
        dsimp [dyadicRadius]
        nlinarith
      dsimp [b]; exact_mod_cast ha'
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro i _; dsimp [f]; positivity)] at hFe
  have hFr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hFe
  rw [← Finset.mul_sum] at hFr
  have hbound := add_le_add hNr hFr
  have heq : (∑ i : Fin (n+1),f i)=∑ j∈Finset.range (n+1), Real.exp
      (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ)) := by
    exact Fin.sum_univ_eq_sum_range
      (fun j ↦ Real.exp (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ))) (n+1)
  rw [heq] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by dsimp [A]; ring

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_AcceptedIntegrand
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma measurable_simpleEncounter {K : ℕ} [NeZero K] (R : ℕ)
    (x y : DiscreteTorus K) :
    Measurable (fun p : SimplePath x y × SimplePath x y ↦ simpleEncounter R p.1 p.2) :=
  measurable_of_countable _

lemma measurable_simpleEncounter_comp {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} [NeZero K] (R : ℕ) {x y : DiscreteTorus K}
    (f : Ω → SimplePath x y) (hf : Measurable f) :
    Measurable (fun z : Ω×Ω ↦ simpleEncounter (K:=K) R (x:=x) (y:=y) (f z.1) (f z.2)) :=
  by
    have hf1 : Measurable (fun z : Ω×Ω ↦ f z.1) := hf.comp measurable_fst
    have hf2 : Measurable (fun z : Ω×Ω ↦ f z.2) := hf.comp measurable_snd
    have hpair : Measurable (fun z : Ω×Ω ↦ (f z.1,f z.2)) := hf1.prodMk hf2
    exact Measurable.comp
      (g:=fun p : SimplePath x y × SimplePath x y ↦ simpleEncounter (K:=K) R p.1 p.2)
      (f:=fun z : Ω×Ω ↦ (f z.1,f z.2))
      (measurable_simpleEncounter (K:=K) R x y) hpair

@[fun_prop] lemma measurable_dyadicEncounter {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    Measurable (fun z : Noise×Noise ↦ simpleEncounter R
      (dyadicDetour hK R hn d v B hB z.1) (dyadicDetour hK R hn d v B hB z.2)) := by
  exact measurable_simpleEncounter_comp R (dyadicDetour hK R hn d v B hB)
    (measurable_dyadicDetour hK R hn d v B hB)

@[fun_prop] lemma measurable_acceptedIntegrand {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K)) :
    Measurable (acceptedIntegrand hK R hn d v κ B) := by
  unfold acceptedIntegrand
  split_ifs <;> fun_prop

lemma dyadic_environment_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (μ : PMF (Finset (DiscreteTorus K))) (p κ : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (hq : ((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))*Real.exp 1≤1/2)
    (z : Noise×Noise) :
    (∑' B, μ B*acceptedIntegrand hK R hn d v κ B z)≤
      ENNReal.ofReal (Real.exp (Real.exp 1*((encounterConstant R:ℝ)*κ+
        2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ)))))*
          ∑ j∈Finset.range (n+1), Real.exp
            (-twoCopyDistance (min j (n-j)) z/(dyadicRadius R:ℝ)))) := by
  let E (B : Finset (DiscreteTorus K)) := acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])
  let J (B : Finset (DiscreteTorus K)) : ℝ := if hB : E B then
    (simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
      (dyadicDetour hK R hn d v B hB z.2):ℝ) else 0
  have he (B : Finset (DiscreteTorus K)) : acceptedIntegrand hK R hn d v κ B z=
      if E B then ENNReal.ofReal (Real.exp (κ*J B)) else 0 := by
    change (if hB : E B then ENNReal.ofReal (Real.exp (κ*
      (simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
        (dyadicDetour hK R hn d v B hB z.2):ℝ))) else 0)=_
    by_cases hB : E B
    · simp only [dite_eq_left hB,ite_eq_left hB,J]
    · simp only [dite_eq_right hB,ite_eq_right hB]
  simp_rw [he]
  refine (accepted_charge_environment_bound R μ p κ (encounterConstant R)
    ((encounterSet (torusNear K R) (projectedSkeleton K n d v z.1)
      (projectedSkeleton K n d v z.2)).card:ℝ) hp hκ hbad
    (projectedSkeleton K n d v z.1) (projectedSkeleton K n d v z.2) E J ?_).trans ?_
  · intro B hB
    simp only [J,dite_eq_left hB]
    exact dyadicDetour_charge hK R hn d v B hB z.1 z.2
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (dyadic_nominal_potential R hn hnK d hd v z.1 z.2 κ
        (p*Real.exp (κ*(encounterConstant R:ℝ))) hκ (by positivity) hq))

lemma dyadic_annealed_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (μ : PMF (Finset (DiscreteTorus K))) (p κ ξ : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (hq : ((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))*Real.exp 1≤1/2)
    (hc : 2*(Real.exp 1*((encounterConstant R:ℝ)*κ+
      2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))))≤ξ)
    (hξ : ∀ T : ℕ, (∫⁻ z, ENNReal.ofReal (Real.exp (ξ*
      ∑ u∈Finset.range (T+1),Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ)))) ∂law.prod law)≤2) :
    (∑' B, μ B*∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law)≤2 := by
  have hme (B : Finset (DiscreteTorus K)) : Measurable (fun z ↦ μ B*acceptedIntegrand hK R hn d v κ B z) := by fun_prop
  simp_rw [← lintegral_const_mul' _ _ (PMF.apply_ne_top μ _)]
  rw [← lintegral_tsum (fun B ↦ (hme B).aemeasurable)]
  refine le_trans (lintegral_mono (fun z ↦ ?_)) (hξ (n/2))
  refine (dyadic_environment_moment hK R hn hnK d hd v μ p κ hp hκ hbad hq z).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  let c : ℝ := Real.exp 1*((encounterConstant R:ℝ)*κ+
      2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ)))))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hf := folded_sum_le n (fun u ↦ Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ)))
    (fun _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ c*(2*∑ u∈Finset.range (n/2+1),Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ))) :=
      mul_le_mul_of_nonneg_left hf hc0
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right (by simpa [mul_comm,c] using hc)
      exact Finset.sum_nonneg fun u _ ↦ (Real.exp_pos _).le

lemma small_route_parameters (C A ξ : ℝ) (hC : 0<C) (hA : 0<A) (hξ : 0<ξ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∀ p : ℝ, 0≤p → p≤p₀ →
      (A*(p*Real.exp (κ*C)))*Real.exp 1≤1/2 ∧
      2*(Real.exp 1*(C*κ+2*(A*(p*Real.exp (κ*C)))))≤ξ := by
  let e := Real.exp 1
  let s := min 1 ξ
  let κ := min 1 (s/(16*e*C))
  let p₀ := s/(16*e*A*Real.exp C)
  have he : 0<e := Real.exp_pos _
  have hs : 0 < s := lt_min (by norm_num) hξ
  have hs1 : s≤1 := min_le_left _ _
  have hsξ : s≤ξ := min_le_right _ _
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hs (by positivity))
  have hp₀ : 0<p₀ := div_pos hs (by positivity)
  have hκ1 : κ≤1 := min_le_left _ _
  have hκs : e*(C*κ)≤ s/16 := by
    have h := (le_div_iff₀ (by positivity : 0<16*e*C)).mp
      (show κ≤ s/(16*e*C) from min_le_right _ _)
    nlinarith
  refine ⟨p₀,κ,hp₀,hκ,?_⟩
  intro p hp hpp
  have hpbound := (le_div_iff₀ (by positivity : 0<16*e*A*Real.exp C)).mp hpp
  have hexp : Real.exp (κ*C)≤Real.exp C := Real.exp_le_exp.mpr (by nlinarith)
  have hqmon := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hexp hp) hA.le
  have hqe : e*(A*(p*Real.exp (κ*C)))≤ s/16 := by
    have hh := mul_le_mul_of_nonneg_left hqmon he.le
    nlinarith
  constructor
  · change _*e≤_
    nlinarith
  · change 2*(e*(C*κ+2*(A*(p*Real.exp (κ*C)))))≤ξ
    nlinarith

lemma dyadic_path_constants (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ n : ℕ, ∀ hn : 0<n, 8*n≤K → ∀ d : Fin 2 → ℤ, (∀j, |d j|≤n) →
      ∀ v : Vertex, ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ,
      0≤p → p≤p₀ → JointBadLaw μ (ENNReal.ofReal p) →
      (1/2:ℝ≥0∞)≤(∑' B, if acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) then μ B else 0) ∧
      ∃ hK : 2<K, (∑' B, μ B*∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law)≤2 := by
  obtain ⟨ξ,hξ,hsoft⟩ := two_copy_soft_moment (dyadicRadius R) (by exact_mod_cast dyadicRadius_pos R)
  obtain ⟨p₁,κ,hp₁,hκ,hparam⟩ := small_route_parameters (encounterConstant R) (candidateConstant (R+2)) ξ
    (by unfold encounterConstant; positivity) (by unfold candidateConstant; positivity) hξ
  obtain ⟨p₂,hp₂,K₀,haccept⟩ := acceptedEnvironment_mass (R+2) (by omega)
  refine ⟨min p₁ p₂,κ,lt_min hp₁ hp₂,hκ,max K₀ 3,?_⟩
  intro K hK inst n hn hnK d hd v μ p hp hpp hbad
  have hK3 : 2<K := by omega
  have hb := hparam p hp (hpp.trans (min_le_left _ _))
  exact ⟨haccept K ((le_max_left _ _).trans hK) inst μ p hp
    (hpp.trans (min_le_right _ _)) hbad v _,hK3,
    dyadic_annealed_moment hK3 R hn hnK d hd v μ p κ ξ hp hκ.le hbad hb.1 hb.2 hsoft⟩

lemma double_lintegral_map {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → X) (hf : Measurable f)
    (g : X×X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, g (x,y) ∂P.map f ∂P.map f)=
      ∫⁻ z, g (f z.1,f z.2) ∂P.prod P := by
  let : IsProbabilityMeasure (P.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  rw [← lintegral_prod g hg.aemeasurable,Measure.map_prod_map P P hf hf,
    lintegral_map hg (hf.prodMap hf)]
  rfl

lemma dyadicDetour_good_mass {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    (law.map (dyadicDetour hK R hn d v B hB)) {q | simplePathGood B q}=1 := by
  rw [Measure.map_apply (measurable_dyadicDetour hK R hn d v B hB) MeasurableSet.of_discrete]
  have he : (dyadicDetour hK R hn d v B hB) ⁻¹' {q | simplePathGood B q}=Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω x hx
    exact (dyadicDetour_spec hK R hn d v B hB ω x hx).1
  rw [he,measure_univ]

lemma dyadicDetour_double_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    (∫⁻ q, ∫⁻ q', ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ)))
      ∂law.map (dyadicDetour hK R hn d v B hB) ∂law.map (dyadicDetour hK R hn d v B hB))=
      ∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law := by
  rw [double_lintegral_map law _ (measurable_dyadicDetour hK R hn d v B hB)
    (fun p ↦ ENNReal.ofReal (Real.exp (κ*(simpleEncounter R p.1 p.2:ℝ)))) (measurable_of_countable _)]
  apply lintegral_congr
  intro z
  simp only [acceptedIntegrand,dite_eq_left hB]

theorem dyadic_good_paths_lift (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ {Ω : Type*} [MeasurableSpace Ω], ∀ P : Measure Ω, ∀ _ : IsProbabilityMeasure P,
      ∀ b : Ω → Finset (DiscreteTorus K), Measurable b →
      ∀ p : ℝ, 0≤p → p≤p₀ →
      (∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤(ENNReal.ofReal p)^A.card) →
      ∀ n : ℕ, 0<n → 8*n≤K → ∀ d : Fin 2 → ℤ, (∀j, |d j|≤n) → ∀ v : Vertex,
      ∃ E : Set Ω, MeasurableSet E ∧ (1/2:ℝ≥0∞)≤P E ∧
      ∃ ν : Kernel Ω (SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1]))),
        IsMarkovKernel ν ∧
        (∀ e∈E, ν e {q | simplePathGood (b e) q}=1) ∧
        (∫⁻ e, E.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e ∂P)≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := dyadic_path_constants R
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst Ω mΩ P hP b hb p hp hpp hbad n hn hnK d hd v
  let := (Measure.isProbabilityMeasure_map_iff (μ:=P) hb.aemeasurable).mpr inferInstance
  let μ := (P.map b).toPMF
  obtain ⟨hmass,hK2,hmoment⟩ := hall K hK inst n hn hnK d hd v μ p hp hpp
    (mapped_bad_law P b hb _ hbad)
  let E (B : Finset (DiscreteTorus K)) := acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])
  have hex : ∃ B, E B := by
    by_contra hh
    have hh' : ∀ B, ¬E B := not_exists.mp hh
    simp only [show ∀ B, ¬acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) from hh',
      ite_false,tsum_zero] at hmass
    norm_num at hmass
  obtain ⟨B₀,hB₀⟩ := hex
  let ω₀ : Noise := fun _ ↦ ⟨0,by norm_num,by norm_num⟩
  let q₀ := dyadicDetour hK2 R hn d v B₀ hB₀ ω₀
  let η (B : Finset (DiscreteTorus K)) := if hB : E B then
    law.map (dyadicDetour hK2 R hn d v B hB) else Measure.dirac q₀
  have hη (B : Finset (DiscreteTorus K)) : IsProbabilityMeasure (η B) := by
    dsimp only [η]
    split_ifs
    · exact (Measure.isProbabilityMeasure_map_iff
        (measurable_dyadicDetour hK2 R hn d v B _).aemeasurable).mpr inferInstance
    · infer_instance
  let ν₀ : Kernel (Finset (DiscreteTorus K))
      (SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1]))) :=
    ⟨η,Measurable.of_discrete⟩
  let ν := ν₀.comap b hb
  refine ⟨{e | E (b e)},hb (t := {B | E B}) MeasurableSet.of_discrete,?_,ν,?_,?_,?_⟩
  · change (1/2:ℝ≥0∞)≤P (b ⁻¹' {B | E B})
    rw [← Measure.map_apply (μ:=P) hb (s:={B | E B}) MeasurableSet.of_discrete,
      ← Measure.toPMF_toMeasure (P.map b),pmf_event_discrete]
    exact hmass
  · exact ⟨fun e ↦ hη (b e)⟩
  · intro e he
    change E (b e) at he
    change η (b e) {q | simplePathGood (b e) q}=1
    simp only [η,dite_eq_left he]
    exact dyadicDetour_good_mass hK2 R hn d v (b e) he
  · have hpoint (e : Ω) :
        {e | E (b e)}.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e =
        ∫⁻ z, acceptedIntegrand hK2 R hn d v κ (b e) z ∂law.prod law := by
      by_cases he : E (b e)
      · rw [Set.indicator_of_mem (s:={e | E (b e)}) (a:=e) he]
        change (∫⁻ q, ∫⁻ q', ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ)))
          ∂η (b e) ∂η (b e))=_
        simp only [η,dite_eq_left he]
        exact dyadicDetour_double_moment hK2 R hn d v κ (b e) he
      · rw [Set.indicator_of_notMem (s:={e | E (b e)}) (a:=e) he]
        change ¬acceptedEnvironment (R+2) (b e) v (v+![(n:ℤ),d 0,d 1]) at he
        simp only [acceptedIntegrand,dite_eq_right he,lintegral_zero]
    simp_rw [hpoint]
    rw [finite_datum_expectation P b hb
      (fun B ↦ ∫⁻ z, acceptedIntegrand hK2 R hn d v κ B z ∂law.prod law)]
    exact hmoment

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_Admissible
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma current_admissible_lift {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
    (h : currentAdmissiblePair x y) :
    ∃ n : ℕ, 0<n ∧ 8*n≤K ∧ K≤10*n ∧ ∃ v : Vertex, ∃ d : Fin 2 → ℤ,
      (∀j, |d j|≤n) ∧ torusProjection K v=x ∧
      torusProjection K (v+![(n:ℤ),d 0,d 1])=y := by
  obtain ⟨n,hl,hu,d,hd,hy⟩ := h
  let v : Vertex := fun j ↦ (x j).val
  have hK : 0<K := NeZero.pos K
  refine ⟨n,by omega,hu,hl,v,d,hd,?_,?_⟩
  · ext j; simp [torusProjection,v]
  · rw [hy]
    ext j; fin_cases j <;> simp [torusProjection,v]

lemma current_admissible_card {K : ℕ} [NeZero K] (hK : 400≤K) :
    K^6≤2000*(currentAdmissiblePairs K).card := by
  let m := K/10
  let I := Finset.Icc (K/10+1) (K/8)
  let J := Finset.range (2*m+1)
  let S : Finset (DiscreteTorus K × ℕ × ℕ × ℕ) :=
    Finset.univ ×ˢ (I ×ˢ (J ×ˢ J))
  let f : DiscreteTorus K × ℕ × ℕ × ℕ → DiscreteTorus K × DiscreteTorus K :=
    fun z ↦ (z.1,z.1+![(z.2.1:ZMod K),((z.2.2.1:ℤ)-m:ZMod K),((z.2.2.2:ℤ)-m:ZMod K)])
  have hI (n : ℕ) (hn : n∈I) : K≤10*n ∧ 8*n≤K ∧ n<K ∧ m<n := by
    have hn := Finset.mem_Icc.mp hn
    dsimp [m]
    omega
  have hJ (b : ℕ) (hb : b∈J) : b<K ∧ |(b:ℤ)-m|≤(m:ℤ) := by
    have hb := Finset.mem_range.mp hb
    dsimp [m] at *
    constructor
    · omega
    · rw [abs_le]; constructor <;> omega
  have hsub : S.image f⊆currentAdmissiblePairs K := by
    intro z hz
    obtain ⟨⟨x,n,b,c⟩,hu,rfl⟩ := Finset.mem_image.mp hz
    simp only [S,Finset.mem_product] at hu
    obtain ⟨_,hn,hb,hc⟩ := hu
    have hin := hI n hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,n,hin.1,hin.2.1,![(b:ℤ)-m,(c:ℤ)-m],?_,?_⟩
    · intro j
      fin_cases j
      · exact (hJ b hb).2.trans (by exact_mod_cast hin.2.2.2.le)
      · exact (hJ c hc).2.trans (by exact_mod_cast hin.2.2.2.le)
    · simp [f]
  have hinj : Set.InjOn f (↑S : Set _) := by
    rintro ⟨x,n,b,c⟩ hx ⟨x',n',b',c'⟩ hx' he
    have he₁ : x=x' := congrArg Prod.fst he
    subst x'
    have he₂ : ![(n:ZMod K),((b:ℤ)-m:ZMod K),((c:ℤ)-m:ZMod K)]=
        ![(n':ZMod K),((b':ℤ)-m:ZMod K),((c':ℤ)-m:ZMod K)] :=
      add_left_cancel (congrArg Prod.snd he)
    change (x,n,b,c)∈S at hx
    change (x,n',b',c')∈S at hx'
    simp only [S,Finset.mem_product] at hx hx'
    obtain ⟨_,hn,hb,hc⟩ := hx
    obtain ⟨_,hn',hb',hc'⟩ := hx'
    have hnval := congrArg (fun z : Fin 3 → ZMod K ↦ (z 0).val) he₂
    simp only [Matrix.cons_val_zero,ZMod.val_natCast_of_lt (hI n hn).2.2.1,
      ZMod.val_natCast_of_lt (hI n' hn').2.2.1] at hnval
    have hbeq : (b:ZMod K)=(b':ZMod K) := by
      have h := congrFun he₂ 1
      simpa using h
    have hceq : (c:ZMod K)=(c':ZMod K) := by
      have h := congrFun he₂ 2
      simpa using h
    have hbval := congrArg ZMod.val hbeq
    have hcval := congrArg ZMod.val hceq
    simp only [ZMod.val_natCast_of_lt (hJ b hb).1,ZMod.val_natCast_of_lt (hJ b' hb').1] at hbval
    simp only [ZMod.val_natCast_of_lt (hJ c hc).1,ZMod.val_natCast_of_lt (hJ c' hc').1] at hcval
    simp only [Prod.mk.injEq]
    exact ⟨trivial,hnval,hbval,hcval⟩
  have hcard : S.card≤(currentAdmissiblePairs K).card :=
    (Finset.card_image_iff.mpr hinj).symm.trans_le (Finset.card_le_card hsub)
  have hcardS : S.card=K^3*I.card*J.card^2 := by
    dsimp only [S]
    rw [Finset.card_product,Finset.card_product,Finset.card_product]
    simp [DiscreteTorus,mul_assoc,pow_two]
  have hcardI : K≤50*I.card := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hcardJ : K≤6*J.card := by
    simp only [J,Finset.card_range,m]
    omega
  rw [hcardS] at hcard
  calc
    K^6=K^3*K*K^2 := by ring
    _ ≤ K^3*(50*I.card)*(6*J.card)^2 := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hcardI) (Nat.pow_le_pow_left hcardJ 2)
    _ = 1800*(K^3*I.card*J.card^2) := by ring
    _ ≤ 1800*(currentAdmissiblePairs K).card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

end HardSphere.DyadicSkeleton
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice

theorem current_good_paths (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      K^6≤2000*(currentAdmissiblePairs K).card ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω], ∀ P : Measure Ω, ∀ _ : IsProbabilityMeasure P,
      ∀ b : Ω → Finset (DiscreteTorus K), Measurable b →
      ∀ p : ℝ, 0≤p → p≤p₀ →
      (∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤(ENNReal.ofReal p)^A.card) →
      ∀ x y : DiscreteTorus K, currentAdmissiblePair x y →
      ∃ E : Set Ω, MeasurableSet E ∧ (1/2:ℝ≥0∞)≤P E ∧
      ∃ ν : Kernel Ω (SimplePath x y), IsMarkovKernel ν ∧
        (∀ e∈E, ν e {q | simplePathGood (b e) q}=1) ∧
        (∫⁻ e, E.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e ∂P)≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := dyadic_good_paths_lift R
  refine ⟨p₀,κ,hp₀,hκ,max K₀ 400,?_⟩
  intro K hK inst
  refine ⟨current_admissible_card ((le_max_right K₀ 400).trans hK),?_⟩
  intro Ω mΩ P hP b hb p hp hpp hbad x y hxy
  obtain ⟨n,hn,hnK,_,v,d,hd,hv,hw⟩ := current_admissible_lift hxy
  subst x y
  exact hall K ((le_max_left K₀ 400).trans hK) inst P hP b hb p hp hpp hbad n hn hnK d hd v

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PhysicalPathComparison
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma physical_lattice_bad_joint {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (μ : Measure (PhysicalDatum N K M G L)) (p : ℝ≥0∞)
    (hb : ∀A : Finset (Fin 3→Fin K),μ {d | A⊆datumBad hL g m t r R C S u d} ≤ p^A.card)
    (A : Finset (DiscreteTorus K)) :
    μ {d | A⊆latticeDatumBad hL g m t r R C S u d} ≤ p^A.card := by
  have he : {d : PhysicalDatum N K M G L | A⊆latticeDatumBad hL g m t r R C S u d}=
      {d | A.image siteIndex⊆datumBad hL g m t r R C S u d} := by
    ext d
    constructor
    · intro hh v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_latticeDatumBad hL g m t r R C S u d w).mp (hh hw)
    · intro hh v hv
      exact (mem_latticeDatumBad hL g m t r R C S u d v).mpr
        (hh (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  rw [he]
  have hinj : Function.Injective (siteIndex : DiscreteTorus K→Fin 3→Fin K) :=
    Function.LeftInverse.injective indexSite_siteIndex
  simpa only [Finset.card_image_of_injective _ hinj] using hb (A.image siteIndex)

theorem physical_path_comparison :
    ∃p₀ κ : ℝ, 0 < p₀ ∧ 0 < κ ∧ ∃K₀ : ℕ,
    ∀K : ℕ,K₀ ≤ K → ∀_ : NeZero K,
    ∀{N M G : ℕ} {L : Length},∀hL : L.val=(K:ℝ),1 ≤ K → 50 < L.val →
    ∀{ψ : Jet (N+1) L} {r : ℝ},IsGroundVector (N+1) L r ψ →
    ∀g : Fin G,∀m : ℕ,∀t R C S s₀ h : ℝ,∀u : Time,
    PhysicalScaleBounds m t r R C S s₀ h u →
    ∀p : ℝ,0 ≤ p → p ≤ p₀ →
    (∀A : Finset (Fin 3→Fin K),
      (physicalDatumLaw (M:=M) g ψ m r R C S s₀ (2*t) u)
        {d | A⊆datumBad hL g m t r R C S u d} ≤ (ENNReal.ofReal p)^A.card) →
    0 < M → ∀δ B : ℝ,0 < δ → 1 ≤ B → routeDensityBound t ≤ ENNReal.ofReal B →
    2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ →
    ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1 →
    ∀x y : DiscreteTorus K,currentAdmissiblePair x y →
    ∃σ : Measure (Torus L×Torus L×Configuration N L),IsFiniteMeasure σ ∧
      (1/2:ℝ≥0∞) ≤ σ univ ∧
      ∀b,
        let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
        IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
          (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ 2*B := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,H⟩ := HardSphere.DyadicSkeleton.current_good_paths 30
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst N M G L hL h1 h50 ψ r hψ g m t R C S s₀ h u hs p hp hpp hbad hM δ B hδ hB hBt hk hsmall x y hxy
  have := physicalDatumLaw_probability (K:=K) (M:=M) g hψ m R C S s₀ (2*t) (by linarith [hs.time_pos]) u
  obtain ⟨E,hE,hm,ν,hi,hgood,henc⟩ := (H K hK inst).2
    (physicalDatumLaw (K:=K) (M:=M) g ψ m r R C S s₀ (2*t) u) inferInstance
    (latticeDatumBad hL g m t r R C S u) (latticeDatumBad_measurable hL g m t r R C S u)
    p hp hpp (physical_lattice_bad_joint hL g m t r R C S u _ _ hbad) x y hxy
  have := hi
  have hne : x≠y := by
    intro he
    obtain ⟨n,hl,hu,d,hd,hy⟩ := hxy
    have hz := congrArg (fun z : DiscreteTorus K ↦ z 0) hy
    rw [←he] at hz
    simp only [Pi.add_apply,Matrix.cons_val_zero] at hz
    have hn0 : (n:ZMod K)=0 := by exact add_left_cancel (hz.symm.trans (add_zero _).symm)
    have hvn := congrArg ZMod.val hn0
    simp only [ZMod.val_natCast,ZMod.val_zero] at hvn
    rw [Nat.mod_eq_of_lt (by have := NeZero.pos K; omega)] at hvn
    have := NeZero.pos K
    omega
  have hc : (∫⁻d in E,∫⁻q,∫⁻q',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 q q':ℝ))) ∂ν d ∂ν d
      ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal (2:ℝ) := by
    simpa only [lintegral_indicator hE,ENNReal.ofReal_ofNat] using henc
  obtain ⟨σ,hσ,hmass,hest⟩ := physical_group_common_comparison hL h1 h50 hψ g m t R C S s₀ h u hs
    hne E hE ν hgood hM δ B κ 2 hδ hB (by norm_num) hBt hk hsmall hc
  exact ⟨σ,hσ,hmass ▸ hm,fun b ↦ by simpa only [mul_comm B 2] using hest b⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalNumeric
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma choose_physical_group {p κ B : ℝ} (hp : 0<p) (hκ : 0<κ) (_hB : 1≤B) :
    ∃q : ℕ,0<q ∧ (2/5:ℝ)^q≤p/2 ∧
      ∃δ : ℝ,0<δ ∧ δ<1 ∧ 2*(B-1)/(2*q:ℝ)-8*Real.log δ≤κ := by
  let δ := Real.exp (-κ/32)
  have hδ : 0<δ := Real.exp_pos _
  have hδ1 : δ<1 := by dsimp only [δ]; rw [Real.exp_lt_one_iff]; linarith
  have hpow : Tendsto (fun q : ℕ ↦ (2/5:ℝ)^q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdiv : Tendsto (fun q : ℕ ↦ 2*(B-1)/(2*q:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  obtain ⟨q,hq,hpow,hdiv⟩ := Filter.Eventually.exists (
    (eventually_ge_atTop (1:ℕ)).and ((hpow.eventually (gt_mem_nhds (by positivity : (0:ℝ)<p/2))).and
      (hdiv.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))))
  refine ⟨q,by omega,hpow.le,δ,hδ,hδ1,?_⟩
  dsimp only [δ]
  rw [Real.log_exp]
  linarith

lemma physical_collision_eventually {A t C δ : ℝ} (_hA : 0<A) (ht : 0<t)
    (hC : 0≤C) (hδ : δ<1) (M : ℕ) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0<α → α≤A →
      ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*
        (routeDensityBound t*datumCollisionBound t (α/D) D⁻¹ (D^(1/12:ℝ)) C)≤1 := by
  let J : ℝ≥0∞ := (ENNReal.ofReal (9/10:ℝ)*(ENNReal.ofReal (99/100:ℝ)*midpointLower t 13))⁻¹
  have hJ : J≠⊤ := ENNReal.inv_ne_top.mpr (by
    dsimp only [ne_eq]
    exact mul_ne_zero (by positivity) (mul_ne_zero (by positivity) (midpointLower_pos ht 13).ne'))
  let f := fun D : ℝ ↦ ENNReal.ofReal (hitConstant*
    (4*C*(2*t)*(A/D)+8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)))
  have hreal : Tendsto (fun D : ℝ ↦ hitConstant*
    (4*C*(2*t)*(A/D)+8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.const_mul (4*C*(2*t)*A)).add
      (boundary_ratio_tendsto.const_mul (8*A))).const_mul hitConstant
    convert hh using 1 <;> try simp only [mul_zero,zero_add]
    funext D
    ring
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f,Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim : Tendsto (fun D ↦ ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*(J*(2*f D))))
      atTop (𝓝 (ENNReal.ofReal δ)) := by
    have hh := ENNReal.Tendsto.const_mul hf (a:=2) (Or.inr (by norm_num))
    have hh := ENNReal.Tendsto.const_mul hh (a:=J) (Or.inr hJ)
    have hh := ENNReal.Tendsto.const_mul hh (a:=routeDensityBound t) (Or.inr (routeDensityBound_ne_top ht))
    have hh := ENNReal.Tendsto.const_mul hh (a:=(4*(49^3*(M+1)):ℕ)) (Or.inr (by finiteness))
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add hh
  have hδE : ENNReal.ofReal δ<1 := ENNReal.ofReal_lt_one.mpr hδ
  filter_upwards [eventually_ge_atTop (1:ℝ),hlim.eventually (gt_mem_nhds hδE)] with D hD hh
  intro α hα hαA
  refine le_trans ?_ hh.le
  gcongr
  change J*(2*ENNReal.ofReal _)≤J*(2*f D)
  gcongr
  dsimp only [f]
  apply ENNReal.ofReal_le_ofReal
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hhit : 0≤hitConstant := le_of_lt hitConstant_pos
  gcongr

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalParameters
attribute [-instance] _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

theorem source_physical_scale {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0 < α → α ≤ A →
      ∀w : Time,t*(w:ℝ)=D⁻¹ →
      PhysicalScaleBounds (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) t (α/D) (D^(1/12:ℝ))
        (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) D⁻¹ (prefixTime midpointTime w) := by
  filter_upwards [source_trial_geometry hA hb ht] with D hD
  intro α hα hαA w hw
  obtain ⟨h1,hn,hr1,hR,hmesh,hceil,hw0,hw1,hwin,hlarge,hdrift,hdrift',hcut,hrelax,hsep⟩ := hD α hα hαA
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one h1
  have hnp : 0 < (⌈t/(α/D)^2⌉₊:ℝ) := by exact_mod_cast hn
  have he : (2*t)/((⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊:ℕ):ℝ)=t/(⌈t/(α/D)^2⌉₊:ℝ) := by
    push_cast
    rw [← two_mul, mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]
  refine ⟨by omega,ht,by positivity,hr1,by positivity,?_,by positivity,?_,hR,hsep.le,?_,?_,?_,?_,?_⟩
  · have := meanCost_nonneg
    positivity
  · change (1/2:ℝ)*(w:ℝ)=D⁻¹/(2*t)
    apply (eq_div_iff (by positivity : (2*t)≠0)).mpr
    nlinarith [hw]
  · rw [he]; exact hmesh
  · push_cast; nlinarith [hceil]
  · rw [he]; exact hwin
  · push_cast; nlinarith [hlarge]
  · apply (div_le_iff₀ (by push_cast; positivity : (0:ℝ) < ((⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊:ℕ):ℝ))).mpr
    have H := (div_le_iff₀ hnp).mp hdrift
    push_cast
    nlinarith [show (0:ℝ) ≤ α/D*(⌈t/(α/D)^2⌉₊:ℝ) by positivity]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalUniformModulus
attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma allocated_group_floor {ell D : ℝ} {M : ℕ} (hell : 0<ell) (hD : 0<D) (hM : 0<M)
    (hlarge : 16*(M:ℝ)/ell≤D) :
    let G := ⌊ell*D/(4*M)⌋₊
    (G*M:ℝ)≤ell*D/2 ∧ ell/(8*M)≤(G:ℝ)/D := by
  dsimp only
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hx : 0≤ell*D/(4*M) := by positivity
  have hlo := Nat.lt_floor_add_one (ell*D/(4*M))
  have hhi := Nat.floor_le hx
  have hbig : 16*M≤ell*D := by
    have h := (div_le_iff₀ hell).mp hlarge
    nlinarith
  constructor
  · have hh := (le_div_iff₀ (by positivity : (0:ℝ)<4*M)).mp hhi
    nlinarith
  · apply (le_div_iff₀ hD).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*M)).mpr
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ)<4*M)).mp hlo
    nlinarith

theorem physical_uniform_modulus :
    ∃A c D₀ : ℝ,2≤A ∧ 0 < c ∧ 1≤D₀ ∧ ∃K₀ : ℕ,400≤K₀ ∧
    ∀{N K : ℕ} [Nontrivial (Fin (N+1))] [NeZero K] {L : Length},
    ∀_hL : L.val=(K:ℝ),K₀≤K → ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 →
    D₀≤D → A/2≤α → α≤2*A → ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    c≤Phase.modulusOccupation
      (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  obtain ⟨p₀,κ,hp₀,hκ,Kc,hpath⟩ := physical_path_comparison
  obtain ⟨A,ell,b,H,t₀,hA2,hell,hb,hH,ht₀,hsupply⟩ := physical_ground_bad_supply
  have hA : 0<A := by linarith
  let t := t₀/2
  have ht : 0<t := by dsimp [t]; positivity
  let B := (routeDensityBound t).toReal
  have hB : 1≤B := by
    have hh := ENNReal.toReal_mono (routeDensityBound_ne_top ht) (one_le_routeDensityBound t)
    simpa only [ENNReal.toReal_one] using hh
  have hBt : routeDensityBound t≤ENNReal.ofReal B := by
    rw [ENNReal.ofReal_toReal (routeDensityBound_ne_top ht)]
  obtain ⟨q,hq,hpow,δ,hδ,hδ1,hcost⟩ := choose_physical_group hp₀ hκ hB
  let M := 2*q
  have hM : 0<M := by dsimp [M]; omega
  let p := min 1 (p₀/12)
  have hp : 0<p := lt_min zero_lt_one (by positivity)
  have hp1 : p≤1 := min_le_left _ _
  have hbad : 6*p+(2/5:ℝ)^q≤p₀ := by
    have hh : p≤p₀/12 := min_le_right _ _
    linarith
  obtain ⟨Ds,hDs,hsupply⟩ := hsupply t ht (by dsimp [t]; linarith) p hp hp1
  have hevent := (source_physical_scale (by positivity : 0<2*A) hb ht).and
    ((physical_collision_eventually (A:=2*A) (C:=64*(meanCost+1)) (by positivity) ht
      (by nlinarith [meanCost_nonneg]) hδ1 M).and
      (tendsto_inv_atTop_zero.eventually (gt_mem_nhds ht)))
  obtain ⟨Dg,hDg⟩ := Filter.eventually_atTop.mp hevent
  let D₀ := max Ds (max Dg (16*(M:ℝ)/ell))
  let c := ell/(128000*M*B)
  refine ⟨A,c,D₀,hA2,by dsimp [c]; positivity,hDs.trans (le_max_left _ _),
    max Kc 400,le_max_right _ _,?_⟩
  intro N K instN instK L hL hK D α hDeq hD hαlo hαhi ψ hψ
  have hDsD := (le_max_left Ds (max Dg (16*(M:ℝ)/ell))).trans hD
  have hDgD : Dg≤D := (le_max_left Dg _).trans ((le_max_right Ds _).trans hD)
  have hDlarge : 16*(M:ℝ)/ell≤D := (le_max_right Dg _).trans ((le_max_right Ds _).trans hD)
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hDs.trans hDsD)
  have hα : 0<α := lt_of_lt_of_le (by positivity : 0<A/2) hαlo
  obtain ⟨hscale,hcoll,htime⟩ := hDg D hDgD
  let w : Time := ⟨D⁻¹/t,⟨by positivity,(div_le_one ht).mpr htime.le⟩⟩
  have hw : t*(w:ℝ)=D⁻¹ := by dsimp only [w]; field_simp
  let G := ⌊ell*D/(4*M)⌋₊
  obtain ⟨hG,hGlow⟩ := allocated_group_floor hell hDp hM hDlarge
  let m := ⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊
  let R := D^(1/12:ℝ)
  let C := 64*(meanCost+1)
  let S := b*D^(-(1/3):ℝ)/8
  let s₀ := b*D^(-(1/3):ℝ)
  let u := prefixTime midpointTime w
  have h400 : 400≤K := (le_max_right Kc 400).trans hK
  have h1 : 1≤K := by omega
  have h100 : 100≤L.val := by rw [hL]; exact_mod_cast (show 100≤K by omega)
  have h50 : 50<L.val := by linarith
  refine physical_modulus_from_gains (G:=G) (M:=M) hL h400 hψ m t R C S s₀ ht.le u
    D ell B hDeq hell hM hB hGlow ?_
  intro ij hij g
  have hjoint : ∀T : Finset (Fin 3→Fin K),
      physicalDatumLaw (M:=M) g ψ m (α/D) R C S s₀ (2*t) u
        {d | T⊆datumBad hL g m t (α/D) R C S u d}≤
      (ENNReal.ofReal (6*p+(2/5:ℝ)^q))^T.card := by
    intro T
    have hh := hsupply hL h100 D α (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq) hDsD hαlo hαhi w hw (show (G:ℝ)*(2*q)≤ell*D/2 by simpa only [G,M,Nat.cast_mul,Nat.cast_ofNat] using hG) ψ hψ g T
    simpa only [ENNReal.ofReal_add (by positivity : 0≤6*p) (by positivity : 0≤(2/5:ℝ)^q),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6),ENNReal.ofReal_ofNat] using hh
  obtain ⟨σ,hσ,hm,hest⟩ := hpath K ((le_max_left Kc 400).trans hK) instK hL h1 h50 hψ
    g m t R C S s₀ D⁻¹ u (hscale α hα hαhi w hw)
    (6*p+(2/5:ℝ)^q) (by positivity) hbad hjoint hM δ B hδ hB hBt (by simpa only [M,Nat.cast_mul,Nat.cast_ofNat] using hcost)
    (hcoll α hα hαhi) ij.1 ij.2 ((Finset.mem_filter.mp hij).2)
  let := hσ
  obtain ⟨hP,hpP,hipP,hmP⟩ := hest true
  obtain ⟨hQ,hpQ,hipQ,hmQ⟩ := hest false
  let := hP
  let := hQ
  exact actual_common_gain σ _ _ hB hm hpP hpQ hipP hipQ hmP hmQ

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalPhaseWindow
attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
attribute [local instance] Classical.propDecidable

lemma occupation_eq_phase {n : ℕ} {L : Length} (f : ScalarL2 (n+1) L) :
    occupation (Nat.zero_lt_succ n) f=
      Phase.occupation (fun p : Configuration n L×Torus L ↦ f (Fin.cons p.2 p.1)) volume volume := by
  have hLp := L.property
  unfold occupation Phase.occupation
  rw [Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity)]
  simp only [div_eq_mul_inv,mul_comm]
  rfl

theorem physical_scaled_occupation :
    ∃A c D₀ : ℝ,2≤A ∧ 0 < c ∧ 1≤D₀ ∧ ∃K₀ : ℕ,400≤K₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀hN : 2≤N,∀hL : L.val=(K:ℝ),K₀≤K →
    ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ →
      c≤occupation (lt_of_lt_of_le (by decide : 0<2) hN) ψ.1 := by
  obtain ⟨A,c,Dm,hA,hc,hDm,Km,hKm,hmod⟩ := Groups.physical_uniform_modulus
  obtain ⟨Dp,hDp,Kp,hKp,hphase⟩ := physical_uniform_phase_error hA hc
  refine ⟨A,c/2,max Dm Dp,hA,by positivity,hDm.trans (le_max_left _ _),
    max Km Kp,hKm.trans (le_max_left _ _),?_⟩
  intro N K instK L hN hL hK D α hDeq hD hlo hhi ψ hψ
  cases N with
  | zero => omega
  | succ n =>
    have hn : 0<n := by omega
    have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.mpr hN
    have hm := hmod hL ((le_max_left Km Kp).trans hK) D α
      (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq)
      ((le_max_left Dm Dp).trans hD) hlo hhi ψ hψ
    have hp := hphase hL ((le_max_right Km Kp).trans hK) D α
      (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq)
      ((le_max_right Dm Dp).trans hD) hlo hhi ψ hψ
    rw [occupation_eq_phase]
    linarith

end HardSphere
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalRescaleLp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

lemma jet_fst (N : ℕ) (L J : Length) (u : Jet N J) : (jet N L J u).1=pull N L J u.1 := rfl
lemma jet_snd (N : ℕ) (L J : Length) (u : Jet N J) (p : Direction N) :
    (jet N L J u).2 p=(J.val/L.val) • pull N L J (u.2 p) := rfl
lemma jet_energy (N : ℕ) (L J : Length) (u : Jet N J) :
    energy (jet N L J u)=(J.val/L.val)^2*energy u := by
  unfold energy
  simp only [jet_snd,norm_smul,pull_norm,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]

lemma pull_bosonic {N : ℕ} {L J : Length} {f : ScalarL2 N J} (hf : bosonic f) :
    bosonic (pull N L J f) := by
  intro σ
  have hσ := (measurePreserving_permute (L:=L) σ).quasiMeasurePreserving.tendsto_ae.eventually (pull_ae N L J f)
  have hb := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually (Measure.ae_smul_measure (hf σ) (ENNReal.ofReal (jacobian N L J)))
  filter_upwards [hσ,hb,pull_ae N L J f] with X hX hB hY
  change (pull N L J f) (fun i ↦ X (σ i))=amplitude N L J • f (config N L J (fun i ↦ X (σ i))) at hX
  rw [hX,hY]
  exact congrArg (fun z : ℂ ↦ amplitude N L J • z) hB

end HardSphere.Rescaling
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalRescaleDomain
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

lemma smoothPull_jet {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) :
    (smoothPull (L:=L) f).jet=jet N L J f.jet := by
  apply Prod.ext
  · apply Lp.ext
    have hf := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually
      (Measure.ae_smul_measure (MemLp.coeFn_toLp f.memLp) (ENNReal.ofReal (jacobian N L J)))
    filter_upwards [MemLp.coeFn_toLp (smoothPull (L:=L) f).memLp,hf,pull_ae N L J f.jet.1] with X hX hF hP
    change ((smoothPull (L:=L) f).memLp.toLp _) X=(pull N L J f.jet.1) X
    rw [hX,hP]
    change amplitude N L J • f.toFun (config N L J X) = amplitude N L J • (f.memLp.toLp _) (config N L J X)
    rw [hF]
  · funext p
    apply Lp.ext
    have hf := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually
      (Measure.ae_smul_measure (MemLp.coeFn_toLp (f.partial_memLp p)) (ENNReal.ofReal (jacobian N L J)))
    have hp := pull_ae N L J (f.jet.2 p)
    have hc := Lp.coeFn_smul (J.val/L.val) (pull N L J (f.jet.2 p))
    filter_upwards [MemLp.coeFn_toLp ((smoothPull (L:=L) f).partial_memLp p),hf,hp,hc] with X hX hF hP hC
    change (((smoothPull (L:=L) f).partial_memLp p).toLp _) X=((J.val/L.val) • pull N L J (f.jet.2 p)) X
    rw [hX,hC]
    change coordDerivative N L (smoothPull (L:=L) f).toFun p X=(J.val/L.val) • (pull N L J (f.jet.2 p)) X
    rw [hP]
    change _=(J.val/L.val) • (amplitude N L J • ((f.partial_memLp p).toLp _) (config N L J X))
    rw [hF]
    exact coord_pull f _ p X

lemma jet_domain {N : ℕ} {L J : Length} {a : ℝ} {u : Jet N J}
    (hu : u∈dirichletDomain N J a) : jet N L J u∈dirichletDomain N L ((L.val/J.val)*a) := by
  apply map_mem_closure (jet N L J).continuous hu
  rintro v ⟨f,rfl⟩
  exact ⟨smoothPull f,smoothPull_jet f⟩

theorem jet_ground {N : ℕ} {L J : Length} {a : ℝ} {u : Jet N J}
    (hu : IsGroundVector N J a u) : IsGroundVector N L ((L.val/J.val)*a) (jet N L J u) := by
  have hLp := L.property
  have hJp := J.property
  refine ⟨jet_domain hu.1,pull_bosonic hu.2.1,?_,?_⟩
  · change ‖unitary N L J u.1‖=1
    exact ((unitary N L J).norm_map u.1).trans hu.2.2.1
  · intro v hv hb hn
    have hd := jet_domain (L:=J) hv
    have he : (J.val/L.val)*((L.val/J.val)*a)=a := by field_simp
    rw [he] at hd
    have h := hu.2.2.2 (jet N J L v) hd (pull_bosonic hb) (by rw [jet_fst,pull_norm,hn])
    rw [jet_energy] at h ⊢
    have ht := mul_le_mul_of_nonneg_left h (sq_nonneg (J.val/L.val))
    have hid : (J.val/L.val)^2*((L.val/J.val)^2*energy v)=energy v := by field_simp
    exact ht.trans_eq hid

end HardSphere.Rescaling
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

lemma torus_preserving (L J : Length) : MeasurePreserving (torus L J) volume
    (ENNReal.ofReal (L.val^3/J.val^3) • volume) := by
  have hLp := L.property
  have hJp := J.property
  let : Measure.IsAddHaarMeasure (ENNReal.ofReal (L.val^3/J.val^3) • (volume : Measure (Torus J))) :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
  apply AddMonoidHom.measurePreserving (μ:=(volume : Measure (Torus L)))
    (ν:= ENNReal.ofReal (L.val^3/J.val^3) • (volume : Measure (Torus J)))
    (f:=(torus L J).toAddMonoidHom) (torusHomeo L J).continuous (torus L J).surjective
  rw [BathSlice.volume_torus,Measure.smul_apply,smul_eq_mul,BathSlice.volume_torus,
    ←ENNReal.ofReal_mul (by positivity : 0≤L.val^3/J.val^3)]
  congr 1
  field_simp

lemma config_cons {n : ℕ} (L J : Length) (x : Torus L) (Y : Configuration n L) :
    config (n+1) L J (Fin.cons x Y)=Fin.cons (torus L J x) (config n L J Y) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl

lemma pull_occupation_succ {n : ℕ} {L J : Length} (f : ScalarL2 (n+1) J) :
    occupation (Nat.zero_lt_succ n) (pull (n+1) L J f)=occupation (Nat.zero_lt_succ n) f := by
  have hLp := L.property
  have hJp := J.property
  let z := L.val^3/J.val^3
  have hz : 0<z := by dsimp only [z]; positivity
  have ha := (cons_preserving (n:=n) L).quasiMeasurePreserving.tendsto_ae.eventually (pull_ae (n+1) L J f)
  have ha' := Measure.ae_ae_of_ae_prod ha
  have hs : (fun Y : Configuration n L ↦ ∫x : Torus L,(pull (n+1) L J f) (Fin.cons x Y))=ᵐ[volume]
      fun Y ↦ amplitude (n+1) L J • (z • ∫x : Torus J,f (Fin.cons x (config n L J Y))) := by
    filter_upwards [ha'] with Y hY
    calc
      _ = ∫x : Torus L,amplitude (n+1) L J • f (Fin.cons (torus L J x) (config n L J Y)) := by
        apply integral_congr_ae
        filter_upwards [hY] with x hx
        simpa only [config_cons] using hx
      _ = amplitude (n+1) L J • (z • ∫x : Torus J,f (Fin.cons x (config n L J Y))) := by
        rw [integral_smul,(torus_preserving L J).integral_comp (torusHomeo L J).measurableEmbedding
          (fun x ↦ f (Fin.cons x (config n L J Y))),integral_smul_measure,
          ENNReal.toReal_ofReal hz.le]
  change (L.val^3)⁻¹ * (∫Y : Configuration n L,‖∫x : Torus L,(pull (n+1) L J f) (Fin.cons x Y)‖^2)=
    (J.val^3)⁻¹ * (∫Y : Configuration n J,‖∫x : Torus J,f (Fin.cons x Y)‖^2)
  have hsi := integral_congr_ae (hs.fun_comp fun x ↦ ‖x‖^2)
  simp only [Function.comp_def] at hsi
  rw [hsi]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  rw [(config_preserving n L J).integral_comp (config_embedding n L J)
    (fun Y ↦ ‖∫x : Torus J,f (Fin.cons x Y)‖^2),integral_smul_measure,
    ENNReal.toReal_ofReal (jacobian_pos n L J).le,smul_eq_mul,amplitude_sq]
  have hprod (b : ℝ) : (z^(n+1))⁻¹*(z^2*(z^n*b))=z*b := by
    rw [pow_succ]
    field_simp [hz.ne']
  change (L.val^3)⁻¹*((z^(n+1))⁻¹*(z^2*(z^n*_)))=(J.val^3)⁻¹*_
  rw [hprod]
  dsimp only [z]
  field_simp [hLp.ne',hJp.ne']

lemma pull_occupation {N : ℕ} (hN : 0<N) {L J : Length} (f : ScalarL2 N J) :
    occupation hN (pull N L J f)=occupation hN f := by
  cases N with
  | zero => omega
  | succ n => exact pull_occupation_succ f

end HardSphere.Rescaling
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_ThermodynamicCalibration
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.Calibration

lemma scaleQ_div {a α n L : ℝ} (ha : 0<a) (hα : 0<α) (hn : 0≤n)
    (hL : 0<L) : scaleQ a α n L / L = Real.sqrt ((a/α)*(n/L^3)) := by
  have he : a*n/(α*L) = ((a/α)*(n/L^3))*L^2 := by
    field_simp
  unfold scaleQ
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hL.le]
  exact mul_div_cancel_right₀ _ hL.ne'

theorem scale_limits {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ)
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    Tendsto (fun k ↦ scaleK a α (N k) (L k)) atTop atTop ∧
    Tendsto (fun k ↦ (scaleK a α (N k) (L k):ℝ) / scaleQ a α (N k) (L k))
      atTop (𝓝 1) ∧
    Tendsto (fun k ↦ (scaleK a α (N k) (L k):ℝ) / L k)
      atTop (𝓝 (Real.sqrt ((a/α)*ρ))) := by
  have hc : 0<Real.sqrt ((a/α)*ρ) := Real.sqrt_pos.2 (by positivity)
  have hq : Tendsto (fun k ↦ scaleQ a α (N k) (L k)/L k)
      atTop (𝓝 (Real.sqrt ((a/α)*ρ))) := by
    convert (tendsto_const_nhds.mul hdensity).sqrt using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    exact scaleQ_div ha hα (Nat.cast_nonneg _) (hL k)
  have hqtop : Tendsto (fun k ↦ scaleQ a α (N k) (L k)) atTop atTop := by
    simpa only [div_mul_cancel₀ _ (hL _).ne'] using hq.pos_mul_atTop hc hLtop
  have hkq := tendsto_nat_floor_div_atTop.comp hqtop
  refine ⟨tendsto_nat_floor_atTop.comp hqtop, hkq, ?_⟩
  have hqp (k) : scaleQ a α (N k) (L k) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hn : (0:ℝ)<N k := by exact_mod_cast hN k
    exact div_pos (mul_pos ha hn) (mul_pos hα (hL k))
  convert hkq.mul hq using 1
  · ext k
    dsimp only [Function.comp_def, scaleK]
    field_simp [hqp k]
  · simp

theorem scaled_parameters_limits {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ)
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    Tendsto (fun k ↦ (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3)
      atTop (𝓝 (ρ / (Real.sqrt ((a/α)*ρ))^3)) ∧
    Tendsto (fun k ↦ ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
      (a*(scaleK a α (N k) (L k):ℝ)/L k)) atTop (𝓝 α) := by
  have hr := (scale_limits ha hα hρ N L hN hL hLtop hdensity).2.2
  have hc : Real.sqrt ((a/α)*ρ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  constructor
  · convert hdensity.div (hr.pow 3) (pow_ne_zero _ hc) using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    by_cases hk : (scaleK a α (N k) (L k):ℝ)=0
    · simp [hk]
    · field_simp [hk, (hL k).ne']
  · have hv : a*ρ/(Real.sqrt ((a/α)*ρ))^2 = α := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    have hh := (hdensity.const_mul a).div (hr.pow 2) (pow_ne_zero _ hc)
    rw [hv] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    by_cases hk : (scaleK a α (N k) (L k):ℝ)=0
    · simp [hk]
    · field_simp [hk, (hL k).ne']

lemma densityLimit_pos {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) :
    0<densityLimit a α ρ := by unfold densityLimit; positivity

lemma densityLimit_sq {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) :
    (densityLimit a α ρ)^2 = α^3/(ρ*a^3) := by
  unfold densityLimit
  calc
    (ρ/(Real.sqrt ((a/α)*ρ))^3)^2 = ρ^2/((Real.sqrt ((a/α)*ρ))^2)^3 := by ring
    _ = α^3/(ρ*a^3) := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp

lemma densityLimit_above_threshold {a α ρ T : ℝ}
    (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) (hT : 0<T)
    (hdilute : ρ*a^3 < α^3/(4*T^2)) : 2*T < densityLimit a α ρ := by
  have hn : 0<ρ*a^3 := by positivity
  have hden : 0<4*T^2 := by positivity
  have hh := (lt_div_iff₀ hden).mp hdilute
  have hs : (2*T)^2 < α^3/(ρ*a^3) := by
    apply (lt_div_iff₀ hn).2
    nlinarith
  rw [← densityLimit_sq ha hα hρ] at hs
  have hp := densityLimit_pos ha hα hρ
  nlinarith

theorem eventually_scaled_window {a α ρ T : ℝ}
    (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) (hT : 0<T)
    (hdilute : ρ*a^3 < α^3/(4*T^2))
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    ∀ᶠ k in atTop,
      α/2 < ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
        (a*(scaleK a α (N k) (L k):ℝ)/L k) ∧
      ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
        (a*(scaleK a α (N k) (L k):ℝ)/L k) < 2*α ∧
      (T+densityLimit a α ρ)/2 < (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3 ∧
      (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3 < 2*densityLimit a α ρ := by
  obtain ⟨hd, halpha⟩ := scaled_parameters_limits ha hα hρ N L hN hL hLtop hdensity
  have hp := densityLimit_pos ha hα hρ
  have habove := densityLimit_above_threshold ha hα hρ hT hdilute
  have hlow : (T+densityLimit a α ρ)/2 < densityLimit a α ρ := by linarith
  have hupp : densityLimit a α ρ < 2*densityLimit a α ρ := by linarith
  have hwa := halpha.eventually (Ioo_mem_nhds (show α/2<α by linarith)
    (show α<2*α by linarith))
  have hwd := hd.eventually (Ioo_mem_nhds hlow hupp)
  filter_upwards [hwa, hwd] with k ha' hd'
  exact ⟨ha'.1, ha'.2, hd'.1, hd'.2⟩

end HardSphere.Calibration

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_OccupationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

lemma occupation_le_norm_sq {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
    occupation hN ψ≤‖ψ‖^2 := by
  have hLp := L.property
  let f := fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)
  have hf : MemLp f 2 (volume.prod volume) := ground_slice_memLp hN ψ
  have ha := Phase.memLp_integral_norm hf
  have hc : MemLp (fun Y ↦ ‖∫x,f (Y,x)‖) 2 volume := by
    refine ha.mono' hf.aestronglyMeasurable.integral_prod_right'.norm ?_
    exact Eventually.of_forall fun Y ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact norm_integral_le_integral_norm _
  have hi := (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integral_prod_left
  have hbound : (∫Y,‖∫x,f (Y,x)‖^2)≤(volume : Measure (Torus L)).real univ * ∫p,‖f p‖^2 ∂volume.prod volume := by
    calc
      _ ≤ ∫Y,(volume : Measure (Torus L)).real univ * ∫x,‖f (Y,x)‖^2 := by
        apply integral_mono_ae hc.integrable_sq (hi.const_mul _)
        filter_upwards [Phase.memLp_slices hf] with Y hY
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
          (Phase.integral_norm_sq_le hY)
      _ = _ := by rw [integral_const_mul,←integral_prod _ (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0))]
  have hm : (∫p,‖f p‖^2 ∂volume.prod volume)=‖ψ‖^2 := by
    rw [scalar_norm_sq_integral]
    exact (bathFirst_preserving hN L).integral_comp
      (by
        cases N with
        | zero => omega
        | succ n =>
          convert (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm.measurableEmbedding.comp
            (MeasurableEquiv.prodComm (α:=Configuration n L) (β:=Torus L)).measurableEmbedding using 1 <;> try rfl
          funext p i
          simp [insertFirst,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm])
      (fun X ↦ ‖ψ X‖^2)
  rw [hm,Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity : 0≤L.val^3)] at hbound
  unfold occupation
  change (L.val^3)⁻¹*(∫Y,‖∫x,f (Y,x)‖^2)≤‖ψ‖^2
  calc
    _ ≤ (L.val^3)⁻¹*(L.val^3*‖ψ‖^2) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ L.property.ne'),one_mul]

end HardSphere
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
attribute [local instance] Classical.propDecidable

theorem eventually_all_ground_occupation :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0 < c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      ∀ᶠ k in atTop,∀ψ : Jet (N k) (L k),IsGroundVector (N k) (L k) a ψ →
        c₀≤occupation (hN k) ψ.1 := by
  obtain ⟨A,c,D₀,hA,hc,hD₀,K₀,hK₀,hscaled⟩ := physical_scaled_occupation
  have hAp : 0<A := by linarith
  have hDp : 0<D₀ := by linarith
  refine ⟨A^3/(4*D₀^2),c,by positivity,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity
  let K := fun k ↦ Calibration.scaleK a A (N k) (L k).val
  have hKtop : Tendsto K atTop atTop :=
    (Calibration.scale_limits ha hAp hρ N (fun k ↦ (L k).val) hN
      (fun k ↦ (L k).property) hLtop hdensity).1
  have hw := Calibration.eventually_scaled_window ha hAp hρ hDp hd N
    (fun k ↦ (L k).val) hN (fun k ↦ (L k).property) hLtop hdensity
  have hlim := Calibration.densityLimit_above_threshold ha hAp hρ hDp hd
  filter_upwards [hw,hKtop.eventually (eventually_ge_atTop K₀),hNtop.eventually (eventually_ge_atTop 2)] with k hk hK hNk
  have hKpos : 0<K k := by omega
  let : NeZero (K k) := ⟨hKpos.ne'⟩
  let J : Length := ⟨(K k:ℝ),by exact_mod_cast hKpos⟩
  let D : ℝ := (N k:ℝ)/J.val^3
  let α : ℝ := D*(a*J.val/(L k).val)
  have hD : D₀≤D := by
    have hh : (D₀+Calibration.densityLimit a A ρ)/2<D := hk.2.2.1
    linarith
  have hαlo : A/2≤α := hk.1.le
  have hαhi : α≤2*A := hk.2.1.le
  have hDpos : 0<D := hDp.trans_le hD
  have hradius : J.val/(L k).val*a=α/D := by
    dsimp only [α]
    field_simp
  intro ψ hψ
  have hg := Rescaling.jet_ground (L:=J) hψ
  rw [hradius] at hg
  have hh := hscaled hNk (show J.val=(K k:ℝ) from rfl) hK D α rfl hD hαlo hαhi
    (Rescaling.jet (N k) J (L k) ψ) hg
  rw [Rescaling.jet_fst,Rescaling.pull_occupation] at hh
  exact hh

end HardSphere
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_OrbitalOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

namespace Orbital
variable {N : ℕ} (hN : 0<N) {L : Length}

lemma map_ae (ψ : ScalarL2 N L) : (map hN ψ : Configuration (N-1) L→ℂ)=ᵐ[volume] sliceIntegral hN ψ :=
  by
  unfold map
  exact MemLp.coeFn_toLp _

section
attribute [local instance] scalarL2_addCommMonoid scalarL2_module

lemma map_norm_sq (ψ : ScalarL2 N L) : ‖map hN ψ‖^2=occupation hN ψ := by
  have hLp := L.property
  rw [scalar_norm_sq_integral]
  have hsi := integral_congr_ae ((map_ae hN ψ).fun_comp fun x ↦ ‖x‖^2)
  simp only [Function.comp_def] at hsi
  rw [hsi]
  unfold sliceIntegral occupation
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,
    integral_const_mul,Real.sq_sqrt (by positivity : 0≤L.val^3)]

lemma map_norm_le (ψ : ScalarL2 N L) : ‖map hN ψ‖≤‖ψ‖ := by
  have hh := (map_norm_sq hN ψ).trans_le (occupation_le_norm_sq hN ψ)
  nlinarith [norm_nonneg (map hN ψ),norm_nonneg ψ]


end

lemma norm_sq (ψ : ScalarL2 N L) : ‖continuous hN ψ‖^2=occupation hN ψ := map_norm_sq hN ψ

end Orbital

end HardSphere
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_MixedCondensation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

attribute [local instance] groundScalarL2Complete

lemma mixedOccupation_lower {N : ℕ} (hN : 0<N) {L : Length} {a c : ℝ}
    (T : Density.Operator (ScalarL2 N L)) (hT : GroundSupported a T)
    (h : ∀u : Jet N L,IsGroundVector N L a u → c≤occupation hN u.1) :
    c ≤ mixedOccupation hN T := by
  apply T.compressionTrace_lower
  intro ψ hψ hn
  obtain ⟨u,hu,hg⟩ := hT ψ hψ hn
  rw [Orbital.norm_sq,←hu]
  exact h u hg

lemma mixedOccupation_le_one {N : ℕ} (hN : 0<N) {L : Length}
    (T : Density.Operator (ScalarL2 N L)) : mixedOccupation hN T≤1 := by
  apply T.compressionTrace_upper
  exact Orbital.map_norm_le hN

theorem condensation_with_mixed_oai :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0 < c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      (∀Ψ : (k : ℕ)→Jet (N k) (L k),
        (∀k,IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀≤liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop) ∧
      (∀T : (k : ℕ)→Density.Operator (ScalarL2 (N k) (L k)),
        (∀k,GroundSupported a (T k)) →
        c₀≤liminf (fun k ↦ mixedOccupation (hN k) (T k)) atTop) := by
  obtain ⟨ε,c,hε,hc,hevent⟩ := eventually_all_ground_occupation
  refine ⟨ε,c,hε,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity
  have he := hevent a ρ ha hρ hd N L hN hNtop hLtop hdensity
  constructor
  · intro Ψ hΨ
    have hbounded : ∀ index, occupation (hN index) (Ψ index).1 ≤ (1 : ℝ) := by
      intro index
      simpa only [(hΨ index).2.2.1,one_pow] using
        occupation_le_norm_sq (hN index) (Ψ index).1
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hbounded)
    filter_upwards [he] with index hindex
    exact hindex (Ψ index) (hΨ index)
  · intro T hT
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (x:=1) (fun k ↦ mixedOccupation_le_one (hN k) (T k)))
    filter_upwards [he] with k hk
    exact mixedOccupation_lower (hN k) (T k) (hT k) hk

end HardSphere
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.condensation_with_mixed_oai := @OAI.HardSphere.condensation_with_mixed_oai
