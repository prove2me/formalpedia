-- Prove2me | solution 1 for OAI.EuclideanRamsey.derived_subset_single
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:43:04.29565+00:00
-- url     : https://prove2.me/submissions/2fe414c1-bb5d-46f3-9f19-f999c4d8820d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean:L124-L177
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.derived_subset_single. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Theorems.Thm_OAI_EuclideanRamsey_RightFraction_mul_pair

-- ---- from OAI.Combinatorics.EuclideanRamsey.DerivedFractions ----
namespace OAI

universe uGroup uIndex uColor uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped commutatorElement
variable {G : Type uGroup} [Group G]

lemma derived_le (N : Subgroup G) [N.Normal] (n : ℕ) : Derived N n ≤ N := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Subgroup.commutator_le_left _ _).trans ih

lemma restrict_diagonal {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (f : κ → ι)
    (h : HasDiagonal M) : HasDiagonal (M.map (restrictionHom f)) := by
  intro g
  exact ⟨fun _ => g,h g,rfl⟩
lemma restrict_pairInverse {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (f : κ → ι)
    (hf : Function.Injective f) (h : PairInverse M) : PairInverse (M.map (restrictionHom f)) := by
  rintro i j hij v ⟨v,hv,rfl⟩
  obtain ⟨b,hb,hi,hj⟩ := h (f i) (f j) (fun he => hij (hf he)) v hv
  exact ⟨restrictionHom f b,⟨b,hb,rfl⟩,hi,hj⟩
lemma restrict_pairCoverage {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (N : Subgroup G)
    (f : κ → ι) (hf : Function.Injective f) (h : PairCoverage M N) :
    PairCoverage (M.map (restrictionHom f)) N := by
  intro i j hij a ha b hb
  obtain ⟨z,hz,hi,hj⟩ := h (f i) (f j) (fun he => hij (hf he)) a ha b hb
  exact ⟨restrictionHom f z,⟨z,hz,rfl⟩,hi,hj⟩

lemma lift_restricted_fraction {ι : Type uIndex} {κ : Type uColor} [DecidableEq ι] [DecidableEq κ]
    (M : Submonoid (ι → G)) (f : κ → ι) (z : κ → G)
    (h : RightFraction (M.map (restrictionHom f)) z) :
    ∃ z' : ι → G,RightFraction M z' ∧ ∀ j,z' (f j)=z j := by
  obtain ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,he⟩ := h
  refine ⟨u*v⁻¹,⟨u,hu,v,hv,rfl⟩,?_⟩
  intro j
  exact (congrFun he j).symm

lemma pair_commutator_fraction {ι : Type uIndex} [DecidableEq ι]
    (M : Submonoid (ι → G)) (hM : PairInverse M)
    (i j k : ι) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (z t : ι → G) (hz : RightFraction M z) (ht : RightFraction M t)
    (hsz : ∀ l,l≠i → l≠j → z l=1) (hst : ∀ l,l≠i → l≠k → t l=1) :
    RightFraction M (Pi.mulSingle i ⁅z i,t i⁆) := by
  have hzi : ∀ l,l≠i → l≠j → z⁻¹ l=1 := by simpa only [Pi.inv_apply,inv_eq_one] using hsz
  have hti : ∀ l,l≠i → l≠k → t⁻¹ l=1 := by simpa only [Pi.inv_apply,inv_eq_one] using hst
  have h := ((hz.mul_pair hM ht i k hik hst).mul_pair hM hz.inv i j hij hzi).mul_pair hM ht.inv i k hik hti
  have he : z*t*z⁻¹*t⁻¹=Pi.mulSingle i ⁅z i,t i⁆ := by
    ext l
    by_cases hli : l=i
    · subst l; simp [commutatorElement_def]
    · by_cases hlj : l=j
      · subst l
        have hh := hst j hli hjk
        simp [hh,Pi.mulSingle_eq_of_ne hli]
      · have hh := hsz l hli hlj
        simp [hh,Pi.mulSingle_eq_of_ne hli]
  rwa [he] at h

lemma fraction_card_le_two {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (M : Submonoid (ι → G)) (N : Subgroup G) (hd : HasDiagonal M)
    (hc : PairCoverage M N) (hcard : Fintype.card ι ≤ 2) (i : ι) :
    N ≤ singleFractions M hd i := by
  intro a ha
  change RightFraction M (Pi.mulSingle i a)
  by_cases h : ∃ j : ι,j≠i
  · obtain ⟨j,hji⟩ := h
    obtain ⟨z,hz,hzi,hzj⟩ := hc i j (Ne.symm hji) a ha 1 N.one_mem
    have he : z=Pi.mulSingle i a := by
      ext l
      by_cases hli : l=i
      · subst l; simpa using hzi
      · have hlj : l=j := by
          by_contra hlj
          have hh : 3 ≤ Fintype.card ι := by
            have hs : ({i,j,l} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
            simpa [hji,Ne.symm hji,hli,Ne.symm hli,hlj,Ne.symm hlj] using hs
          omega
        subst l
        simpa [Pi.mulSingle_eq_of_ne hli] using hzj
    exact ⟨z,hz,1,M.one_mem,by simpa using he.symm⟩
  · have he : (fun _ : ι => a)=Pi.mulSingle i a := by
      ext l
      have hl : l=i := by by_contra hh; exact h ⟨l,hh⟩
      simp [hl]
    exact ⟨_,hd a,1,M.one_mem,by simpa using he.symm⟩

theorem derived_subset_single (N : Subgroup G) [N.Normal] (n : ℕ) :
    ∀ (ι : Type uIndex) [Fintype ι] [DecidableEq ι] (M : Submonoid (ι → G))
      (hd : HasDiagonal M) (_hi : PairInverse M) (_hc : PairCoverage M N),
      Fintype.card ι ≤ n+2 → ∀ i,Derived N n ≤ singleFractions M hd i := by
  induction n with
  | zero =>
    intro ι _ _ M hd hi hc hcard i
    exact fraction_card_le_two M N hd hc hcard i
  | succ n ih =>
    intro ι _ _ M hd hi hc hcard i
    by_cases hsmall : Fintype.card ι ≤ 2
    · exact (derived_le N _).trans (fraction_card_le_two M N hd hc hsmall i)
    obtain ⟨j,hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    have hek : ∃ k : ι,k≠i ∧ k≠j := by
      by_contra hh
      have he : (Finset.univ : Finset ι) ⊆ {i,j} := by
        intro k _
        by_cases hki : k=i
        · simp [hki]
        · have hkj : k=j := by by_contra hkj; exact hh ⟨k,hki,hkj⟩
          simp [hkj]
      have hh := Finset.card_le_card he
      have hh' : Fintype.card ι ≤ 2 := hh.trans (Finset.card_insert_le _ _ |>.trans (by simp))
      exact hsmall hh'
    obtain ⟨k,hki,hkj⟩ := hek
    change ⁅Derived N n,Derived N n⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have lift (j : ι) (hji : j≠i) (a : G) (ha : a∈Derived N n) :
        ∃ z : ι → G,RightFraction M z ∧ z i=a ∧ ∀ l,l≠i → l≠j → z l=1 := by
      let κ := {l : ι // l≠j}
      let f : κ → ι := Subtype.val
      let M' := M.map (restrictionHom f)
      let i' : κ := ⟨i,Ne.symm hji⟩
      have hf : Function.Injective f := Subtype.val_injective
      have hκ : Fintype.card κ ≤ n+2 := by
        have hh := Fintype.card_subtype_lt (p:=fun l : ι => l≠j) (x:=j) (by simp)
        change Fintype.card κ < Fintype.card ι at hh
        omega
      have he := ih κ M' (restrict_diagonal M f hd) (restrict_pairInverse M f hf hi)
        (restrict_pairCoverage M N f hf hc) hκ i' ha
      obtain ⟨z,hz,he⟩ := lift_restricted_fraction M f (Pi.mulSingle i' a) he
      refine ⟨z,hz,?_,?_⟩
      · simpa [i',f] using he i'
      · intro l hli hlj
        have hh := he ⟨l,hlj⟩
        have hn : (⟨l,hlj⟩ : κ) ≠ i' := by intro he; exact hli (Subtype.mk.inj he)
        simpa [f,Pi.mulSingle_eq_of_ne hn] using hh
    obtain ⟨z,hz,hzi,hsz⟩ := lift j hji a ha
    obtain ⟨t,ht,hti,hst⟩ := lift k hki b hb
    have hh := pair_commutator_fraction M hi i j k (Ne.symm hji) (Ne.symm hki)
      (Ne.symm hkj) z t hz ht hsz hst
    change RightFraction M (Pi.mulSingle i ⁅a,b⁆)
    simpa only [hzi,hti] using hh
end EuclideanRamsey

namespace EuclideanRamsey
variable {X : Type uPoint} {G : Type uGroup} [Group G]
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open scoped commutatorElement


theorem solution.{uGroup,uIndex} : type_of% @_root_.OAI.EuclideanRamsey.derived_subset_single.{uGroup,uIndex} := @_root_.OAI.EuclideanRamsey.derived_subset_single.{uGroup,uIndex}
