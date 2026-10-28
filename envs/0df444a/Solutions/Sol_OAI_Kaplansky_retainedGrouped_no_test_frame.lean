-- Prove2me | solution 1 for OAI.Kaplansky.retainedGrouped_no_test_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:50:53.542902+00:00
-- url     : https://prove2.me/submissions/da2bce76-540d-4989-981d-32f8f024c994

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf010

section
-- module Solutions.OAIQ15_Sf.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

theorem testProjectiveDimension_pos {m R : ℕ} (hm : 0 < m) (i : Fin R) :
    0 < testProjectiveDimension m R i := by
  have hn : R-i.val ≠ 0 := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hp : 0 < 4^k := pow_pos (by omega) _
  have hh : 0 < 4^(R-i.val)-1 := by rw [hk, pow_succ]; omega
  unfold testProjectiveDimension
  positivity

end Kaplansky

end

namespace Kaplansky
open scoped BigOperators

theorem retainedTrivialMultiplicity_eq (m R : ℕ) :
    retainedTrivialMultiplicity m R = 64*m^2*(∑ t : Fin (R+1),4^t.val) := by
  have ht : ∀ t : Fin (R+1), testMultiplicity m R (R-t.val) 0=64*m*4^t.val := by
    intro t
    change 64*m*4^(R-(R-t.val))=64*m*4^t.val
    have he : R-(R-t.val)=t.val := by omega
    rw [he]
  unfold retainedTrivialMultiplicity
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

theorem retainedTrivialMultiplicity_bound {m R : ℕ} (hm : 0 < m) :
    retainedTrivialMultiplicity m R < 2*m*testRank m R 0 := by
  rw [retainedTrivialMultiplicity_eq,testRank_eq]
  have h := three_sum_pow_four (R+1)
  rw [pow_succ] at h
  have hp : 0<64*m^2 := by positivity
  have hsum : (∑ t : Fin (R+1),4^t.val)<2*4^R := by omega
  have hh := Nat.mul_lt_mul_of_pos_left hsum hp
  simpa only [Nat.add_zero] using (show 64*m^2*(∑ t : Fin (R+1),4^t.val)<2*m*(64*m*4^R) from by nlinarith [hh])

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Relative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral relative singular chains, homology, and relative section maps. -/

section
open CategoryTheory Limits AlgebraicTopology

theorem relativeChainMap_id {A X : TopCat.{0}} (i : A ⟶ X) :
    relativeChainMap i i (𝟙 A) (𝟙 X) (by simp) = 𝟙 _ := by
  apply (cancel_epi (relativeChainProjection i)).mp
  simp

end

section
open CategoryTheory Limits

theorem relativeHomologyMap_id {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    relativeHomologyMap i i (𝟙 _) (𝟙 _) (by simp) n = 𝟙 _ := by
  simp [relativeHomologyMap, relativeChainMap_id, relativeSingularHomology]

theorem relativeHomologyMap_comp {A X B Y C Z : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j)
    (b : B ⟶ C) (g : Y ⟶ Z) (h' : j ≫ g = b ≫ k) (n : ℕ) :
    relativeHomologyMap i j a f h n ≫ relativeHomologyMap j k b g h' n =
      relativeHomologyMap i k (a ≫ b) (f ≫ g) (by rw [← Category.assoc, h,
        Category.assoc, h', Category.assoc]) n := by
  exact (HomologicalComplex.homologyMap_comp (relativeChainMap i j a f h)
    (relativeChainMap j k b g h') n).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (relativeChainMap_comp i j k a f h b g h'))

end

open Bundle Topology CategoryTheory OnePoint

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Equivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Contractible-pair homology, equivalences, and relative map extensionality. -/

section
open CategoryTheory Limits
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The isomorphism is the same map as that induced by the actual map of pairs. -/
theorem relativeHomologyHomeomorphIso_hom (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (n : ℕ) :
    (relativeHomologyHomeomorphIso e U V h n).hom =
      relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
        (subspaceMap U V ⟨e, e.continuous⟩ (fun x hx => (h x).mp hx))
        (TopCat.ofHom ⟨e, e.continuous⟩) (subspaceMap_square _ _ _ _) n := rfl

end

section
open CategoryTheory

/-- Into an embedded subspace, the ambient map uniquely determines the
map of relative chains and hence of relative homology. -/
theorem relativeHomologyMap_congr_ambient {A X B Y : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) [Mono j]
    (a b : A ⟶ B) (f g : X ⟶ Y)
    (h : i ≫ f = a ≫ j) (h' : i ≫ g = b ≫ j) (he : f = g) (n : ℕ) :
    relativeHomologyMap i j a f h n = relativeHomologyMap i j b g h' n := by
  subst g
  have ha : a = b := (cancel_mono j).mp (h.symm.trans h')
  subst b
  rfl

end

open CategoryTheory Limits HomologicalComplex ContinuousMap

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_MayerVietoris
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative Mayer-Vietoris comparison, exactness, and gluing. -/

section
open CategoryTheory Limits HomologicalComplex

variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
include hU hV hcover

theorem relativeOpenCoverGlue_restrictions (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    restrictedPairToAmbientHomologyMap U A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = u ∧
    restrictedPairToAmbientHomologyMap V A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = v := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  have he := (relativeMayerVietoris_exact_at_sum U V A hU hV hcover (n+1)).g_desc
    (biprod.desc u v) (show (relativeMayerVietorisSumSequence U V A (n+1)).f ≫
      biprod.desc u v = 0 by
        dsimp only [relativeMayerVietorisSumSequence]
        erw [biprod.lift_desc, Preadditive.neg_comp, hcompat, add_neg_cancel]
        rfl)
  constructor
  · have hl := congrArg (fun f => biprod.inl ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hl
    erw [biprod.inl_desc_assoc, biprod.inl_desc] at hl
    exact hl
  · have hr := congrArg (fun f => biprod.inr ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hr
    erw [biprod.inr_desc_assoc, biprod.inr_desc] at hr
    exact hr

end

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

/-- Vanishing criterion in full relative singular homology, suitable for
inductively joining bundle charts. -/
theorem relativeOpenCover_isZero (n : ℕ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1)))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1)))
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) (n+1)) := by
  have hg : (relativeMayerVietorisSumSequence U V A (n+1)).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  exact (relativeMayerVietoris_exact_at_relative U V A hU hV hcover n).isZero_of_both_zeros
    hg (hi.eq_of_tgt _ _)

/-- Agreement on the two charts determines a global normalization uniquely
when the preceding overlap group vanishes. -/
theorem relativeOpenCover_hom_ext (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hu : restrictedPairToAmbientHomologyMap U A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap U A (n+1) ≫ g)
    (hv : restrictedPairToAmbientHomologyMap V A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap V A (n+1) ≫ g) : f = g := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A (n+1)).g).mp
  dsimp only [relativeMayerVietorisSumSequence]
  apply biprod.hom_ext'
  · erw [biprod.inl_desc_assoc, biprod.inl_desc_assoc]
    exact hu
  · erw [biprod.inr_desc_assoc, biprod.inr_desc_assoc]
    exact hv

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hyperplane
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.productLineCore_contMDiffVectorBundle _root_.OAI.Kaplansky.ComplexGrassmann.smoothLineSum_contMDiffVectorBundle _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem graphVerticalFunctional_vector (F : GraphFrame 1 k) (A : GraphSlope 1 k) (j : Fin k) :
    graphVerticalFunctional F j (graphLineVector F A)=A (fun _ => 1) j := by
  change (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).2 j=_
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]

end Kaplansky.ComplexGrassmann

end

open Bundle Topology
namespace Kaplansky.ComplexGrassmann

theorem standard_verticalFunctional (k : ℕ) (i : Fin k) :
    graphVerticalFunctional (standardLineGraphFrame k) i=coordinateFunctional (positiveCoordinate k i) := by
  apply LinearMap.ext
  intro v
  exact standardLineGraphFrame_vertical k _ i

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_FiniteCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative maps and vanishing and gluing over finite open covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Relative homology of an empty ambient space is zero in every degree. -/
theorem relativeHomology_isZero_empty [IsEmpty X] (A : Set X) (n : ℕ) :
    IsZero (relativeSingularHomology (subspaceInclusion A) n) := by
  have : IsIso (subspaceInclusion A) := by
    exact (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of X) (show A ≃ₜ X from
      { toFun := Subtype.val
        invFun := fun x => isEmptyElim x
        left_inv := fun x => isEmptyElim x.val
        right_inv := fun x => isEmptyElim x
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_of_discreteTopology })).isIso_hom
  have : IsIso (integralSingularChains.map (subspaceInclusion A)) := by infer_instance
  exact (homologyFunctor _ _ n).map_isZero
    (isZero_cokernel_of_epi (integralSingularChains.map (subspaceInclusion A)))

/-- The relative two-chart sum is surjective also in degree zero. There
is no spurious degree-minus-one overlap hypothesis. -/
theorem relativeOpenCover_sum_epi_zero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (relativeMayerVietorisSumSequence U V A 0).g := by
  have : Epi (relativeCoverChainSequence U V A).g :=
    (relativeCoverChainSequence_shortExact U V A).epi_g
  have hepi : Epi (homologyMap (relativeCoverChainSequence U V A).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j; simp)
  have hiso : IsIso (homologyMap (relativeCoverChainComparison U V A) 0) := by
    change IsIso (relativeOpenCoverHomologyIso U V A hU hV hcover 0).hom
    infer_instance
  have : Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫
      (relativeMayerVietorisSumSequence U V A 0).g) := by
    change Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫ biprod.desc _ _)
    erw [relativeCoverMiddleHomologyIso_map]
    exact epi_comp' hepi (@IsIso.epi_of_iso _ _ _ _ _ hiso)
  exact epi_of_epi (relativeCoverMiddleHomologyIso U V A 0).hom _

theorem relativeOpenCover_zero_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) 0))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) 0)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) 0) := by
  have := relativeOpenCover_sum_epi_zero U V A hU hV hcover
  have hg : (relativeMayerVietorisSumSequence U V A 0).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A 0).g).mp
  erw [hg, zero_comp]

/-- Uniform vanishing below r is preserved by a two-set open union. -/
theorem relativeOpenUnion_below_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (r : ℕ)
    (hu : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n))
    (hv : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n))
    (hi : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) n) := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  have hu' n hn := (hu n hn).of_iso
    (restrictedPairSubsetIso U (U ∪ V) A Set.subset_union_left n)
  have hv' n hn := (hv n hn).of_iso
    (restrictedPairSubsetIso V (U ∪ V) A Set.subset_union_right n)
  have hi' n hn := (hi n hn).of_iso
    (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)
  intro n hn
  cases n with
  | zero =>
    exact relativeOpenCover_zero_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov (hu' 0 hn) (hv' 0 hn)
  | succ n =>
    exact relativeOpenCover_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov n (hu' (n+1) hn) (hv' (n+1) hn) (hi' n (by omega))

end

section
open CategoryTheory Limits Set
variable {X ι : Type} [TopologicalSpace X]

/-- Uniform relative vanishing below r on all nonempty finite intersections
implies the same bound on their union. The empty union and degree zero are
included, and there is no loss depending on the number of charts. -/
theorem finiteRelativeOpenUnion_below_isZero (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (r : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ n < r,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) n) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    intro n _
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    rw [he]
    exact relativeHomology_isZero_empty _ n
  | @insert a S ha ih =>
    by_cases hs : S.Nonempty
    · have hU : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set (U a))) n) := by
        have he : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
        have hz := hinter {a} (by simp) (by simp)
        rw [he] at hz
        exact hz
      have hV := ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts n hn => hinter T ht (hts.trans (Finset.subset_insert a S)) n hn)
      have hI : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
        apply ih (fun i => U a ∩ U i)
          (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi)))
        intro T ht hts n hn
        have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) n hn
        have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
          ext x
          simp only [mem_iInter, Finset.mem_insert]
          constructor
          · intro hx i hi
            rcases hi with rfl | hi
            · obtain ⟨j,hj⟩ := ht
              exact (hx j hj).1
            · exact (hx i hi).2
          · intro hx i hi
            exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
        rw [he]
        exact hb
      have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
        ext x
        simp only [mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨i,hi,hxa,hxi⟩
          exact ⟨hxa,i,hi,hxi⟩
        · rintro ⟨hxa,i,hi,hxi⟩
          exact ⟨i,hi,hxa,hxi⟩
      rw [heI] at hI
      have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
      rw [heW]
      exact relativeOpenUnion_below_isZero (U a) (⋃ i ∈ S, U i) A
        (hopen a (by simp))
        (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
        r hU hV hI
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      have hz := hinter {a} (by simp) (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      have heb : (⋃ i ∈ insert a (∅ : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hz
      rw [heb]
      exact hz

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairHomologyMap_comp {U V W : Set X}
    (h : U ⊆ V) (k : V ⊆ W) (A : Set X) (n : ℕ) :
    restrictedPairHomologyMap h A n ≫ restrictedPairHomologyMap k A n =
      restrictedPairHomologyMap (h.trans k) A n := by
  unfold restrictedPairHomologyMap
  erw [← homologyMap_comp]
  congr 1
  unfold restrictedPairChainMap
  erw [relativeChainMap_comp]
  rfl

/-- Actual inclusion after eliminating a redundant enclosing subtype. -/
theorem restrictedPairSubsetIso_toAmbient (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A h n).hom ≫ restrictedPairHomologyMap h A n =
      restrictedPairToAmbientHomologyMap (Subtype.val ⁻¹' U : Set W) (Subtype.val ⁻¹' A) n := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Maps out of a restricted open union are determined on its two actual
subsets when the preceding relative overlap group vanishes. -/
theorem relativeOpenUnion_hom_ext (U V A : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z)
    (hu : restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ g)
    (hv : restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ g) : f = g := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  apply relativeOpenCover_hom_ext U' V' (Subtype.val ⁻¹' A)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hcov n
    (hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)) f g
  · rw [← restrictedPairSubsetIso_toAmbient U (U ∪ V) A Set.subset_union_left,
      Category.assoc, Category.assoc, hu]
  · rw [← restrictedPairSubsetIso_toAmbient V (U ∪ V) A Set.subset_union_right,
      Category.assoc, Category.assoc, hv]

end

section
open CategoryTheory Limits Set

section
variable {X ι : Type} [TopologicalSpace X]

/-- The actual chart inclusions jointly detect maps out of a finite open
union in degree n+1 if every intersection vanishes in degrees at most n. -/
theorem finiteRelativeOpenUnion_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z)
    (hfg : ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
      restrictedPairHomologyMap h A (n+1) ≫ f =
      restrictedPairHomologyMap h A (n+1) ≫ g) : f = g := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    have hz : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ (∅ : Finset ι), U i))) (n+1)) := by
      rw [he]
      exact relativeHomology_isZero_empty _ _
    exact hz.eq_of_src f g
  | @insert a S ha ih =>
    have hI : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
      apply finiteRelativeOpenUnion_below_isZero S (fun i => U a ∩ U i) A
        (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))) (n+1)
        ?_ n (by omega)
      intro T ht hts q hq
      have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
      have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [mem_iInter, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
            exact (hx j hj).1
          · exact (hx i hi).2
        · intro hx i hi
          exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
      rw [he]
      exact hb
    have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
      ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩
        exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩
        exact ⟨i,hi,hxa,hxi⟩
    rw [heI] at hI
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    revert f g hfg
    rw [heW]
    intro f g hfg
    apply relativeOpenUnion_hom_ext (U a) (⋃ i ∈ S, U i) A (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi)))) n hI f g
    · exact hfg a (by simp) Set.subset_union_left
    · apply ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      exact hfg i (Finset.mem_insert_of_mem hi) (h.trans Set.subset_union_right)

end

section
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairSubsetIso_map (U V W A : Set X)
    (hUV : U ⊆ V) (hVW : V ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A (hUV.trans hVW) n).hom ≫
      restrictedPairHomologyMap hUV A n =
    restrictedPairHomologyMap (preimage_mono hUV :
      (Subtype.val ⁻¹' U : Set W) ⊆ Subtype.val ⁻¹' V) (Subtype.val ⁻¹' A) n ≫
      (restrictedPairSubsetIso V W A hVW n).hom := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Compatible linear maps on two open subspaces glue to a map on
their union when the preceding overlap homology is zero. -/
theorem relativeOpenUnion_exists_glue (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z,
      restrictedPairHomologyMap (subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f = u ∧
      restrictedPairHomologyMap (subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f = v := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  let A' : Set ↥(U ∪ V) := Subtype.val ⁻¹' A
  have hcov : U' ∪ V' = univ := by ext x; exact iff_true_intro x.property
  let eu := restrictedPairSubsetIso U (U ∪ V) A subset_union_left (n+1)
  let ev := restrictedPairSubsetIso V (U ∪ V) A subset_union_right (n+1)
  have hi' : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A' : Set ↥(U' ∩ V'))) n) :=
    hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ hx => Or.inl hx.1) n)
  have hc : restrictedPairHomologyMap (inter_subset_left : U' ∩ V' ⊆ U') A' (n+1) ≫
        (eu.hom ≫ u) =
      restrictedPairHomologyMap (inter_subset_right : U' ∩ V' ⊆ V') A' (n+1) ≫
        (ev.hom ≫ v) := by
    rw [← Category.assoc, ← Category.assoc]
    change (_ ≫ (restrictedPairSubsetIso U (U ∪ V) A _ _).hom) ≫ u =
      (_ ≫ (restrictedPairSubsetIso V (U ∪ V) A _ _).hom) ≫ v
    erw [← restrictedPairSubsetIso_map (U ∩ V) U (U ∪ V) A inter_subset_left subset_union_left,
      ← restrictedPairSubsetIso_map (U ∩ V) V (U ∪ V) A inter_subset_right subset_union_right]
    erw [Category.assoc, Category.assoc, hcompat]
  let f := relativeOpenCoverGlue U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  have hf := relativeOpenCoverGlue_restrictions U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  refine ⟨f, ?_, ?_⟩
  · apply (cancel_epi eu.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso U (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.1
  · apply (cancel_epi ev.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso V (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.2

end

variable {X ι : Type} [TopologicalSpace X]

/-- Restricting a pair to the whole ambient set changes no homology. -/
theorem restrictedPairToAmbient_univ_isIso (A : Set X) (n : ℕ) :
    IsIso (restrictedPairToAmbientHomologyMap Set.univ A n) := by
  let e := relativeHomologyHomeomorphIso (Homeomorph.Set.univ X)
    (Subtype.val ⁻¹' A) A (fun _ => Iff.rfl) n
  have he : restrictedPairToAmbientHomologyMap Set.univ A n = e.hom := by
    erw [relativeHomologyHomeomorphIso_hom]
    apply relativeHomologyMap_congr_ambient
    rfl
  rw [he]
  infer_instance

/-- Finite chart detection for the whole actual pair. -/
theorem finiteRelativeOpenCover_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = Set.univ) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hfg : ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ g) : f = g := by
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  apply (cancel_epi (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1))).mp
  apply finiteRelativeOpenUnion_hom_ext S U A hopen n hinter
  intro i hi h
  simp only [← Category.assoc, restrictedPairHomologyMap_toAmbient]
  exact hfg i hi

end

open CategoryTheory Limits Set
section
variable {X J : Type} [TopologicalSpace X]

/-- Pairwise compatible normalizations on a finite open cover glue in
the first possibly nonzero relative degree. All inclusions are the actual
restricted-pair maps; no extension of a homomorphism is postulated. -/
theorem finiteRelativeOpenUnion_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z,
      ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
        restrictedPairHomologyMap h A (n+1) ≫ f = u i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert a S ha ih =>
    obtain ⟨v,hv⟩ := ih (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    let C : J → Set X := fun i => U a ∩ U i
    have hCopen : ∀ i ∈ S, IsOpen (C i) :=
      fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))
    have hCI : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
        IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, C i))) q) := by
      intro T ht hts q hq
      have he : (⋂ i ∈ T, C i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [C, mem_iInter, mem_inter_iff, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
            exact (hx j hj).1
          · exact (hx i hi).2
        · intro hx i hi
          exact ⟨hx a (Or.inl rfl),hx i (Or.inr hi)⟩
      rw [he]
      exact hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
    have heI : (⋃ i ∈ S, C i) = U a ∩ (⋃ i ∈ S, U i) := by
      ext x
      simp only [C, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩; exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩; exact ⟨i,hi,hxa,hxi⟩
    have hI := finiteRelativeOpenUnion_below_isZero S C A hCopen (n+1) hCI n (by omega)
    rw [heI] at hI
    have hcv : restrictedPairHomologyMap (inter_subset_left :
          U a ∩ (⋃ i ∈ S, U i) ⊆ U a) A (n+1) ≫ u a =
        restrictedPairHomologyMap (inter_subset_right :
          U a ∩ (⋃ i ∈ S, U i) ⊆ ⋃ i ∈ S, U i) A (n+1) ≫ v := by
      have hext := finiteRelativeOpenUnion_hom_ext S C A hCopen n hCI (Z := Z)
      rw [heI] at hext
      apply hext
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp (inter_subset_right : U a ∩ U i ⊆ U i) hinc,
        Category.assoc, hv i hi hinc]
      exact hc a (by simp) i (Finset.mem_insert_of_mem hi)
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    rw [heW]
    obtain ⟨f,hfa,hfv⟩ := relativeOpenUnion_exists_glue (U a) (⋃ i ∈ S, U i) A
      (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
      n hI (u a) v hcv
    refine ⟨f,?_⟩
    intro i hi h
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfa
    · have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp hinc subset_union_right, Category.assoc, hfv]
      exact hv i hi hinc

/-- A finite open cover now gives a genuine map on the whole pair. -/
theorem finiteRelativeOpenCover_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = univ) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z,
      ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f = u i := by
  obtain ⟨v,hv⟩ := finiteRelativeOpenUnion_exists_glue S U A hopen n hinter u hc
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  refine ⟨inv (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) ≫ v, ?_⟩
  intro i hi
  have hinc : U i ⊆ ⋃ j ∈ S, U j :=
    fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
  rw [← restrictedPairHomologyMap_toAmbient hinc, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact hv i hi hinc

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Compactification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Compactification excision and ordinary relative section classes. -/

open Bundle Topology CategoryTheory
section
variable {B V : Type} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℂ (E b)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]

theorem ordinarySectionClassMap_eq (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) (n : ℕ) :
    ordinarySectionClassMap s hs n = ordinarySectionClassMap t ht n := by
  unfold ordinarySectionClassMap
  rw [integralSingularHomology_homotopy (bundleSectionHomotopy s t hs ht) n]
  rfl

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ b, NormedSpace ℂ (E b)]
  [FiberBundle V E] [VectorBundle ℂ V E] in
/-- A nowhere-zero section factors through the removed subspace, so its
localized absolute map is zero in every degree. -/
theorem ordinarySectionClassMap_eq_zero (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hne : ∀ b, s b ≠ 0) (n : ℕ) : ordinarySectionClassMap s hs n = 0 := by
  let f : C(B,nonzeroBundle (V := V) (E := E)) :=
    ⟨fun b => ⟨⟨b,s b⟩,(mem_nonzeroBundle _).mpr (hne b)⟩,hs.subtype_mk _⟩
  have he : TopCat.ofHom ⟨_,hs⟩ = TopCat.ofHom f ≫
      subspaceInclusion (nonzeroBundle (V := V) (E := E)) := rfl
  unfold ordinarySectionClassMap
  rw [he,Functor.map_comp,Category.assoc,inclusion_absoluteToRelative,Limits.comp_zero]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Product
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair homology, pair homotopies, and diagonal normalization. -/

section
open CategoryTheory Limits ContinuousMap
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Composition of homeomorphisms agrees with composition on relative homology. -/
theorem relativeHomologyHomeomorphIso_trans_hom
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (U : Set X) (V : Set Y) (W : Set Z)
    (he : ∀ x, x ∈ U ↔ e x ∈ V) (hf : ∀ y, y ∈ V ↔ f y ∈ W) (n : ℕ) :
    (relativeHomologyHomeomorphIso (e.trans f) U W
      (fun x => (he x).trans (hf (e x))) n).hom =
      (relativeHomologyHomeomorphIso e U V he n).hom ≫
        (relativeHomologyHomeomorphIso f V W hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  rw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Restricting product coordinates commutes with projection to relative fiber homology. -/
theorem productPairNormalization_restrict
    {X Y A B V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (i : C(X,Y)) (hi : Set.MapsTo i U W)
    (e : X ≃ₜ A × V) (f : Y ≃ₜ B × V)
    (he : ∀ x, x ∈ U ↔ (e x).2 ≠ 0) (hf : ∀ y, y ∈ W ↔ (f y).2 ≠ 0)
    (hcoords : ∀ x, (f (i x)).2 = (e x).2) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W i hi) (TopCat.ofHom i) (subspaceMap_square U W i hi) n ≫
      ((relativeHomologyHomeomorphIso f W {z | z.2 ≠ 0} hf n).hom ≫
        productPairProjection (B := B) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso e U {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp,
    relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  ext x : 1
  exact hcoords x

end

section
open CategoryTheory ContinuousMap
section
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- The fiber inclusion is split injective over ANY base containing that point. -/
theorem productPairFiberMap_projection (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n ≫ productPairProjection W n = 𝟙 _ := by
  unfold productPairFiberMap productPairProjection
  erw [relativeHomologyMap_comp, ← relativeHomologyMap_id (subspaceInclusion W) n]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Over a contractible base the actual inclusion is the inverse normalization. -/
theorem productPairFiberMap_eq_inv [ContractibleSpace B] (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = (productPairProjectionIso (B := B) W n).inv := by
  have := productPairProjection_isIso (B := B) W n
  apply (cancel_mono (productPairProjection (B := B) W n)).mp
  rw [productPairFiberMap_projection]
  exact (productPairProjectionIso (B := B) W n).inv_hom_id.symm

theorem productPairFiberMap_eq [ContractibleSpace B] (b c : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = productPairFiberMap c W n := by
  rw [productPairFiberMap_eq_inv, productPairFiberMap_eq_inv]

end

open CategoryTheory ContinuousMap
open scoped unitInterval
section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy that carries the removed subspace into the removed subspace
at EVERY time gives equal maps on relative singular homology. The proof uses
the actual cylinder projection and its two equal inverse inclusions. -/
theorem relativeHomologyMap_homotopy (U : Set X) (V : Set Y)
    {f g : C(X,Y)} (hf : Set.MapsTo f U V) (hg : Set.MapsTo g U V)
    (H : Homotopy f g) (hH : ∀ t : I, ∀ x ∈ U, H (t,x) ∈ V) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V f hf) (TopCat.ofHom f) (by rfl) n =
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V g hg) (TopCat.ofHom g) (by rfl) n := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let h := relativeHomologyMap (subspaceInclusion {z : I × X | z.2 ∈ U})
    (subspaceInclusion V)
    (subspaceMap _ _ H.toContinuousMap (fun z hz => hH z.1 z.2 hz))
    (TopCat.ofHom H.toContinuousMap) (by rfl) n
  have endpoint (t : I) (k : C(X,Y)) (hk : Set.MapsTo k U V)
      (he : ∀ x, H (t,x) = k x) :
      productPairFiberMap t U n ≫ h =
        relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
          (subspaceMap U V k hk) (TopCat.ofHom k) (by rfl) n := by
    unfold productPairFiberMap
    change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
    erw [relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext x : 1
    exact he x
  rw [← endpoint 0 f hf (H.apply_zero), ← endpoint 1 g hg (H.apply_one),
    productPairFiberMap_eq (0 : I) 1 U n]

end

end

section
open CategoryTheory ContinuousMap
open scoped unitInterval
variable {ι : Type}

theorem complexDiagonalHomotopy_nonzero (a : ι → ℂˣ) :
    ∀ t : I, ∀ v ∈ ({0}ᶜ : Set (ι → ℂ)), complexDiagonalHomotopy a (t,v) ∈ ({0}ᶜ : Set (ι → ℂ)) := by
  intro t v hv
  exact complexDiagonalMap_nonzero _ hv

/-- Every invertible complex diagonal change acts as the identity on actual
integral local relative homology, in every degree. -/
theorem complexDiagonalRelativeMap_eq_id (a : ι → ℂˣ) (n : ℕ) :
    complexDiagonalRelativeMap a n = 𝟙 _ := by
  have h := relativeHomologyMap_homotopy ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ
    (complexDiagonalMap_nonzero a) (fun _ h => h)
    (complexDiagonalHomotopy a) (complexDiagonalHomotopy_nonzero a) n
  change complexDiagonalRelativeMap a n = _ at h
  rw [h, ← relativeHomologyMap_id (subspaceInclusion ({0}ᶜ : Set (ι → ℂ))) n]
  apply relativeHomologyMap_congr_ambient
  rfl

end

open CategoryTheory ContinuousMap
section
variable {B ι : Type} [TopologicalSpace B]

theorem complexLineCoordinate_change {L : Type} [AddCommGroup L] [Module ℂ L]
    (e f : L ≃ₗ[ℂ] ℂ) (z : ℂ) :
    f (e.symm z) = (complexLineCoordinateUnit e f : ℂ) * z := by
  have h : e.symm z = z • e.symm 1 := by
    rw [← map_smul]
    simp
  rw [h, map_smul]
  change z * f (e.symm 1) = f (e.symm 1) * z
  exact mul_comm _ _

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveLocal
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open CategoryTheory Metric
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem canonicalProductLocalGenerator_coordinate (hp : 0 < ∑ i, K i) :
    (canonicalProductLocalHomologyIso K hp).hom (canonicalProductLocalGenerator K hp) = (1 : ℤ) :=
  ConcreteCategory.congr_hom (canonicalProductLocalHomologyIso K hp).inv_hom_id 1

theorem canonicalProductLocalGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductLocalGenerator K hp ≠ 0 := by
  intro h
  have hc := canonicalProductLocalGenerator_coordinate K hp
  rw [h, map_zero] at hc
  norm_num at hc

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

open CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem projectiveProductTopLocalizationIso_hom (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    (projectiveProductTopLocalizationIso K hp P).hom =
      absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ i, K i)) := rfl

theorem projectiveProductFundamentalClass_localizes (hp : 0 < ∑ i, K i) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i))
      (projectiveProductFundamentalClass K hp) = canonicalProductLocalGenerator K hp := by
  rw [← projectiveProductTopLocalizationIso_hom K hp]
  exact ConcreteCategory.congr_hom
    (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv_hom_id _

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProductCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair fiber normalization, punctured products, and overlap generators. -/

section
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem signedCoordinateHalfspace_open (i : Fin (Module.finrank ℝ E) × Bool) :
    IsOpen (signedCoordinateHalfspace i) := by
  have hc := (continuous_apply i.1).comp (Module.finBasis ℝ E).equivFunL.continuous
  cases h : i.2 <;> simp only [signedCoordinateHalfspace, h, Bool.false_eq_true,
    ↓reduceIte] <;> first | exact isOpen_lt hc continuous_const | exact isOpen_lt continuous_const hc

theorem signedCoordinateHalfspace_convex (i : Fin (Module.finrank ℝ E) × Bool) :
    Convex ℝ (signedCoordinateHalfspace i) := by
  let l : E →ₗ[ℝ] ℝ := (LinearMap.proj i.1).comp
    (Module.finBasis ℝ E).equivFunL.toLinearMap
  cases h : i.2
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Iio (0 : ℝ)).linear_preimage l
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Ioi (0 : ℝ)).linear_preimage l

/-- The signed coordinate halfspaces cover exactly the punctured space. -/
theorem signedCoordinateHalfspaces_cover :
    (⋃ i : Fin (Module.finrank ℝ E) × Bool, signedCoordinateHalfspace i) = ({0}ᶜ : Set E) := by
  ext x
  simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨i,b⟩,hi⟩ rfl
    cases b <;> simp [signedCoordinateHalfspace] at hi
  · intro hx
    have he : ∃ i, (Module.finBasis ℝ E).equivFunL x i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      apply (Module.finBasis ℝ E).equivFunL.injective
      ext i
      simpa using hn i
    obtain ⟨i,hi⟩ := he
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact ⟨(i,false), hi⟩
    · exact ⟨(i,true), hi⟩

end

section
open CategoryTheory Limits Set
variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A convex base, including the empty case, has no relative bundle
homology below the fiber dimension. -/
theorem convexBaseProductPair_below_isZero (C : Set E) (hC : Convex ℝ C)
    (hd : 2 ≤ Module.finrank ℝ V) (n : ℕ) (hn : n < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' {z : E × V | z.2 ≠ 0} : Set {z : E × V | z.1 ∈ C})) n) := by
  by_cases hc : C.Nonempty
  · let : ContractibleSpace C := hC.contractibleSpace hc
    exact ((localVectorHomology_isZero V hd n (by omega)).of_iso
      (productPairProjectionIso (B := C) ({0}ᶜ : Set V) n)).of_iso
        (relativeHomologyHomeomorphIso (firstCoordinateSubspaceHomeomorph C)
          _ {z : C × V | z.2 ≠ 0} (fun _ => Iff.rfl) n)
  · have : IsEmpty {z : E × V | z.1 ∈ C} :=
      ⟨fun z => hc ⟨z.1.1,z.2⟩⟩
    exact relativeHomology_isZero_empty _ n

open ComplexGrassmann

end

section
open CategoryTheory Limits
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

theorem productPairChartFiberMap_coordinates (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom =
      productPairFiberMap b W n := by
  unfold productPairChartFiberMap productPairBaseSubsetIso productPairFiberMap
  erw [relativeHomologyHomeomorphIso_hom]
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem productPairChartFiberMap_isIso (C : Set B) [ContractibleSpace C]
    (b : C) (W : Set V) (n : ℕ) : IsIso (productPairChartFiberMap C b W n) := by
  have : IsIso (productPairFiberMap b W n) := by
    rw [productPairFiberMap_eq_inv]
    infer_instance
  have : IsIso (productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom) := by
    rw [productPairChartFiberMap_coordinates]
    infer_instance
  exact IsIso.of_isIso_comp_right (productPairChartFiberMap C b W n)
    (productPairBaseSubsetIso C W n).hom

/-- Inclusion of a chart fiber is literally the same global fiber inclusion. -/
theorem productPairChartFiberMap_inclusion (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫
      restrictedPairToAmbientHomologyMap {z : B × V | z.1 ∈ C} {z | z.2 ∈ W} n =
    productPairFiberMap b.1 W n := by
  unfold productPairChartFiberMap productPairFiberMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_AffineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine-avoidance covers and convex product-pair homology. -/

section
open Set
variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J]

theorem affineAvoidanceChart_open (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : IsOpen (affineAvoidanceChart l c s) :=
  isOpen_iInter_of_finite (fun j => (signedCoordinateHalfspace_open (s j)).preimage ((l j).continuous.add continuous_const))

omit [Fintype J] in
theorem affineAvoidanceChart_convex (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Convex ℝ (affineAvoidanceChart l c s) :=
  convex_iInter (fun j => ((signedCoordinateHalfspace_convex (s j)).translate_preimage_left (c j)).linear_preimage (l j).toLinearMap)

omit [Fintype J] in
theorem affineAvoidanceCharts_cover (l : J → E →L[ℝ] F) (c : J → F) :
    (⋃ s : J → Fin (Module.finrank ℝ F) × Bool, affineAvoidanceChart l c s) =
      affineAvoidanceSet l c := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩ := mem_iUnion.mp hx
    change ∀ j, l j x + c j ≠ 0
    intro j
    have hm : l j x + c j ∈ ⋃ i, signedCoordinateHalfspace i :=
      mem_iUnion.mpr ⟨s j,mem_iInter.mp hs j⟩
    rw [signedCoordinateHalfspaces_cover] at hm
    exact hm
  · intro hx
    have he : ∀ j, ∃ i : Fin (Module.finrank ℝ F) × Bool,
        l j x + c j ∈ signedCoordinateHalfspace i := by
      intro j
      rw [← mem_iUnion, signedCoordinateHalfspaces_cover]
      exact hx j
    choose s hs using he
    exact mem_iUnion.mpr ⟨s,mem_iInter.mpr hs⟩

omit [Fintype J] in
theorem affineAvoidanceChart_subset (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) :
    affineAvoidanceChart l c s ⊆ affineAvoidanceSet l c := by
  rw [← affineAvoidanceCharts_cover]
  exact subset_iUnion _ s

end

section
open CategoryTheory Limits Set
variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A nonempty convex subset remains contractible when viewed inside a
larger base subset, with its actual iterated subspace topology. -/
theorem convexRestrictedBase_contractible (D C : Set E) (hCD : C ⊆ D)
    (hc : Convex ℝ C) (hne : (Subtype.val ⁻¹' C : Set D).Nonempty) :
    ContractibleSpace (Subtype.val ⁻¹' C : Set D) := by
  have : ContractibleSpace C := hc.contractibleSpace ⟨hne.choose.val,hne.choose_spec⟩
  exact (subspaceSubsetHomeomorph C D hCD).contractibleSpace

omit [FiniteDimensional ℝ E] in
/-- Every nonempty intersection of convex base charts has the required
lower relative vanishing. Empty intersections have zero groups as well. -/
theorem convexCover_product_intersection_below_isZero
    (D : Set E) (S : Finset J) (C : J → Set E)
    (hsub : ∀ i ∈ S, C i ⊆ D) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (T : Finset J) (ht : T.Nonempty) (hts : T ⊆ S)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology
      (subspaceInclusion {z : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) × V |
        z.2 ≠ 0}) q) := by
  let W : Set E := ⋂ i ∈ T, C i
  have hW : W ⊆ D := by
    obtain ⟨i,hi⟩ := ht
    intro x hx
    exact hsub i (hts hi) (mem_iInter.mp (mem_iInter.mp hx i) hi)
  have hcv : Convex ℝ W :=
    convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))
  have heq : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) = Subtype.val ⁻¹' W := by
    ext x; simp [W]
  rw [heq]
  by_cases hne : (Subtype.val ⁻¹' W : Set D).Nonempty
  · have := convexRestrictedBase_contractible D W hW hcv hne
    exact (localVectorHomology_isZero V hv q (by omega)).of_iso
      (productPairProjectionIso (B := (Subtype.val ⁻¹' W : Set D)) ({0}ᶜ : Set V) q)
  · have : IsEmpty ((Subtype.val ⁻¹' W : Set D) × V) :=
      ⟨fun z => hne ⟨z.1.val,z.1.property⟩⟩
    exact relativeHomology_isZero_empty _ q

omit [FiniteDimensional ℝ E] in
/-- Relative homology below fiber dimension vanishes over any finite
union of open convex base sets. Neither connectivity nor contractibility
of that union is asserted. -/
theorem convexOpenUnion_product_below_isZero
    (S : Finset J) (C : J → Set E)
    (hopen : ∀ i ∈ S, IsOpen (C i)) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : (⋃ i ∈ S, C i) × V | z.2 ≠ 0}) q) := by
  let U : J → Set (E × V) := fun i => {z | z.1 ∈ C i}
  let A : Set (E × V) := {z | z.2 ≠ 0}
  have hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ k < Module.finrank ℝ V,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) k) := by
    intro T _ hts k hk
    have he : (⋂ i ∈ T, U i) = {z : E × V | z.1 ∈ ⋂ i ∈ T, C i} := by
      ext z; simp [U]
    rw [he]
    exact convexBaseProductPair_below_isZero _
      (convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))) hv k hk
  have hz := finiteRelativeOpenUnion_below_isZero S U A
    (fun i hi => (hopen i hi).preimage continuous_fst) (Module.finrank ℝ V) hinter q hq
  have he : (⋃ i ∈ S, U i) = {z : E × V | z.1 ∈ ⋃ i ∈ S, C i} := by
    ext z; simp [U]
  rw [he] at hz
  exact hz.of_iso (productPairBaseSubsetIso (⋃ i ∈ S, C i) ({0}ᶜ : Set V) q).symm

end

open CategoryTheory Limits Set
section
variable {E F V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype J]

omit [FiniteDimensional ℝ E] in
/-- Lower relative vanishing over a finite affine-zero complement,
proved by the explicit convex cover. All kernels may intersect. -/
theorem affineAvoidance_product_below_isZero (l : J → E →L[ℝ] F) (c : J → F)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : affineAvoidanceSet l c × V | z.2 ≠ 0}) q) := by
  classical
  have h := convexOpenUnion_product_below_isZero
    (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)) (affineAvoidanceChart l c)
    (fun s _ => affineAvoidanceChart_open l c s)
    (fun s _ => affineAvoidanceChart_convex l c s) hv q hq
  have he : (⋃ i ∈ (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)),
      affineAvoidanceChart l c i) = affineAvoidanceSet l c := by
    simpa only [Finset.mem_univ, iUnion_true] using affineAvoidanceCharts_cover l c
  rw [he] at h
  exact h

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_GraphCover
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Projective graph denominators, intersections, and finite graph covers. -/

open Set
namespace ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem projectiveProductGraphCharts_cover :
    (⋃ F : ∀ i, GraphFrame 1 (K i), (projectiveProductGraphChart K F).source) = univ := by
  ext P
  simp only [mem_iUnion, mem_univ, iff_true]
  choose F hF using fun i => grassmann_atlas_covers (P i)
  exact ⟨F,fun i _ => hF i⟩

/-- Compactness supplies a genuine finite cover of the actual projective
product by graph charts. Any specified chart can be retained in the cover. -/
theorem projectiveProduct_finiteGraphCover (F₀ : ∀ i, GraphFrame 1 (K i)) :
    ∃ S : Finset (∀ i, GraphFrame 1 (K i)), F₀ ∈ S ∧
      (⋃ F ∈ S, (projectiveProductGraphChart K F).source) = univ := by
  classical
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover
    (fun F : ∀ i, GraphFrame 1 (K i) => (projectiveProductGraphChart K F).source)
    (fun F => (projectiveProductGraphChart K F).open_source)
    (by rw [projectiveProductGraphCharts_cover])
  refine ⟨insert F₀ S, by simp, subset_antisymm (subset_univ _) ?_⟩
  intro P hP
  obtain ⟨F,hF,hPF⟩ := mem_iUnion.mp (hS hP) |>.imp fun _ => mem_iUnion.mp
  exact mem_iUnion.mpr ⟨F,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hF,hPF⟩⟩

end ComplexGrassmann

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_LineNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral line normalization and finite-cover diagonal comparison. -/

section
open CategoryTheory Limits Set
variable {B ι J : Type} [TopologicalSpace B]

/-- A finite contractible cover detects the normalization of a varying
complex diagonal coordinate change. The whole base need not be contractible
or connected; the lower intersection groups are the actual relative groups. -/
theorem productPairCoordinateMap_eq_projection_of_finite_cover
    (S : Finset J) (U : J → Set B)
    (hopen : ∀ i ∈ S, IsOpen (U i)) (hcover : (⋃ i ∈ S, U i) = Set.univ)
    (hchart : ∀ i ∈ S, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × (ι → ℂ) | z.2 ≠ 0}) q))
    (f : C(B × (ι → ℂ),(ι → ℂ))) (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0)
    (a : B → ι → ℂˣ) (he : ∀ b v, f (b,v) = complexDiagonalMap (a b) v) :
    productPairCoordinateMap f hf (n+1) =
      productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ)) (n+1) := by
  let C : J → Set (B × (ι → ℂ)) := fun i => {z | z.1 ∈ U i}
  let A : Set (B × (ι → ℂ)) := {z | z.2 ∈ ({0}ᶜ : Set (ι → ℂ))}
  have hC : (⋃ i ∈ S, C i) = Set.univ := by
    ext z
    have hb : z.1 ∈ ⋃ i ∈ S, U i := by rw [hcover]; trivial
    simpa only [mem_iUnion, C, mem_ofPred_eq, mem_univ, iff_true] using hb
  refine finiteRelativeOpenCover_hom_ext S C A
    (fun i hi => (hopen i hi).preimage continuous_fst) hC n ?_ _ _ ?_
  · intro T ht hts q hq
    have heC : (⋂ i ∈ T, C i) = {point : B × (ι → ℂ) | point.1 ∈ ⋂ i ∈ T, U i} := by
      ext point
      simp [C]
    rw [heC]
    exact (hinter T ht hts q hq).of_iso
      (productPairBaseSubsetIso (⋂ i ∈ T, U i) ({0}ᶜ : Set (ι → ℂ)) q)
  · intro i hi
    by_cases hne : (U i).Nonempty
    · let : ContractibleSpace (U i) := hchart i hi hne
      let b : U i := ⟨hne.choose,hne.choose_spec⟩
      have := productPairChartFiberMap_isIso (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      apply (cancel_epi (productPairChartFiberMap (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1))).mp
      have hc : productPairFiberMap b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1) ≫
          productPairCoordinateMap f hf (n+1) = complexDiagonalRelativeMap (a b.1) (n+1) := by
        unfold productPairFiberMap productPairCoordinateMap complexDiagonalRelativeMap
        erw [relativeHomologyMap_comp]
        apply relativeHomologyMap_congr_ambient
        ext v : 1
        exact he b.1 v
      have hincl := productPairChartFiberMap_inclusion (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      have hc' := (congrArg (fun g => g ≫ productPairCoordinateMap f hf (n+1)) hincl).trans
        (hc.trans (complexDiagonalRelativeMap_eq_id (a b.1) (n+1)))
      have hp' := (congrArg (fun g => g ≫ productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ))
        (n+1)) hincl).trans (productPairFiberMap_projection b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1))
      exact (Category.assoc _ _ _).symm.trans
        (hc'.trans (hp'.symm.trans (Category.assoc _ _ _)))
    · have : IsEmpty (C i) := ⟨fun z => hne ⟨z.1.1,z.2⟩⟩
      exact (relativeHomology_isZero_empty (Subtype.val ⁻¹' A : Set (C i)) (n+1)).eq_of_src _ _

end

open Bundle Topology CategoryTheory Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

theorem div_linearEquiv_inverse_one (L : ℂ ≃ₗ[ℂ] ℂ) (z : ℂ) :
    z / L.symm 1 = L z := by
  have hn : L.symm 1 ≠ 0 := fun hz => one_ne_zero (L.symm.map_eq_zero_iff.mp hz)
  apply (div_eq_iff hn).mpr
  have he := L.symm.map_smul (L z) (1 : ℂ)
  change L.symm (L z * 1) = L z * L.symm 1 at he
  simpa only [mul_one, L.symm_apply_apply] using he

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

theorem twistedStandard_coordinate_evaluation
    (i : Option ι) (j : Fin (1+twistedProjectiveDimensions K h i))
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    (show ℂ from twistedCoordinateSection K h i j
        (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) /
      (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      coordinateFunctional j (graphLineVector (twistedStandardFrames K h i) (A i)) := by
  rw [show (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      (show ℂ ≃ₗ[ℂ] ℂ from productGraphLineEvaluation (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl i A).symm 1 from rfl,
    div_linearEquiv_inverse_one]
  change projectionDualLineFiberEquiv _ (hyperplaneFunctionalSection (coordinateFunctional j) _)
    ⟨productGraphLineVector (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) i A,_⟩ = _
  rw [hyperplaneFunctionalSection_realization]
  change coordinateFunctional j (graphLineVector (twistedStandardFrames K h i)
    (slopeCoordinate (twistedStandardFrames K h i) (slopePoint (twistedStandardFrames K h i) (A i)))) = _
  rw [slopeCoordinate_point]

theorem twistedStandardSectionCoordinates_eq
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    twistedStandardSectionCoordinates K h A = twistedSlopeEvaluationEquiv K h A := by
  funext s
  cases s with
  | inl j =>
    change ((1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) _)) /
      (1 * (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A none (fun _ => 1) j
    rw [one_mul, one_mul]
    refine (twistedStandard_coordinate_evaluation K h none (positiveCoordinate h j) A).trans ?_
    exact (congrArg (fun f : EuclideanSpace ℂ (Fin (1+h)) →ₗ[ℂ] ℂ =>
      f (graphLineVector (standardLineGraphFrame h) (A none)))
      (standard_verticalFunctional h j).symm).trans
        (graphVerticalFunctional_vector (standardLineGraphFrame h) (A none) j)
  | inr s =>
    change ((show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2) _) *
      (show ℂ from twistedCoordinateSection K h none 0 _)) /
      ((show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some (some s.1)) A) *
       (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A (some s.1) (fun _ => 1) s.2
    rw [mul_div_mul_comm]
    refine (congrArg₂ (fun x y : ℂ => x * y)
      (twistedStandard_coordinate_evaluation K h (some s.1) (positiveCoordinate (K s.1) s.2) A)
      (twistedStandard_coordinate_evaluation K h none 0 A)).trans ?_
    have hzero : coordinateFunctional (0 : Fin (1+h))
        (graphLineVector (standardLineGraphFrame h) (A none)) = 1 := by
      change (graphLineVector (standardLineGraphFrame h) (A none)) 0 = 1
      have he := graphLineVector_coordinates (standardLineGraphFrame h) (show GraphSlope 1 h from A none)
      have hh := congrArg (fun v => (standardLineGraphFrame h v).1 (0 : Fin 1)) he
      simp only [standardLineGraphFrame_horizontal,LinearEquiv.apply_symm_apply] at hh
      exact hh
    change coordinateFunctional (positiveCoordinate (K s.1) s.2)
      (graphLineVector (standardLineGraphFrame (K s.1)) (A (some s.1))) *
      coordinateFunctional (0 : Fin (1+h)) (graphLineVector (standardLineGraphFrame h) (A none)) = _
    rw [hzero,mul_one,← standard_verticalFunctional]
    exact graphVerticalFunctional_vector (standardLineGraphFrame (K s.1)) (A (some s.1)) s.2

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

theorem continuous_twistedOldComponent
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P
      (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)) := by
  have hc := ((continuous_finiteLineSumComponent
    (fun s => productLineCore K (twistedSourceLabel K h s)) s).comp hv).comp
    (twistedOldBase K h).continuous
  apply continuous_iff_continuousAt.mpr
  intro P
  rw [FiberBundle.continuousAt_section]
  have hh := (FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := P)).mp hc.continuousAt |>.2
  cases s with
  | inl j => exact hh
  | inr s => exact hh

theorem continuous_twistedSectionFromVector
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (j : Fin (1+h)) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedSectionFromVector K h v j P)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨continuous_id,fun s => ?_⟩
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_twistedOldComponent K h v hv s) (continuous_twistedCoordinateSection K h none j)

omit [Fintype ι] in
theorem twistedCoordinateSections_not_all_zero
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    ¬ (∀ j : Fin (1+h), twistedCoordinateSection K h none j P = 0) := by
  intro hz
  have hp := (twistedCoordinateSection_positive_zero_iff K h P none).mp
    (fun j => hz (positiveCoordinate h j))
  have he := hz 0
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    (projectiveProjectionMap h (P none)) = 0 at he
  rw [hp] at he
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    ((projectiveProjectionEquiv h).symm (projectiveProjectionEquiv h (firstCoordinateProjection h))) = 0 at he
  rw [Equiv.symm_apply_apply] at he
  exact hyperplaneFirstCoordinateSection_ne_zero h he

variable {d : ℕ}

theorem continuous_twistedFrameSection
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedFrameSection K h f hd P)) := by
  apply continuousOn_univ.mp
  apply continuousOn_bundle_sum (𝕜 := ℂ)
  intro j _
  exact (continuous_twistedSectionFromVector K h _ (f.continuous_vector _) j).continuousOn

theorem twistedFrameSection_ne_zero
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    twistedFrameSection K h f hd P ≠ 0 := by
  intro hz
  have hind := (f.orthonormal (twistedOldBase K h P)).linearIndependent.comp
    (Fin.castLE hd) (Fin.castLE_injective hd)
  have he : (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        f.vector (twistedOldBase K h P) (Fin.castLE hd j)) = 0 := by
    change (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
          f.vector (twistedOldBase K h P) (Fin.castLE hd j))) = 0
    change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
      twistedFrameSection K h f hd P) = 0 at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    ext s
    exact mul_comm _ _
  have hc := Fintype.linearIndependent_iff.mp hind _ he
  exact twistedCoordinateSections_not_all_zero K h P hc

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_FrameNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral normalization of finite-line frames over affine-avoidance covers. -/

section
open Bundle Topology CategoryTheory Set
variable {A S : Type} [TopologicalSpace A] [Fintype S] {I : S → Type}
  (C : ∀ s, VectorBundleCore ℂ A ℂ (I s))
  (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
  (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))

variable (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
  (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))

theorem finiteLineFrame_transition (a : A) (z : S → ℂ) :
    finiteLineFrameEquiv C w hwn a ((finiteLineFrameEquiv C v hn a).symm z) =
      complexDiagonalMap (fun s => complexLineCoordinateUnit
        (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a)) z := by
  funext s
  exact complexLineCoordinate_change
    (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a) (z s)

/-- Normalization of the actual finite sum of actual line cores is independent
of the chosen continuous nonvanishing line frames on a finite contractible
cover with the stated lower intersection vanishing. No global contractibility
or connectedness hypothesis is required. -/
theorem finiteLineFrameNormalization_eq_of_finite_cover
    {J : Type} (T : Finset J) (U : J → Set A)
    (hopen : ∀ i ∈ T, IsOpen (U i)) (hcover : (⋃ i ∈ T, U i) = Set.univ)
    (hchart : ∀ i ∈ T, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ I : Finset J, I.Nonempty → I ⊆ T → ∀ q < n+1,
      Limits.IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ I, U i) × (S → ℂ) | z.2 ≠ 0}) q)) :
    finiteLineFrameNormalization C v hn hc (n+1) =
      finiteLineFrameNormalization C w hwn hwc (n+1) := by
  let ev := finiteLineFrameHomeomorph C v hn hc
  let ew := finiteLineFrameHomeomorph C w hwn hwc
  let f : C(A × (S → ℂ),(S → ℂ)) :=
    ⟨fun z => (ew (ev.symm z)).2, continuous_snd.comp (ew.continuous.comp ev.symm.continuous)⟩
  have hf : ∀ z : A × (S → ℂ), z.2 ≠ 0 → f z ≠ 0 := by
    intro z hz he
    have hw : (ev.symm z).2 = 0 :=
      (finiteLineFrameHomeomorph_zero_iff C w hwn hwc _).mp he
    have hv := (finiteLineFrameHomeomorph_zero_iff C v hn hc (ev.symm z)).mpr hw
    change (ev (ev.symm z)).2 = 0 at hv
    rw [ev.apply_symm_apply] at hv
    exact hz hv
  let c : A → S → ℂˣ := fun a s => complexLineCoordinateUnit
    (lineFrameEquiv (C s) (v s) (hn s) a)
    (lineFrameEquiv (C s) (w s) (hwn s) a)
  have he : ∀ a z, f (a,z) = complexDiagonalMap (c a) z :=
    finiteLineFrame_transition C v hn w hwn
  have hnorm := productPairCoordinateMap_eq_projection_of_finite_cover
    T U hopen hcover hchart n hinter f hf c he
  have heq : finiteLineFrameNormalization C w hwn hwc (n+1) =
      (finiteLineFrameRelativeIso C v hn hc (n+1)).hom ≫
        productPairCoordinateMap f hf (n+1) := by
    unfold finiteLineFrameNormalization finiteLineFrameRelativeIso
    rw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
    unfold productPairProjection productPairCoordinateMap
    erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext z : 1
    change (ew z).2 = (ew (ev.symm (ev z))).2
    rw [ev.symm_apply_apply]
  rw [heq, hnorm]
  rfl

end

open Bundle Topology CategoryTheory Set
section
variable {E F J S : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J] [Fintype S] {I : S → Type}

/-- On the complement of any finite family of affine zero sets, the two
normalizations of the ACTUAL finite sum of line cores coincide in
fiber degree. Contractibility, connectivity, transition degree and homology
vanishing are not premises: the finite convex cover supplies the comparison. -/
theorem affineAvoidance_finiteLineFrameNormalization_eq
    (l : J → E →L[ℝ] F) (c : J → F)
    (C : ∀ s, VectorBundleCore ℂ (affineAvoidanceSet l c) ℂ (I s))
    (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
    (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))
    (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
    (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))
    (hv : 2 ≤ Module.finrank ℝ (S → ℂ)) :
    finiteLineFrameNormalization C v hn hc (Module.finrank ℝ (S → ℂ)) =
      finiteLineFrameNormalization C w hwn hwc (Module.finrank ℝ (S → ℂ)) := by
  classical
  let I := J → Fin (Module.finrank ℝ F) × Bool
  let U : I → Set (affineAvoidanceSet l c) := fun s => Subtype.val ⁻¹' affineAvoidanceChart l c s
  have hcover : (⋃ s ∈ (Finset.univ : Finset I), U s) = Set.univ := by
    ext x
    have hx : x.val ∈ ⋃ s : I, affineAvoidanceChart l c s := by
      rw [affineAvoidanceCharts_cover]; exact x.property
    simpa only [U, mem_iUnion, Finset.mem_univ, exists_true_left,
      mem_preimage, mem_univ, iff_true] using hx
  let n := Module.finrank ℝ (S → ℂ) - 1
  have hdim : n+1 = Module.finrank ℝ (S → ℂ) := by dsimp [n]; omega
  have h := finiteLineFrameNormalization_eq_of_finite_cover C v hn hc w hwn hwc
    Finset.univ U
    (fun s _ => (affineAvoidanceChart_open l c s).preimage continuous_subtype_val) hcover
    (fun s _ hne => convexRestrictedBase_contractible _ _ (affineAvoidanceChart_subset l c s)
      (affineAvoidanceChart_convex l c s) hne) n
    (fun T ht hts q hq => convexCover_product_intersection_below_isZero
      (affineAvoidanceSet l c) Finset.univ (affineAvoidanceChart l c)
      (fun s _ => affineAvoidanceChart_subset l c s)
      (fun s _ => affineAvoidanceChart_convex l c s) T ht hts hv q (by omega))
  rwa [hdim] at h

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Normalization
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted bundle graph normalization and its naturality. -/

section
open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)

theorem twistedCoordinateSpace_real_finrank :
    Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) = 2*(h+∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [TwistedHyperplaneSlot, Fintype.card_sigma, Nat.mul_comm]

theorem twistedGraphBundleNormalization_pullback
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source) (n : ℕ) :
    twistedGraphBundleNormalization K h U e F hF n =
      (twistedGraphBundlePullbackRelativeIso K h U e n).hom ≫
        finiteLineFrameNormalization
          (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
          (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
          (continuous_twistedGraphLineUnit K h U e F hF) n := by
  have he := relativeHomologyHomeomorphIso_trans_hom
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))
    (Subtype.val ⁻¹' nonzeroBundle) {z | z.2 ≠ 0} {z | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1)
    (fun z => (not_congr (finiteLineFrameHomeomorph_zero_iff _ _ _ _ z)).symm) n
  exact (congrArg (fun g => g ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n)
    he).trans (Category.assoc _ _ _)

variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fintype J]

theorem twistedGraphBundleNormalization_affine_eq
    (l : J → E →L[ℝ] V) (c : J → V) (a : U ≃ₜ affineAvoidanceSet l c)
    (F₁ F₂ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (h₁ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₁).source)
    (h₂ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₂).source)
    (hp : 0 < h+∑ i, K i) :
    twistedGraphBundleNormalization K h U a F₁ h₁ (2*(h+∑ i, K i)) =
      twistedGraphBundleNormalization K h U a F₂ h₂ (2*(h+∑ i, K i)) := by
  rw [twistedGraphBundleNormalization_pullback,twistedGraphBundleNormalization_pullback]
  apply congrArg (fun f => (twistedGraphBundlePullbackRelativeIso K h U a (2*(h+∑ i, K i))).hom ≫ f)
  have hv : 2 ≤ Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) := by
    rw [twistedCoordinateSpace_real_finrank]; omega
  have he := affineAvoidance_finiteLineFrameNormalization_eq (S := TwistedHyperplaneSlot K h) l c
    (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U a))
    (twistedGraphLineUnit K h U a F₁ h₁) (twistedGraphLineUnit_ne_zero K h U a F₁ h₁)
    (continuous_twistedGraphLineUnit K h U a F₁ h₁)
    (twistedGraphLineUnit K h U a F₂ h₂) (twistedGraphLineUnit_ne_zero K h U a F₂ h₂)
    (continuous_twistedGraphLineUnit K h U a F₂ h₂) hv
  rwa [twistedCoordinateSpace_real_finrank] at he

variable {L : Type} [Fintype L]

theorem twistedGraphBundleIntersection_below_isZero
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (G : L → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set (twistedGraphBundleDomain K h
        (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)))) q) := by
  apply (affineAvoidance_product_below_isZero
    (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F₀ G)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F₀ G)
    (V := TwistedHyperplaneSlot K h → ℂ) ?_ q ?_).of_iso
    (twistedGraphBundleRelativeIso K h
      (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)
      (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F₀ G)
      F₀ inter_subset_left q)
  · rw [twistedCoordinateSpace_real_finrank]; omega
  · rwa [twistedCoordinateSpace_real_finrank]

end Kaplansky

end

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A B : Type} [Fintype ι] [TopologicalSpace A] [TopologicalSpace B]
  (K : ι → ℕ) (r : ℕ) {U V : Set (ProjectiveProduct (twistedProjectiveDimensions K r))} (h : U ⊆ V)
  (e : U ≃ₜ A) (f : V ≃ₜ B) (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K r i))
  (hF : V ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K r) F).source)

/-- The fiber coordinate depends only on the original base point,
fiber vector and graph frame, and not on the chosen base coordinates. -/
theorem twistedGraphBundleCoordinates_restrict_fiber (z : twistedGraphBundleDomain K r U) :
    (twistedGraphBundleCoordinates K r V f F hF ⟨z.1,h z.2⟩).2 =
      (twistedGraphBundleCoordinates K r U e F (h.trans hF) z).2 := by
  funext s
  change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r V f F hF s (f ⟨z.1.proj,h z.2⟩)) =
    (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r U e F (h.trans hF) s (e ⟨z.1.proj,z.2⟩))
  congr 1
  cases s with
  | inl j =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1
    simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
      productGraphLineProjection,productGraphLineVector,chartBaseMap,
      ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply]
    dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv]
    simp only [Homeomorph.symm_apply_apply]
    rfl
  | inr s =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1 <;>
      simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
        productGraphLineProjection,productGraphLineVector,chartBaseMap,
        ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] <;>
      dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv] <;>
      simp only [Homeomorph.symm_apply_apply] <;> rfl

/-- Restriction of the normalization on a larger chart is exactly the
normalization of the smaller actual bundle pair, in any base coordinates. -/
theorem twistedGraphBundleNormalization_restrict (n : ℕ) :
    restrictedPairHomologyMap (fun _ hz => h hz : twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)
        nonzeroBundle n ≫ twistedGraphBundleNormalization K r V f F hF n =
      twistedGraphBundleNormalization K r U e F (h.trans hF) n := by
  exact productPairNormalization_restrict
    (Subtype.val ⁻¹' nonzeroBundle) (Subtype.val ⁻¹' nonzeroBundle)
    (subspaceInclusionOfLE (fun _ hz => h hz :
      twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)).hom
    (fun _ hz => hz)
    (twistedGraphBundleCoordinates K r U e F (h.trans hF))
    (twistedGraphBundleCoordinates K r V f F hF)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r U e F (h.trans hF) z)).symm)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r V f F hF z)).symm)
    (twistedGraphBundleCoordinates_restrict_fiber K r h e f F hF) n

end Kaplansky

end

open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

/-- The local integral fiber normalizations agree after the actual
inclusions from a pairwise intersection of total-space charts. -/
theorem twistedGraphBundleChartNormalization_compatible
    (F G : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    restrictedPairHomologyMap (inter_subset_left :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h F (2*(h+∑ i, K i)) =
    restrictedPairHomologyMap (inter_subset_right :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h G)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h G (2*(h+∑ i, K i)) := by
  let U := (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∩ (projectiveProductGraphChart (twistedProjectiveDimensions K h) G).source
  let H : Unit → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun _ => G
  have he : U = projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F H := by
    ext P; simp [U, H, projectiveProductGraphIntersection]
  let e := (Homeomorph.setCongr he).trans (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F H)
  change restrictedPairHomologyMap (fun z hz => hz.1 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h F) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl _ =
    restrictedPairHomologyMap (fun z hz => hz.2 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h G) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl _
  rw [twistedGraphBundleNormalization_restrict K h inter_subset_left e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl,
    twistedGraphBundleNormalization_restrict K h inter_subset_right e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl]
  exact twistedGraphBundleNormalization_affine_eq K h U (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F H)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F H) e F G inter_subset_left inter_subset_right hp

/-- All finite nonempty intersections of the total-space graph charts
have the required lower relative vanishing. -/
theorem twistedGraphBundleChartIntersection_below_isZero
    (T : Finset (∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))) (ht : T.Nonempty)
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set ↥(⋂ F ∈ T, twistedGraphBundleChartDomain K h F))) q) := by
  classical
  obtain ⟨F,hF⟩ := ht
  let G : T → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun t => t.val
  have he : (⋂ H ∈ T, twistedGraphBundleChartDomain K h H) =
      twistedGraphBundleDomain K h (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F G) := by
    ext z
    simp only [mem_iInter]
    change (∀ H, H ∈ T → z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) H).source) ↔
      z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∧
        z.proj ∈ ⋂ t : T, (projectiveProductGraphChart (twistedProjectiveDimensions K h) (G t)).source
    rw [mem_iInter]
    exact ⟨fun h => ⟨h F hF,fun t => h t.val t.property⟩,
      fun h H hH => h.2 ⟨H,hH⟩⟩
  rw [he]
  exact twistedGraphBundleIntersection_below_isZero K h F G hp q hq

/-- A genuine normalization on the WHOLE actual twisted bundle pair,
agreeing with the normalization on any preselected graph chart. -/
theorem twistedHyperplaneBundle_exists_global_normalization
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (nonzeroBundle : Set (TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
          (twistedHyperplaneSumCore K h).Fiber))) (2*(h+∑ i, K i)) ⟶
        relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)))
          (2*(h+∑ i, K i)),
      restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F₀) nonzeroBundle
          (2*(h+∑ i, K i)) ≫ f = twistedGraphBundleChartNormalization K h F₀ (2*(h+∑ i, K i)) := by
  classical
  obtain ⟨S,hF₀,hS⟩ := projectiveProduct_finiteGraphCover (twistedProjectiveDimensions K h) F₀
  have hopen : ∀ F ∈ S, IsOpen (twistedGraphBundleChartDomain K h F) :=
    fun F _ => (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).open_source.preimage (FiberBundle.continuous_proj _ _)
  have hcover : (⋃ F ∈ S, twistedGraphBundleChartDomain K h F) = univ := by
    ext z
    have hz : z.proj ∈ ⋃ F ∈ S, (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source := by
      rw [hS]; trivial
    simpa only [mem_iUnion, twistedGraphBundleChartDomain, twistedGraphBundleDomain,
      mem_ofPred_eq, mem_univ, iff_true] using hz
  let n := 2*(h+∑ i, K i)-1
  have hn : n+1 = 2*(h+∑ i, K i) := by dsimp [n]; omega
  have hex := finiteRelativeOpenCover_exists_glue S (twistedGraphBundleChartDomain K h)
    nonzeroBundle hopen hcover n
    (fun T ht _ q hq => twistedGraphBundleChartIntersection_below_isZero K h T ht hp q (by omega))
    (fun F => twistedGraphBundleChartNormalization K h F (n+1))
    (fun F _ G _ => by rw [hn]; exact twistedGraphBundleChartNormalization_compatible K h F G hp)
  rw [hn] at hex
  obtain ⟨f,hf⟩ := hex
  exact ⟨f,hf F₀ hF₀⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Survival of hyperplane fiber classes and nonvanishing Thom obstructions. -/

open Bundle Topology CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem retainedTest_hyperplaneDegree_pos {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    0 < ∑ i : Fin R, testProjectiveDimension m R i := by
  have : Nonempty (Fin R) := ⟨⟨0,hR⟩⟩
  exact Finset.sum_pos (fun i _ => testProjectiveDimension_pos hm i) Finset.univ_nonempty

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
private theorem sectionProductNormalization
    {X Y A V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (s : C(X,Y)) (hs : MapsTo s U W)
    (e : Y ≃ₜ A × V) (f : X ≃ₜ V)
    (he : ∀ y, y ∈ W ↔ (e y).2 ≠ 0) (hf : ∀ x, x ∈ U ↔ f x ∈ ({0}ᶜ : Set V))
    (hcoords : ∀ x, (e (s x)).2 = f x) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W s hs) (TopCat.ofHom s) (subspaceMap_square U W s hs) n ≫
      ((relativeHomologyHomeomorphIso e W {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso f U ({0}ᶜ : Set V) hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp]
  exact relativeHomologyMap_congr_ambient _ _ _ _ _ _ _ _ (by
    ext x : 1
    exact hcoords x) n

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

theorem twistedStandardBundleCoordinates_section (P : (twistedStandardChart K h).source) :
    twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl
      (twistedRestrictedSection K h P) =
    (twistedStandardChartHomeomorph K h P,
      twistedSlopeEvaluationEquiv K h (twistedStandardChartHomeomorph K h P)) := by
  apply Prod.ext
  · rfl
  let A := twistedStandardChartHomeomorph K h P
  have hP : P.1 = canonicalProductGraphPoint (twistedProjectiveDimensions K h) A := by
    change P.1 = ((twistedStandardChartHomeomorph K h).symm
      (twistedStandardChartHomeomorph K h P)).val
    rw [Homeomorph.symm_apply_apply]
  change (fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h P.1) s / (show ℂ from twistedStandardLineUnit K h s A)) = _
  rw [hP]
  exact twistedStandardSectionCoordinates_eq K h A

theorem twistedRestrictedSection_normalization (n : ℕ) :
    twistedRestrictedSectionRelativeMap K h n ≫
      twistedGraphBundleNormalization K h (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n =
      (twistedLocalSectionRelativeIso K h n).hom := by
  apply sectionProductNormalization
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ)
    (Subtype.val ⁻¹' nonzeroBundle) (twistedRestrictedSection K h) _
    (twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl)
    (twistedLocalSectionHomeomorph K h)
  intro P
  exact congrArg Prod.snd (twistedStandardBundleCoordinates_section K h P)

theorem twistedGraphBundleChartNormalization_isIso
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :
    IsIso (twistedGraphBundleChartNormalization K h F n) := by
  let e := twistedGraphBundleRelativeIso K h
    (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n
  let f := productPairProjection (B := ProjectiveProductModel (twistedProjectiveDimensions K h))
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n
  change IsIso (e.hom ≫ f)
  exact IsIso.comp_isIso' e.isIso_hom (productPairProjection_isIso _ _)

theorem twistedGraphBundleChartToAmbient_mono
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    Mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i))) := by
  obtain ⟨f,hf⟩ := twistedHyperplaneBundle_exists_global_normalization K h F hp
  have : IsIso (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ f) := by
    rw [hf]
    exact twistedGraphBundleChartNormalization_isIso K h F _
  exact mono_of_mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
    nonzeroBundle (2*(h+∑ i, K i))) f

theorem twistedProjectiveDimensions_sum :
    ∑ i, twistedProjectiveDimensions K h i = h+∑ i, K i := by
  rw [Fintype.sum_option]
  rfl

theorem twistedOrdinaryRelativeMap_chart (n : ℕ) :
    canonicalChartRelativeInclusion (twistedProjectiveDimensions K h) n ≫
      twistedOrdinaryRelativeMap K h n =
    twistedRestrictedSectionRelativeMap K h n ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
  unfold canonicalChartRelativeInclusion twistedOrdinaryRelativeMap twistedRestrictedSectionRelativeMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp,relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem twistedOrdinaryRelativeMap_mono (hp : 0 < h+∑ i, K i) :
    Mono (twistedOrdinaryRelativeMap K h (2*(h+∑ i, K i))) := by
  let n := 2*(h+∑ i, K i)
  let e := canonicalChartExcisionIso (twistedProjectiveDimensions K h) n
  let r := twistedRestrictedSectionRelativeMap K h n
  let f := twistedGraphBundleNormalization K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n
  have : IsIso (r ≫ f) := by
    change IsIso (twistedRestrictedSectionRelativeMap K h n ≫ _)
    rw [twistedRestrictedSection_normalization]
    infer_instance
  have : Mono r := mono_of_mono r f
  have : Mono (restrictedPairToAmbientHomologyMap
      (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n) :=
    twistedGraphBundleChartToAmbient_mono K h (twistedStandardFrames K h) hp
  have he : twistedOrdinaryRelativeMap K h n = e.inv ≫ r ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc,← Category.assoc,e.hom_inv_id,Category.id_comp]
    exact twistedOrdinaryRelativeMap_chart K h n
  change Mono (twistedOrdinaryRelativeMap K h n)
  rw [he]
  infer_instance

theorem twistedOrdinaryRelativeMap_comparison (n : ℕ) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct (twistedProjectiveDimensions K h)}ᶜ :
        Set (ProjectiveProduct (twistedProjectiveDimensions K h)))) n ≫
      twistedOrdinaryRelativeMap K h n =
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) n :=
  absoluteToRelative_naturality _ _ _ _ _ n

/-- The actual twisted section carries the existing augmented-base
fundamental class to a nonzero ordinary relative class. -/
theorem twistedOrdinarySection_fundamental_ne_zero
    (hp : 0 < ∑ i, twistedProjectiveDimensions K h i) :
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) (2*∑ i, twistedProjectiveDimensions K h i)
      (projectiveProductFundamentalClass (twistedProjectiveDimensions K h) hp) ≠ 0 := by
  have hp' : 0 < h+∑ i, K i := by rwa [twistedProjectiveDimensions_sum] at hp
  have : Mono (twistedOrdinaryRelativeMap K h (2*∑ i, twistedProjectiveDimensions K h i)) := by
    rw [twistedProjectiveDimensions_sum]
    exact twistedOrdinaryRelativeMap_mono K h hp'
  rw [← twistedOrdinaryRelativeMap_comparison]
  change twistedOrdinaryRelativeMap K h _
    (absoluteToRelative _ _ (projectiveProductFundamentalClass _ hp)) ≠ 0
  rw [projectiveProductFundamentalClass_localizes]
  intro hz
  exact canonicalProductLocalGenerator_ne_zero (twistedProjectiveDimensions K h) hp
    ((ModuleCat.mono_iff_injective (twistedOrdinaryRelativeMap K h _)).mp
      inferInstance (hz.trans (map_zero _).symm))

theorem twistedHyperplane_every_section_has_zero (hp : 0 < h+∑ i, K i)
    (s : ∀ P, (twistedHyperplaneSumCore K h).Fiber P)
    (hs : Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P (s P))) :
    ∃ P, s P = 0 := by
  have hp' : 0 < ∑ i, twistedProjectiveDimensions K h i := by
    rw [twistedProjectiveDimensions_sum]; exact hp
  by_contra hn
  push Not at hn
  have hz := ordinarySectionClassMap_eq_zero s hs hn (2*∑ i, twistedProjectiveDimensions K h i)
  have he := @ordinarySectionClassMap_eq _ (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    _ _ _ (twistedHyperplaneSumCore K h).Fiber _ _ _
    (twistedHyperplaneSumCore K h).fiberBundle (twistedHyperplaneSumCore K h).vectorBundle
    (twistedHyperplaneSection K h) s (continuous_twistedHyperplaneSection K h) hs
    (2*∑ i, twistedProjectiveDimensions K h i)
  have hz := he.trans hz
  apply twistedOrdinarySection_fundamental_ne_zero K h hp'
  rw [hz]
  rfl

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The tensor construction contradicts any frame with more vectors than
the displayed trivial rank. The frame need not respect the line summands. -/
theorem twistedSourceStage_no_large_frame {ι : Type} [Fintype ι]
    (K : ι → ℕ) (h d : ℕ) (hp : 0 < h+∑ i, K i) (hd : h < d) :
    IsEmpty (ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) := by
  refine ⟨fun f => ?_⟩
  have hd' : 1+h ≤ d := by omega
  obtain ⟨P,hP⟩ := twistedHyperplane_every_section_has_zero K h hp
    (twistedFrameSection K h f hd') (continuous_twistedFrameSection K h f hd')
  exact twistedFrameSection_ne_zero K h f hd' P hP

theorem retainedGrouped_no_test_frame_oai {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    IsEmpty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0)) := by
  have hp := retainedTest_hyperplaneDegree_pos hm hR
  have := twistedSourceStage_no_large_frame (testProjectiveDimension m R)
    (retainedTrivialMultiplicity m R) (2*m*testRank m R 0) (by omega)
    (retainedTrivialMultiplicity_bound hm)
  exact ⟨fun f => isEmptyElim (f.congr (retainedTwistedSourceUnitary m R).symm)⟩

end Kaplansky

end

end OAI
end

theorem solution : type_of% @OAI.Kaplansky.retainedGrouped_no_test_frame_oai := @OAI.Kaplansky.retainedGrouped_no_test_frame_oai
