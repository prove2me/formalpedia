-- Prove2me | solution 1 for OAI.ProductFiniteResolution.finite_free_resolution_of_products
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:51:47.590062+00:00
-- url     : https://prove2.me/submissions/c19c91bd-5e28-47e9-8f5a-ca640e5af4e0

import Mathlib
import Definitions.Def_OAIQ66So030

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolution
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PartialResolution.complex_projective _root_.OAI.PartialResolution.obj_projective _root_.OAI.PresentationGeometry.FiniteStage.cellSystem _root_.OAI.PresentationGeometry.FiniteStage.indexSystem _root_.OAI.PresentationGeometry.FiniteStage.mapSystem _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ProductFiniteResolution

open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidAlgebra

variable {k G : Type} [CommRing k] [Group G]

lemma kerRep_finite {C D : Rep k G} (f : C ⟶ D)
    (h : (ProductCriterion.moduleMap f).ker.FG) : Module.Finite k[G] (kerRep f).ρ.asModule := by
  let := Module.Finite.iff_fg.mpr h
  exact Module.Finite.equiv (kerAsModuleEquiv f).symm

attribute [instance] Beginning.finite₀ Beginning.finite₁ Beginning.finite₂ Beginning.epi_ε

variable {Z : Rep k G} (B : Beginning Z)

lemma degree_eq_free (n : ℕ) : (extendedComplex B).X n = Rep.free k G (degreeIndex B n) := by
  obtain (_ | _ | _ | n) := n
  · rfl
  · rfl
  · rfl
  · change next (ChainComplex.mkAux _ _ _ B.d₁ B.d₂ B.d₂_d₁
        (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩) n).f =
      next ((extendedComplex B).d (n + 2) (n + 1))
    have h := ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d
      (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
      B.d₁ B.d₂ B.d₂_d₁
      (fun S : ShortComplex (Rep k G) => ⟨next S.f, differential S.f, differential_comp S.f⟩) n
    change _ = next ((ShortComplex.mk _ _
      ((extendedComplex B).d_comp_d (n + 2) (n + 1) n)).f)
    exact congrArg (fun S : ShortComplex (Rep k G) => next S.f) h

lemma kerRep_finite_of_product_exact {U C D : Rep k G} (f : U ⟶ C) (g : C ⟶ D)
    (hfg : f ≫ g = 0) {α β : Type} [Finite α]
    (eC : C = Rep.free k G α) (eD : D = Rep.free k G β)
    (hex : ∀ I : Type, ((ShortComplex.mk f g hfg).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact) :
    Module.Finite k[G] (kerRep g).ρ.asModule := by
  cases eC
  cases eD
  apply kerRep_finite g
  apply ProductCriterion.kernel_fg_of_tensor_homology_zero U f g hfg
  intro I
  exact (ShortComplex.exact_iff_isZero_homology _).mp (hex I)

lemma degreeIndex_finite (B : Beginning (Rep.trivial k G k))
    (hzero : ∀ (I : Type) (n : ℕ), 2 ≤ n →
      IsZero (groupHomology (RegularProductR.rep k G I) n)) (n : ℕ) :
    Finite (degreeIndex B n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | _ | n) := n
    · exact B.finite₀
    · exact B.finite₁
    · exact B.finite₂
    · have : Finite (degreeIndex B (n + 2)) := ih (n + 2) (by omega)
      apply (freeCover _).finite_of
      apply kerRep_finite_of_product_exact
        ((extendedComplex B).d (n + 3) (n + 2))
        ((extendedComplex B).d (n + 2) (n + 1))
        ((extendedComplex B).d_comp_d _ _ _)
        (degree_eq_free B (n + 2)) (degree_eq_free B (n + 1))
      intro I
      have he := ProductCriterion.product_resolution_exact (resolution B) (n + 2)
        (fun J => hzero J (n + 2) (by omega)) I
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)] at he
      exact he

theorem exists_finite_free_resolution (B : Beginning (Rep.trivial k G k))
    (hzero : ∀ (I : Type) (n : ℕ), 2 ≤ n →
      IsZero (groupHomology (RegularProductR.rep k G I) n)) :
    ∃ P : ProjectiveResolution (Rep.trivial k G k),
      ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free k G α) := by
  refine ⟨resolution B, fun n => ⟨degreeIndex B n, degreeIndex_finite B hzero n, ?_⟩⟩
  exact ⟨eqToIso (degree_eq_free B n)⟩

end ProductFiniteResolution

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.PresentationComplex.transported_simplyConnected _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry
open Set Topology
universe u
variable (G : Type u) [Group G]

theorem exists_word_presentation [Group.IsFinitelyPresented G] :
    ∃ (k r : ℕ) (w : Fin r → List (Fin k × Bool)),
      Nonempty (G ≃* PresentedGroup (PresentationComplex.relatorSet w)) := by
  classical
  obtain ⟨k,φ,hφ,S,hfin,hS⟩ := Group.IsFinitelyPresented.out (G := G)
  let := hfin.fintype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let w : Fin r → List (Fin k × Bool) := fun i => (e i).1.toWord
  have hw : PresentationComplex.relatorSet w = S := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      simpa only [w,FreeGroup.mk_toWord] using (e i).2
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      refine ⟨i,?_⟩
      change FreeGroup.mk (e i).1.toWord = x
      rw [FreeGroup.mk_toWord]
      exact congrArg Subtype.val hi
  refine ⟨k,r,w,?_⟩
  have hc : Subgroup.normalClosure (PresentationComplex.relatorSet w) = φ.ker := by
    rw [hw,hS]
  let q : PresentedGroup (PresentationComplex.relatorSet w) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact ⟨q.symm⟩

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.FiniteStage
section
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
lemma initialStage_exists [Group.IsFinitelyPresented Q] : Nonempty (Stage Q 0) := by
  obtain ⟨k,r,w,⟨e⟩⟩ := exists_word_presentation Q
  exact ⟨PresentationComplex.initialStage w e⟩
end

open Set Topology Metric
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolutionBeginningOfComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace ProductFiniteResolution
variable (G : Type) [Group G] [Group.IsFinitelyPresented G]
theorem beginning_exists : Nonempty (Beginning (Rep.trivial ℤ G ℤ)) := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  obtain ⟨S⟩ := PresentationGeometry.FiniteStage.initialStage_exists G
  exact ⟨PresentationGeometry.FiniteStage.algebraicBeginning S⟩

theorem finite_free_resolution_of_products_oai
    (hz : ∀ (I : Type) (n : ℕ), 2 ≤ n → IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    ∃ P : ProjectiveResolution (Rep.trivial ℤ G ℤ),
      ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free ℤ G α) := by
  obtain ⟨B⟩ := beginning_exists G
  exact exists_finite_free_resolution B hz
end ProductFiniteResolution

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end OrbitBrown

end

end OAI
end

theorem solution : type_of% @OAI.ProductFiniteResolution.finite_free_resolution_of_products_oai := @OAI.ProductFiniteResolution.finite_free_resolution_of_products_oai
