-- Prove2me | solution 1 for GlobalTheory.GermInterp.exists_germ_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:01.22511+00:00
-- url     : https://prove2.me/submissions/2c3a92ae-b266-47ec-adff-64c5fef51da1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsMaximalOfFinitePrimes
import Theorems.Thm_GlobalTheory_GermInterp_exists_sub_mem_map
import Theorems.Thm_GlobalTheory_GermInterp_mem_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
open GlobalTheory GlobalTheory.GermInterp
namespace GlobalTheory.GermInterp
theorem _root_.solution : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by
  intro K _ X p V J f a hft hV hfin
  let I : Ideal Γ(X, V) := Ideal.span (Set.range f)
  let Z := {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}
  have : Finite Z := hfin.to_subtype
  let P : Z → PrimeSpectrum Γ(X, V) := fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩
  have hIP : ∀ k, I ≤ (P k).asIdeal := by
    intro k
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)
  have hinj : Function.Injective P := by
    intro k k' e
    apply Subtype.ext
    have e1 := hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩
    have e2 := hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩
    have e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩ := e
    rw [e3] at e1
    exact e1.symm.trans e2
  have hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite := by
    refine (Set.finite_range P).subset ?_
    intro Q hQ
    have hyV : hV.fromSpec Q ∈ V := hV.range_fromSpec.le ⟨Q, rfl⟩
    have hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)
    refine ⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩
    have hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal := by
      rw [hQeq]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi
  have : IsJacobsonRing Γ(Sp K, ⊤) :=
    isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom,
      RingEquiv.surjective _⟩
  have : IsJacobsonRing Γ(X, V) :=
    RingHom.FiniteType.isJacobsonRing
      (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))
  letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) :=
    fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩
  have loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal :=
    fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)
  refine ⟨r, fun y hy hz => ?_⟩
  let k : Z := ⟨y, hy, hz⟩
  have hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g := by
    intro g
    rw [gs_eq (𝟙 X) y V hy g]
    rfl
  have hk := hr k
  rw [Ideal.map_span, ← Set.range_comp] at hk
  have e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f := by
    funext i
    exact hgs (f i)
  rw [e, hgs r]
  exact hk
end GlobalTheory.GermInterp
