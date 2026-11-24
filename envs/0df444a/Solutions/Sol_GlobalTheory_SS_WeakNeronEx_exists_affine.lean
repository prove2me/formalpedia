-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.exists_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:33.092928+00:00
-- url     : https://prove2.me/submissions/bc9c190b-5225-4e21-9022-fe0ba580f67d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_sp_comp
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_sp_inj
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_spMap_ev
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_fromSpec_hom
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_exists_chart
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_flat_sub
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_gen_injective
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_gen_surjective
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Sp K) (hf : IsProjBy f) :
    ∃ (m : ℕ) (B : Fin m → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (u : ∀ i, Sp (TensorProduct R K (B i)) ⟶ X),
      (∀ i, Algebra.FiniteType R (B i) ∧ Module.Flat R (B i) ∧ IsOpenImmersion (u i) ∧
        u i ≫ f = spMap (algebraMap K _)) ∧
      ∀ (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] [Field L] [Algebra V L]
        [IsFractionRing V L] (a : Sp L ⟶ X),
        a ≫ f ≫ spMap (algebraMap R K) = spMap ((algebraMap V L).comp (algebraMap R V)) →
        ∃ (i : Fin m) (b : B i →ₐ[R] V) (ψ : TensorProduct R K (B i) →+* L), spMap ψ ≫ u i = a ∧
          ∀ x, ψ (1 ⊗ₜ x) = algebraMap V L (b x) := by
  obtain ⟨H, -, m, s, hc, hs⟩ := hf
  choose haff r hr hsurj using hs
  letI : ∀ i, Algebra K Γ(X, nonzeroLocus (s i)) := fun i => (cst f _).toAlgebra
  letI : ∀ i, Algebra R Γ(X, nonzeroLocus (s i)) := fun i => ((cst f _).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K Γ(X, nonzeroLocus (s i)) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : ∀ i, TensorProduct R K (Algebra.adjoin R (Set.range (r i))) ≃ₐ[K] Γ(X, nonzeroLocus (s i)) := fun i =>
    AlgEquiv.ofBijective (gen R K _) ⟨gen_injective R K _, gen_surjective R K _ (hsurj i)⟩
  refine ⟨m + 1, fun i => Algebra.adjoin R (Set.range (r i)), inferInstance, inferInstance,
    fun i => spMap (e i).symm.toAlgHom.toRingHom ≫ (haff i).fromSpec, fun i => ⟨?_, flat_sub R K _, ?_, ?_⟩, ?_⟩
  · exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  · haveI : IsIso (spMap (e i).symm.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso (Spec.map (e i).symm.toRingEquiv.toCommRingCatIso.hom))
    infer_instance
  · rw [Category.assoc, fromSpec_hom, sp_comp]
    exact congrArg spMap ((e i).symm.toAlgHom.comp_algebraMap)
  · intro V L _ _ _ _ _ _ _ a ha
    obtain ⟨i, h, hi⟩ := exists_chart s hc r hr (V := V) a
    have h₁ := spMap_ev a (haff i) h
    have h₂ : (ev a _ h).comp (algebraMap R _) = (algebraMap V L).comp (algebraMap R V) := by
      apply sp_inj
      have h₀ : a ≫ f = spMap ((ev a _ h).comp (cst f _)) := by
        rw [← sp_comp, ← fromSpec_hom f (haff i), reassoc_of% h₁]
      rw [← ha, reassoc_of% h₀, sp_comp]
      rfl
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ : Γ(X, nonzeroLocus (s i)) →ₐ[R] L := ⟨ev a _ h, fun c => congrArg (fun q => q c) h₂⟩
    have hle : Algebra.adjoin R (Set.range (r i)) ≤ (IsScalarTower.toAlgHom R V L).range.comap φ := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hi j
    let κ := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V L) (IsFractionRing.injective V L)
    refine ⟨i, κ.symm.toAlgHom.comp ((φ.comp (Subalgebra.val _)).codRestrict _ fun x => hle x.2),
      (ev a _ h).comp (e i).toAlgHom.toRingHom, ?_, fun x => ?_⟩
    · rw [← Category.assoc, sp_comp]
      refine Eq.trans ?_ h₁
      congr 2
      ext y
      simp
    · have h₃ : ∀ y, algebraMap V L (κ.symm y) = y := fun y =>
        congrArg Subtype.val (κ.apply_symm_apply y)
      refine Eq.trans ?_ (h₃ _).symm
      have h₄ : gen R K (Algebra.adjoin R (Set.range (r i))) (1 ⊗ₜ x) = x.1 := by simp [gen]
      exact congrArg (ev a _ h) h₄
end GlobalTheory.SS.WeakNeronEx
