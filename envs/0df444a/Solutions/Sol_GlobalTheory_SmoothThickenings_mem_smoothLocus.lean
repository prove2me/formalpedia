-- Prove2me | solution 1 for GlobalTheory.SmoothThickenings.mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:57.963193+00:00
-- url     : https://prove2.me/submissions/6004fee4-8401-4858-9f40-c1d3f653eb6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothOfSmoothThickenings
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_SmoothLimit_mem_smoothLocus
import Theorems.Thm_GlobalTheory_T_isSmoothAt_of_smooth_mod_ideal_powers
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothThickenings
namespace GlobalTheory.SmoothThickenings
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤)
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V I e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW' : IsAffineOpen W := hW
  have hWle : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  set ψ := f.appLE ⊤ W hWle with hψ
  set φ : CommRingCat.of V ⟶ Γ(X, W) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ ψ with hφ
  let : Algebra V Γ(X, W) := φ.hom.toAlgebra
  have hjf : hW'.fromSpec ≫ f = Spec.map φ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW' hWle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, hφ, Spec.map_comp]
  have : Algebra.FiniteType V Γ(X, W) := by
    have h1 : ψ.hom.FiniteType := f.finiteType_appLE (isAffineOpen_top _) hW' hWle
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2
    exact h1.comp h2
  set p := hW'.primeIdealOf ⟨x, hxW⟩
  have hpx : hW'.fromSpec p = x := hW'.fromSpec_primeIdealOf ⟨x, hxW⟩
  have hcomap : p.asIdeal.comap (algebraMap V Γ(X, W)) = IsLocalRing.maximalIdeal V := by
    have h3 : (Spec.map φ) p = IsLocalRing.closedPoint V := by
      rw [← hjf]
      exact (congrArg f hpx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h3
  have hsm : ∀ e : ℕ, Algebra.Smooth (V ⧸ I ^ (e + 1))
      (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) := by
    intro e
    have hg : thick V I e = Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))) := by
      unfold thick
      rw [Ideal.Quotient.algebraMap_eq]
    have := h e
    have h3 : Smooth (pullback.snd (Spec.map φ) (thick V I e)) := by
      rw [← hjf, ← pullbackRightPullbackFstIso_inv_snd_snd f (thick V I e) hW'.fromSpec]
      have hA : IsOpenImmersion (pullback.snd hW'.fromSpec (pullback.fst f (thick V I e))) :=
        inferInstance
      exact MorphismProperty.comp_mem @Smooth _ _ inferInstance
        (MorphismProperty.comp_mem @Smooth _ _ inferInstance this)
    have h4 : Smooth ((pullbackSpecIso V Γ(X, W) (V ⧸ I ^ (e + 1))).inv ≫ pullback.snd _ _) := by
      have : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V Γ(X, W))))
          (Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))))) := by
        rw [← hg]
        exact h3
      infer_instance
    rw [pullbackSpecIso_inv_snd] at h4
    have h5 := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h4
    have h6 := RingHom.Smooth.propertyIsLocal.respectsIso.1 _
      (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv h5
    have heq : algebraMap (V ⧸ I ^ (e + 1)) (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) =
        (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : (V ⧸ I ^ (e + 1)) →ₐ[V] _).toRingHom := by
      ext t
      simp
    rw [← RingHom.smooth_algebraMap, heq]
    exact h6
  have hq : Algebra.IsSmoothAt V p.asIdeal := GlobalTheory.T.isSmoothAt_of_smooth_mod_ideal_powers V I hI Γ(X, W) hsm p.asIdeal hcomap
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) W hW' hWle hxW]
  let : Algebra Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) := ψ.hom.toAlgebra
  show Algebra.FormallySmooth Γ(Spec (CommRingCat.of V), ⊤) (Localization.AtPrime p.asIdeal)
  rw [← RingHom.formallySmooth_algebraMap]
  rw [Algebra.IsSmoothAt, ← RingHom.formallySmooth_algebraMap] at hq
  have e2 := RingHom.FormallySmooth.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv hq
  convert e2 using 1
  ext a
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) (Localization.AtPrime p.asIdeal),
    IsScalarTower.algebraMap_apply V Γ(X, W) (Localization.AtPrime p.asIdeal)]
  congr 1
  show ψ a = φ ((Scheme.ΓSpecIso (CommRingCat.of V)).hom a)
  rw [hφ, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
end GlobalTheory.SmoothThickenings
