-- Prove2me | solution 1 for GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:39.343395+00:00
-- url     : https://prove2.me/submissions/47effa57-91b2-459e-9525-02edf13f6d63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducible
import Theorems.Thm_GlobalTheory_affineOpen_fromSpec_mem_basicOpen_iff
import Theorems.Thm_GlobalTheory_T_exists_basicOpen_fibres_preirreducible_smooth
import Theorems.Thm_P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2
import Theorems.Thm_P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X),
    Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)),
      V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧
      ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  intro X S f e hf hef s
  obtain ⟨V, W, hWV, hV, hW, hes, hirr⟩ := GlobalTheory.T.exists_affine_chart_preirreducible_fiber' X S f e hf hef s
  have hfes : f (e s) = s := by rw [← Scheme.Hom.comp_apply, hef]; rfl
  have hsV : s ∈ V := by have h := hWV hes; rwa [Scheme.Hom.mem_preimage, hfes] at h
  letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have hsm : Algebra.Smooth Γ(S, V) Γ(X, W) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.appLE @Smooth f hf ⟨V, hV⟩ ⟨W, hW⟩ hWV)

  have hcomap : ∀ (x : X) (hxW : x ∈ W) (hxV : f x ∈ V),
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) =
        (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal := fun x hxW hxV =>
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW)
  have hfx : ∀ r : Spec Γ(X, W), f (hW.fromSpec r) =
      hV.fromSpec (Spec.map (f.appLE V W hWV) r) := fun r => by
    show (hW.fromSpec ≫ f) r = (Spec.map (f.appLE V W hWV) ≫ hV.fromSpec) r
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]
  set q := hW.primeIdealOf ⟨e s, hes⟩ with hqdef
  set p₀ := hV.primeIdealOf ⟨s, hsV⟩ with hp₀def
  have hq : q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = p₀.asIdeal := by
    rw [hqdef, hcomap (e s) hes (hWV hes)]
    congr 2; exact Subtype.ext hfes
  let Ω := AlgebraicClosure p₀.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap Γ(S, V) Ω) = p₀.asIdeal := by
    rw [IsScalarTower.algebraMap_eq Γ(S, V) p₀.asIdeal.ResidueField Ω, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p₀.asIdeal.ResidueField Ω).injective]
    exact Ideal.ker_algebraMap_residueField _
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) ≫ hV.fromSpec)
      (IsLocalRing.closedPoint Ω) = s := by
    have : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω) = p₀ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Γ(S, V) Ω) (IsLocalRing.maximalIdeal Ω) = p₀.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    show hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω)) = s
    rw [this, hp₀def, hV.fromSpec_primeIdealOf]
  have h1 := hirr Ω _ hpt
  have h2 := GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' X S f V W hWV hV hW Ω rfl h1
  obtain ⟨b, a, I, hb, ha, hI, hmain⟩ := GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth Γ(S, V) Γ(X, W) hsm q Ω (hq.trans hker.symm) h2
  refine ⟨X.basicOpen b, S.basicOpen a, V, I, S.basicOpen_le a, ?_, ?_, ?_, ?_⟩
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hV a p₀).mpr (by rw [← hq]; exact ha)
    rwa [hp₀def, hV.fromSpec_primeIdealOf] at h
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hW b q).mpr hb
    rwa [hqdef, hW.fromSpec_primeIdealOf] at h
  · intro c hc hsc
    have h := (affineOpen_fromSpec_mem_basicOpen_iff hV c p₀).mp
      (by rw [hp₀def, hV.fromSpec_primeIdealOf]; exact hsc)
    exact h (by rw [← hq]; exact hI c hc)
  · intro t htV₀ htI
    have htV : t ∈ V := S.basicOpen_le a htV₀
    set t' := hV.primeIdealOf ⟨t, htV⟩ with ht'def
    have hft' : hV.fromSpec t' = t := hV.fromSpec_primeIdealOf _
    have ha' : a ∉ t'.asIdeal :=
      (affineOpen_fromSpec_mem_basicOpen_iff hV a t').mp (by rw [hft']; exact htV₀)
    have hc' : ∀ c ∈ I, c ∈ t'.asIdeal := fun c hc => by
      by_contra hnc
      exact htI c hc (hft' ▸ (affineOpen_fromSpec_mem_basicOpen_iff hV c t').mpr hnc)
    have hZ := hmain t' ha' hc'
    have heq : ((X.basicOpen b : X.Opens) : Set X) ∩ f ⁻¹' {t} = hW.fromSpec ''
        {r : PrimeSpectrum Γ(X, W) | r.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = t'.asIdeal ∧
          b ∉ r.asIdeal} := by
      ext x
      constructor
      · rintro ⟨hxU, hxt⟩
        have hxW : x ∈ W := X.basicOpen_le b hxU
        have hxt' : f x = t := hxt
        refine ⟨hW.primeIdealOf ⟨x, hxW⟩, ⟨?_, ?_⟩, hW.fromSpec_primeIdealOf _⟩
        · rw [hcomap x hxW (hWV hxW), ht'def]
          congr 2; exact Subtype.ext hxt'
        · exact (affineOpen_fromSpec_mem_basicOpen_iff hW b _).mp
            (by rw [hW.fromSpec_primeIdealOf]; exact hxU)
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        refine ⟨(affineOpen_fromSpec_mem_basicOpen_iff hW b r).mpr hr2, ?_⟩
        show f (hW.fromSpec r) = t
        have : Spec.map (f.appLE V W hWV) r = t' := PrimeSpectrum.ext hr1
        rw [hfx, this, hft']
    rw [heq]
    exact hZ.image _ (Scheme.Hom.continuous _).continuousOn
end GlobalTheory
