-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ad2365bc-9ba7-50de-84d6-f4856a1a77c5

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict
import Theorems.Thm_MvPolynomial_CrossingQuotient_maximalIdeal_stalk_eq_span_germ_sub
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Theorems.Thm_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard"

open MvPolynomial

namespace CTKit
universe uu
variable {C X U M : Scheme.{uu}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)

noncomputable def Ψ (W : M.Opens) : Γ(M, W) →+* Γ(C, g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W))) :=
  (g.app (ι ''ᵁ (f ⁻¹ᵁ W))).hom.comp (((ι.appIso (f ⁻¹ᵁ W)).inv).hom.comp (f.app W).hom)

theorem Ψ_apply (W : M.Opens) (s : Γ(M, W)) : Ψ g ι f W s = g.app _ ((ι.appIso (f ⁻¹ᵁ W)).inv (f.app W s)) := rfl

theorem le_of_le {W W' : M.Opens} (h : W' ≤ W) : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W')) ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W)) :=
  g.preimage_mono (ι.image_mono (f.preimage_mono h))

theorem Ψ_res {W W' : M.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    Ψ g ι f W' (M.presheaf.map (homOfLE h).op s) = C.presheaf.map (homOfLE (le_of_le g ι f h)).op (Ψ g ι f W s) := by
  rw [Ψ_apply, Ψ_apply]
  have e1 : f.app W' (M.presheaf.map (homOfLE h).op s) = U.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W s) := by
    show (M.presheaf.map (homOfLE h).op ≫ f.app W') s = _
    rw [Scheme.Hom.naturality]; rfl
  have e2 : (ι.appIso (f ⁻¹ᵁ W')).inv (U.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W s)) =
      X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op ((ι.appIso (f ⁻¹ᵁ W)).inv (f.app W s)) := by
    show (U.presheaf.map (homOfLE (f.preimage_mono h)).op ≫ (ι.appIso (f ⁻¹ᵁ W')).inv) _ = _
    rw [Scheme.Hom.appIso_inv_naturality]
    rfl
  have e3 : ∀ y, g.app (ι ''ᵁ (f ⁻¹ᵁ W')) (X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op y) =
      C.presheaf.map (homOfLE (le_of_le g ι f h)).op (g.app (ι ''ᵁ (f ⁻¹ᵁ W)) y) := fun y => by
    show (X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op ≫ g.app _) y = _
    rw [Scheme.Hom.naturality]; rfl
  rw [e1, e2, e3]

theorem Ψ_top_of_app_top (y : Γ(X, ⊤)) (s : Γ(M, ⊤)) (hs : f.app ⊤ s = ι.appTop y) :
    Ψ g ι f ⊤ s = C.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op (g.appTop y) := by
  rw [Ψ_apply, hs]
  have e2 : (ι.appIso (f ⁻¹ᵁ ⊤)).inv (ι.appTop y) = X.presheaf.map (homOfLE (ι.image_le_opensRange _ |>.trans le_top)).op y := by
    show (ι.app ⊤ ≫ (ι.appIso (ι ⁻¹ᵁ ⊤)).inv) y = _
    rw [Scheme.Hom.app_appIso_inv]
    rfl
  rw [e2]
  show (X.presheaf.map _ ≫ g.app _) y = _
  rw [Scheme.Hom.naturality]
  rfl

theorem appTop_SpecMap {R S : CommRingCat.{uu}} (ψ : R ⟶ S) (r : R) :
    (Spec.map ψ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (ψ r) := by
  have h := Scheme.ΓSpecIso_inv_naturality ψ
  calc (Spec.map ψ).appTop ((Scheme.ΓSpecIso R).inv r) = ((Scheme.ΓSpecIso R).inv ≫ (Spec.map ψ).appTop) r := rfl
    _ = (ψ ≫ (Scheme.ΓSpecIso S).inv) r := by rw [h]
    _ = (Scheme.ΓSpecIso S).inv (ψ r) := rfl

end CTKit

namespace GIKit

theorem natCast_mem_maximalIdeal {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  have h : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have hmem : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := A.nonunits_le h
  have h' := (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, hmem⟩ : ↥A))).mp h
  have e : (⟨((p : ℕ) : AlgebraicClosure ℚ), hmem⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
  rwa [e] at h'

theorem exists_pow_natCast_mem_span {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (b : ↥A) (hb : b ≠ 0) : ∃ n : ℕ, ((p : ℕ) : ↥A) ^ n ∈ Ideal.span {b} := by
  classical
  have hpm := natCast_mem_maximalIdeal A hA
  have hmemrad : ((p : ℕ) : ↥A) ∈ (Ideal.span {b}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hbP, hP⟩
    by_cases hPm : P = IsLocalRing.maximalIdeal ↥A
    · rw [hPm]; exact hpm
    · exfalso
      have hbot := ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime hp.out A hA P hPm
      have hbmem : b ∈ P := hbP (Ideal.subset_span rfl)
      rw [hbot, Ideal.mem_bot] at hbmem
      exact hb hbmem
  exact hmemrad

theorem isLocalization_away_natCast {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsLocalization.Away (((p : ℕ) : ↥A)) (AlgebraicClosure ℚ) := by
  classical
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ (IsUnit.mk0 _ (by rw [map_natCast]; exact_mod_cast hp.out.ne_zero))
  · intro z
    by_cases hz : z ∈ A
    · exact ⟨(⟨z, hz⟩, 1), by simp⟩
    · have hzi : z⁻¹ ∈ A := (A.mem_or_inv_mem z).resolve_left hz
      have hz0 : z ≠ 0 := by rintro rfl; exact hz A.zero_mem
      have hb0 : (⟨z⁻¹, hzi⟩ : ↥A) ≠ 0 := by
        intro h; apply hz0; have := congrArg Subtype.val h; simpa using this
      obtain ⟨n, hn⟩ := exists_pow_natCast_mem_span A hA ⟨z⁻¹, hzi⟩ hb0
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
      refine ⟨(c, ⟨((p : ℕ) : ↥A) ^ n, n, rfl⟩), ?_⟩

      have hc' : (c : AlgebraicClosure ℚ) * z⁻¹ = ((p : ℕ) : AlgebraicClosure ℚ) ^ n := by
        have := congrArg (fun a : ↥A => (a : AlgebraicClosure ℚ)) hc
        simpa using this
      show z * algebraMap ↥A (AlgebraicClosure ℚ) (((p : ℕ) : ↥A) ^ n) = algebraMap ↥A (AlgebraicClosure ℚ) c
      rw [map_pow, map_natCast, ← hc']
      show z * ((c : AlgebraicClosure ℚ) * z⁻¹) = (c : AlgebraicClosure ℚ)
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
  · intro a b h
    exact ⟨1, by simpa using Subtype.ext h⟩

theorem isOpenImmersion_subtype {p : ℕ} [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom A.subtype)) := by
  haveI := isLocalization_away_natCast A hA
  exact IsOpenImmersion.of_isLocalization (S := AlgebraicClosure ℚ) ((p : ℕ) : ↥A)

end GIKit

namespace PsiKit
open Opposite TopologicalSpace

universe u

theorem map_maximalIdeal_of_surjective {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (θ : R ⟶ S) [IsLocalHom θ.hom] (hθ : Function.Surjective θ.hom) :
    Ideal.map θ.hom (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  have h := Ideal.map_eq_top_or_isMaximal_of_surjective θ.hom hθ (IsLocalRing.maximalIdeal.isMaximal R)
  rcases h with h | h
  · exact absurd h (ne_of_lt (lt_of_le_of_lt (IsLocalRing.map_maximalIdeal_le θ.hom) (lt_top_iff_ne_top.mpr
      (Ideal.IsMaximal.ne_top inferInstance))))
  · exact IsLocalRing.eq_maximalIdeal h

theorem surjective_of_isIso {R S : CommRingCat.{u}} (θ : R ⟶ S) [IsIso θ] : Function.Surjective θ.hom := by
  intro s
  refine ⟨(inv θ).hom s, ?_⟩
  change (inv θ ≫ θ).hom s = s
  rw [IsIso.inv_hom_id]
  rfl

theorem injective_of_isIso {R S : CommRingCat.{u}} (θ : R ⟶ S) [IsIso θ] : Function.Injective θ.hom := by
  intro a b h
  have := congrArg (inv θ).hom h
  change (θ ≫ inv θ).hom a = (θ ≫ inv θ).hom b at this
  rwa [IsIso.hom_inv_id] at this

theorem span_map_eq_maximalIdeal {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (θ : R ⟶ S) [IsLocalHom θ.hom] (hθ : Function.Surjective θ.hom) (g : R)
    (h : Ideal.span {g} = IsLocalRing.maximalIdeal R) :
    Ideal.span {θ.hom g} = IsLocalRing.maximalIdeal S := by
  rw [← map_maximalIdeal_of_surjective θ hθ, ← h, Ideal.map_span, Set.image_singleton]

theorem span_eq_maximalIdeal_of_isIso {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (θ : R ⟶ S) [IsIso θ] (g : R)
    (h : Ideal.span {θ.hom g} = IsLocalRing.maximalIdeal S) :
    Ideal.span {g} = IsLocalRing.maximalIdeal R := by
  haveI : IsLocalHom (inv θ).hom := isLocalHom_of_isIso _
  have hg : g = (inv θ).hom (θ.hom g) := by
    change g = (θ ≫ inv θ).hom g
    rw [IsIso.hom_inv_id]; rfl
  rw [hg]
  exact span_map_eq_maximalIdeal (inv θ) (surjective_of_isIso _) _ h

theorem stalkMap_injective_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

theorem stalkMap_injective_of_etale_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens)
    [AlgebraicGeometry.Etale (W.ι ≫ f)] (x : X) (hx : x ∈ W) :
    Function.Injective (f.stalkMap x).hom := by
  have key : ∀ w : (W : Scheme.{u}), Function.Injective (f.stalkMap (W.ι w)).hom := by
    intro w
    have h := stalkMap_injective_of_flat (W.ι ≫ f) w
    rw [Scheme.Hom.stalkMap_comp] at h
    intro a b hab
    apply h
    change (W.ι.stalkMap w).hom ((f.stalkMap (W.ι w)).hom a) = (W.ι.stalkMap w).hom ((f.stalkMap (W.ι w)).hom b)
    rw [hab]
  exact key ⟨x, hx⟩

section model
variable {A : Type u} [CommRing A] [IsDomain A]

open TrivSqZeroExt in
theorem mul_U_sub_ne_zero (t xv yv : A) (hxv : xv * yv = algebraMap A A t) (hx : xv ≠ 0)
    (s : CrossingQuotient A t) (hs : s ∉ RingHom.ker (CrossingQuotient.lift (t := t) xv yv hxv).toRingHom) :
    s * (CrossingQuotient.U t - algebraMap A (CrossingQuotient A t) xv) ≠ 0 := by
  classical
  let K := FractionRing A
  let D := TrivSqZeroExt K K
  let x : K := algebraMap A K xv
  let y : K := algebraMap A K yv
  have hx' : algebraMap A (FractionRing A) xv ≠ 0 := fun h => hx ((IsFractionRing.injective A K) (by rw [map_zero]; exact h))
  let a : D := inl x + inr 1
  let b : D := inl y - inr (y / x)
  have hab : a * b = algebraMap A D t := by
    have ht : algebraMap A K t = x * y := by
      rw [← map_mul, hxv]; rfl
    rw [TrivSqZeroExt.algebraMap_eq_inl', ht]
    ext
    · simp [K, D, x, y, a, b, fst_mul]
    · simp [K, D, x, y, a, b, snd_mul]
      rw [mul_div_cancel₀ _ hx', neg_add_cancel]
  let g : CrossingQuotient A t →ₐ[A] D := CrossingQuotient.lift (t := t) a b hab
  let L := CrossingQuotient.lift (t := t) xv yv hxv
  have hfg : ((TrivSqZeroExt.fstHom A K K).comp g : CrossingQuotient A t →ₐ[A] K) =
      (Algebra.ofId A K).comp L := by
    apply CrossingQuotient.algHom_ext_chart
    · simp [K, D, g, L, a, Algebra.ofId_apply, x]
    · simp [K, D, g, L, b, Algebra.ofId_apply, x, y]
  intro h0
  have h1 := congrArg g h0
  rw [map_mul, map_sub, map_zero, AlgHom.commutes, CrossingQuotient.lift_U, TrivSqZeroExt.algebraMap_eq_inl'] at h1
  have h2 : (g s).fst = 0 := by
    have := congrArg TrivSqZeroExt.snd h1
    simpa [K, D, a, snd_mul, x] using this
  have h3 : algebraMap A K (L s) = 0 := by
    have := congrArg (fun φ : CrossingQuotient A t →ₐ[A] K => φ s) hfg
    simp only [AlgHom.comp_apply, Algebra.ofId_apply] at this
    rw [← this]
    exact h2
  apply hs
  rw [RingHom.mem_ker]
  exact (IsFractionRing.injective A K) (by rw [map_zero]; exact h3)

theorem germ_U_sub_ne_zero (t xv yv : A) (hxv : xv * yv = algebraMap A A t) (hx : xv ≠ 0)
    (m : Spec (CommRingCat.of (CrossingQuotient A t)))
    (hm : m.asIdeal = RingHom.ker (CrossingQuotient.lift (t := t) xv yv hxv).toRingHom) :
    (Spec (CommRingCat.of (CrossingQuotient A t))).presheaf.germ ⊤ m trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient A t))).inv
        (CrossingQuotient.U t - algebraMap A (CrossingQuotient A t) xv)) ≠ 0 := by
  intro h0
  set q : CrossingQuotient A t := CrossingQuotient.U t - algebraMap A (CrossingQuotient A t) xv
  have h1 : StructureSheaf.toStalk (CrossingQuotient A t) m q = 0 := by
    rw [← StructureSheaf.algebraMap_germ_apply ⊤ m trivial]
    exact h0
  have h2 : algebraMap (CrossingQuotient A t) ((Spec.structureSheaf (CrossingQuotient A t)).presheaf.stalk m) q = 0 := h1
  rw [IsLocalization.map_eq_zero_iff m.asIdeal.primeCompl] at h2
  obtain ⟨⟨s, hs⟩, hsq⟩ := h2
  have hs' : s ∉ m.asIdeal := hs
  rw [hm] at hs'
  exact mul_U_sub_ne_zero t xv yv hxv hx s hs' hsq

end model

theorem specMap_base_asIdeal {R S : CommRingCat.{u}} (f : R ⟶ S) (x : Spec S) :
    ((Spec.map f).base x).asIdeal = Ideal.comap f.hom x.asIdeal := rfl

theorem asIdeal_eq_bot_of_field {K : Type u} [Field K] (y : Spec (CommRingCat.of K)) : y.asIdeal = ⊥ :=
  Ideal.eq_bot_of_prime _

end PsiKit

namespace PsiKit

theorem key
    {A : Type} [CommRing A] [Algebra A (AlgebraicClosure ℚ)]
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of A)) [IsSeparated c]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : A →+* ↥Pl)
    (gq : pullback c (specMap A (AlgebraicClosure ℚ)) ⟶ pullback c (Spec.map (CommRingCat.ofHom ρ))) [IsOpenImmersion gq]
    (hgq_snd : gq ≫ pullback.snd c (Spec.map (CommRingCat.ofHom ρ)) =
      pullback.snd c (specMap A (AlgebraicClosure ℚ)) ≫ Spec.map (CommRingCat.ofHom Pl.subtype))
    [hY : IsIntegral (pullback c (specMap A (AlgebraicClosure ℚ)))]
    (yb : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) c)
    (tt : ↥Pl)
    (U : (pullback c (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme tt)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl tt))) =
      U.ι ≫ pullback.snd _ _)
    (Wet : (U : Scheme.{0}).Opens) [AlgebraicGeometry.Etale (Wet.ι ≫ f)]
    (sV sV' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0}))
    (hsV : sV ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsV' : sV' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsWV : sV.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet)
    (hP : graphOver c yb.1 yb.2 ≫ gq = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sV ≫ U.ι)
    (xv yv xv' yv' : ↥Pl)
    (hxv : xv * yv = algebraMap ↥Pl ↥Pl tt)
    (hxv' : xv' * yv' = algebraMap ↥Pl ↥Pl tt)
    (hxv0 : xv ≠ 0)
    (hfsV : sV ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tt) xv yv hxv).toRingHom))
    (hfsV' : sV' ≫ f = Spec.map (CommRingCat.ofHom
      (CrossingQuotient.lift (t := tt) xv' yv' hxv').toRingHom))
    (huqV : sV' ≫ f = sV ≫ f → sV' = sV) :
    letI X : Scheme.{0} := pullback c (Spec.map (CommRingCat.ofHom ρ))
    letI Y : Scheme.{0} := pullback c (specMap A (AlgebraicClosure ℚ))
    letI Q := CrossingQuotient ↥Pl tt
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI av : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q xv)
    ∀ (O' : Mdl.Opens),
      (∀ m ∈ O', (CrossingQuotient.U _ - algebraMap ↥Pl Q xv) ∉ m.asIdeal ∨
        (algebraMap ↥Pl Q yv - CrossingQuotient.V _) ∉ m.asIdeal) →
    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O') →
      (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sV ≫ U.ι).base ∧ z ∉ Set.range (sV' ≫ U.ι).base)) →
    ∀ (hWU : W₂ ≤ U.ι ''ᵁ ⊤),
    letI aX : Γ(X, W₂) := X.presheaf.map (homOfLE hWU).op ((U.ι.appIso ⊤).inv (f.appTop av))
    letI aY : Γ(Y, gq ⁻¹ᵁ W₂) := gq.app W₂ aX
    ∀ (U' : Y.affineOpens) (hU : (U' : Y.Opens) ≤ gq ⁻¹ᵁ W₂),
      (RelEffCartierDiv.ofPoint c yb.1 yb.2).I.ideal U' =
          Ideal.span {Y.presheaf.map (homOfLE hU).op aY} ∧
        Y.presheaf.map (homOfLE hU).op aY ∈ nonZeroDivisors Γ(Y, U') := by
  classical
  intro O' hO' W₂ W₃ hcov hW₂U hle hW₃ hWU U' hU

  let X : Scheme.{0} := pullback c (Spec.map (CommRingCat.ofHom ρ))
  let Y : Scheme.{0} := pullback c (specMap A (AlgebraicClosure ℚ))
  let Q := CrossingQuotient ↥Pl tt
  let Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
  let φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let q : (CrossingQuotient ↥Pl tt) := CrossingQuotient.U _ - algebraMap ↥Pl (CrossingQuotient ↥Pl tt) xv
  let r : (CrossingQuotient ↥Pl tt) := algebraMap ↥Pl (CrossingQuotient ↥Pl tt) yv - CrossingQuotient.V _
  let av : Γ(Mdl, ⊤) := φ q
  let aX : Γ(X, W₂) := X.presheaf.map (homOfLE hWU).op ((U.ι.appIso ⊤).inv (f.appTop av))
  let aY : Γ(Y, gq ⁻¹ᵁ W₂) := gq.app W₂ aX
  let L := CrossingQuotient.lift (t := tt) xv yv hxv
  let L' := CrossingQuotient.lift (t := tt) xv' yv' hxv'
  let jb := graphOver c yb.1 yb.2
  let Kb := AlgebraicClosure ℚ
  let pt : Spec (CommRingCat.of Kb) := IsLocalRing.closedPoint Kb
  let P : Y := jb.base pt
  let η : Spec (CommRingCat.of ↥Pl) := (Spec.map (CommRingCat.ofHom Pl.subtype)).base pt
  let x₀ : (U : Scheme.{0}) := sV.base η
  let gU := (U : Scheme.{0}).presheaf.germ ⊤ x₀ trivial (f.appTop av)

  haveI : IsIntegral Y := hY

  have hbar : ∀ y : Spec (CommRingCat.of Kb), ((Spec.map (CommRingCat.ofHom Pl.subtype)).base y).asIdeal = ⊥ := by
    intro y
    rw [PsiKit.specMap_base_asIdeal, PsiKit.asIdeal_eq_bot_of_field y]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  have hη : η.asIdeal = ⊥ := hbar pt
  have hηuniq : ∀ y : Spec (CommRingCat.of ↥Pl), y.asIdeal = ⊥ → y = η :=
    fun y hy => PrimeSpectrum.ext (hy.trans hη.symm)
  have hgqP : gq.base P = U.ι.base x₀ := by
    have := congrArg (fun k => k.base pt) hP
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using this
  have hsnd : ∀ z : Y, ((pullback.snd c (Spec.map (CommRingCat.ofHom ρ))).base (gq.base z)).asIdeal = ⊥ := by
    intro z
    have := congrArg (fun k => k.base z) hgq_snd
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    rw [this]
    exact hbar _
  have hx₀W : x₀ ∈ Wet := by
    have hspec : η ⤳ IsLocalRing.closedPoint ↥Pl :=
      (PrimeSpectrum.le_iff_specializes η (IsLocalRing.closedPoint ↥Pl)).mp (by
        show η.asIdeal ≤ _
        rw [hη]; exact bot_le)
    exact (hspec.map sV.base.hom.continuous).mem_open Wet.isOpen hsWV
  have hz₀W₂ : U.ι.base x₀ ∈ W₂ := by
    have hrange : U.ι.base x₀ ∈ Set.range (sV ≫ U.ι).base := ⟨η, rfl⟩
    have hn3 : U.ι.base x₀ ∉ W₃ := fun h => ((hW₃ _).mp h).1 hrange
    have htop : U.ι.base x₀ ∈ (⊤ : X.Opens) := trivial
    rw [← hcov] at htop
    rcases (TopologicalSpace.Opens.mem_sup.mp htop) with h | h
    · exact h
    · exact absurd h hn3
  have hPW : P ∈ gq ⁻¹ᵁ W₂ := by
    show gq.base P ∈ W₂
    rw [hgqP]; exact hz₀W₂

  have hLq : L q = 0 := by
    simp only [L, q, map_sub, CrossingQuotient.lift_U, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hvan : sV.appTop (f.appTop av) = 0 := by
    have h1 : sV.appTop (f.appTop av) = (sV ≫ f).appTop av := by rw [Scheme.Hom.comp_appTop]; rfl
    have h2 : (Spec.map (CommRingCat.ofHom L.toRingHom)).appTop av = 0 := by
      show (Spec.map (CommRingCat.ofHom L.toRingHom)).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient ↥Pl tt))).inv q) = 0
      rw [CTKit.appTop_SpecMap]
      show (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv (L q) = 0
      rw [hLq, map_zero]
    rw [h1]
    show (sV ≫ f).app ⊤ av = 0
    rw [Scheme.Hom.congr_app hfsV ⊤]
    show (Spec (CommRingCat.of ↥Pl)).presheaf.map _ ((Spec.map (CommRingCat.ofHom L.toRingHom)).appTop av) = 0
    rw [h2, map_zero]
  have hx : U.ι.app W₂ aX = (U : Scheme.{0}).presheaf.map (homOfLE (le_top : U.ι ⁻¹ᵁ W₂ ≤ ⊤)).op (f.appTop av) := by
    show (X.presheaf.map (homOfLE hWU).op ≫ U.ι.app W₂) ((U.ι.appIso ⊤).inv (f.appTop av)) = _
    rw [Scheme.Hom.naturality]
    show (U : Scheme.{0}).presheaf.map _ (((U.ι.appIso ⊤).inv ≫ U.ι.app (U.ι ''ᵁ ⊤)) (f.appTop av)) = _
    rw [Scheme.Hom.appIso_inv_app, ← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  have ha0 : jb.app (gq ⁻¹ᵁ W₂) aY = 0 := by
    have h1 : (Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sV ≫ U.ι).app W₂ aX = 0 := by
      rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app]
      show (Spec.map (CommRingCat.ofHom Pl.subtype)).app _ (sV.app _ (U.ι.app W₂ aX)) = 0
      rw [hx]
      have h2 : sV.app (U.ι ⁻¹ᵁ W₂) ((U : Scheme.{0}).presheaf.map (homOfLE (le_top : U.ι ⁻¹ᵁ W₂ ≤ ⊤)).op (f.appTop av)) =
          (Spec (CommRingCat.of ↥Pl)).presheaf.map (homOfLE (le_top : sV ⁻¹ᵁ (U.ι ⁻¹ᵁ W₂) ≤ ⊤)).op (sV.appTop (f.appTop av)) := by
        show ((U : Scheme.{0}).presheaf.map _ ≫ sV.app _) _ = _
        rw [Scheme.Hom.naturality]; rfl
      rw [h2, hvan, map_zero, map_zero]
    show (gq.app W₂ ≫ jb.app _) aX = 0
    rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app hP W₂]
    show (Spec (CommRingCat.of Kb)).presheaf.map _ ((Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sV ≫ U.ι).app W₂ aX) = 0
    rw [h1, map_zero]

  have hfx₀ : (f.base x₀).asIdeal = RingHom.ker L.toRingHom := by
    have h1 : f.base x₀ = (sV ≫ f).base η := rfl
    rw [h1, hfsV, PsiKit.specMap_base_asIdeal, hη, ← RingHom.ker_eq_comap_bot]
    rfl
  have hMP : IsLocalRing.maximalIdeal (Mdl.presheaf.stalk (f.base x₀)) =
      Ideal.span {Mdl.presheaf.germ ⊤ (f.base x₀) trivial av} := by
    have gen : ∀ m : Mdl, m.asIdeal = RingHom.ker L.toRingHom →
        IsLocalRing.maximalIdeal (Mdl.presheaf.stalk m) = Ideal.span {Mdl.presheaf.germ ⊤ m trivial av} := by
      rintro ⟨I, hI⟩ hm
      change I = _ at hm
      subst hm
      have hxv1 : xv * yv = tt := by simpa using hxv
      exact MvPolynomial.CrossingQuotient.maximalIdeal_stalk_eq_span_germ_sub (↥Pl) tt xv yv hxv1 hxv0 hI
    exact gen _ hfx₀
  have hfgerm : ∀ x : (U : Scheme.{0}),
      (f.stalkMap x).hom (Mdl.presheaf.germ ⊤ (f.base x) trivial av) = (U : Scheme.{0}).presheaf.germ ⊤ x trivial (f.appTop av) :=
    fun x => Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial av
  have hιgerm : ∀ (x : (U : Scheme.{0})) (hz : U.ι.base x ∈ W₂),
      (U.ι.stalkMap x).hom (X.presheaf.germ W₂ (U.ι.base x) hz aX) = (U : Scheme.{0}).presheaf.germ ⊤ x trivial (f.appTop av) := by
    intro x hz
    erw [Scheme.Hom.germ_stalkMap_apply U.ι W₂ x hz aX]
    rw [hx]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have h𝔪U : Ideal.span {gU} = IsLocalRing.maximalIdeal ((U : Scheme.{0}).presheaf.stalk x₀) := by
    have hUNIF := AlgebraicGeometry.Scheme.Hom.map_stalkMap_maximalIdeal_eq_of_etale_restrict f Wet x₀ hx₀W
    rw [← hUNIF, hMP, Ideal.map_span, Set.image_singleton, hfgerm x₀]
  have h𝔪X : ∀ (z : X) (hz : z ∈ W₂), z = U.ι.base x₀ →
      Ideal.span {X.presheaf.germ W₂ z hz aX} = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    rintro z hz rfl
    apply PsiKit.span_eq_maximalIdeal_of_isIso (U.ι.stalkMap x₀)
    rw [hιgerm x₀ hz]
    exact h𝔪U
  have hagen : Ideal.span {Y.presheaf.germ (gq ⁻¹ᵁ W₂) P hPW aY} = IsLocalRing.maximalIdeal (Y.presheaf.stalk P) := by
    have h1 := h𝔪X (gq.base P) hPW hgqP
    have h2 := PsiKit.span_map_eq_maximalIdeal (gq.stalkMap P) (PsiKit.surjective_of_isIso _) _ h1
    erw [Scheme.Hom.germ_stalkMap_apply gq W₂ P hPW aX] at h2
    exact h2

  have hunitX : ∀ (x : (U : Scheme.{0})) (hz : U.ι.base x ∈ W₂), q ∉ (f.base x).asIdeal →
      IsUnit (X.presheaf.germ W₂ (U.ι.base x) hz aX) := by
    intro x hz hq
    have h1 : IsUnit (Mdl.presheaf.germ ⊤ (f.base x) trivial av) := by
      rw [← Scheme.mem_basicOpen]
      show f.base x ∈ Mdl.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv q)
      rw [basicOpen_eq_of_affine]
      exact hq
    have h2 := h1.map (f.stalkMap x).hom
    rw [hfgerm x, ← hιgerm x hz] at h2
    exact (isUnit_map_iff (U.ι.stalkMap x).hom _).mp h2
  have haU : ∀ (z : Y) (hz : z ∈ gq ⁻¹ᵁ W₂), z ≠ P → IsUnit (Y.presheaf.germ (gq ⁻¹ᵁ W₂) z hz aY) := by
    intro z hz hzP
    have hzX : gq.base z ∈ W₂ := hz
    suffices hX : IsUnit (X.presheaf.germ W₂ (gq.base z) hzX aX) by
      have := hX.map (gq.stalkMap z).hom
      erw [Scheme.Hom.germ_stalkMap_apply gq W₂ z hzX aX] at this
      exact this
    let x : (U : Scheme.{0}) := ⟨gq.base z, hW₂U hzX⟩
    have hxz : U.ι.base x = gq.base z := rfl
    refine hunitX x hzX ?_

    have hover : Ideal.comap (algebraMap ↥Pl Q) (f.base x).asIdeal = ⊥ := by
      have h1 := congrArg (fun k => k.base x) hf
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h1
      have h2 := congrArg PrimeSpectrum.asIdeal h1
      rw [PsiKit.specMap_base_asIdeal] at h2
      exact h2.trans (hsnd z)
    have hxvnot : algebraMap ↥Pl (CrossingQuotient ↥Pl tt) xv ∉ (f.base x).asIdeal := by
      intro h
      apply hxv0
      have : xv ∈ Ideal.comap (algebraMap ↥Pl Q) (f.base x).asIdeal := h
      rw [hover] at this
      exact this
    by_cases hW3 : gq.base z ∈ W₃
    ·
      have hmemO : f.base x ∈ O' := by
        have himg : gq.base z ∈ U.ι ''ᵁ (f ⁻¹ᵁ O') := hle ⟨hzX, hW3⟩
        obtain ⟨x', hx', hx'e⟩ := himg
        have : x' = x := U.ι.isOpenEmbedding.injective (hx'e.trans hxz.symm)
        rw [← this]; exact hx'
      rcases hO' _ hmemO with h | h
      · exact h
      · intro hq
        apply h
        have hid : algebraMap ↥Pl (CrossingQuotient ↥Pl tt) xv * r = q * CrossingQuotient.V _ := by
          have hUV : CrossingQuotient.U tt * CrossingQuotient.V _ = algebraMap ↥Pl (CrossingQuotient ↥Pl tt) tt :=
            CrossingQuotient.U_mul_V _
          have ht : algebraMap ↥Pl (CrossingQuotient ↥Pl tt) tt = algebraMap ↥Pl (CrossingQuotient ↥Pl tt) xv * algebraMap ↥Pl (CrossingQuotient ↥Pl tt) yv := by
            rw [← map_mul, hxv]; rfl
          simp only [q, r, mul_sub, sub_mul]
          rw [hUV, ht]
        have hmem : algebraMap ↥Pl (CrossingQuotient ↥Pl tt) xv * r ∈ (f.base x).asIdeal := by
          rw [hid]; exact Ideal.mul_mem_right _ _ hq
        exact ((f.base x).2.mem_or_mem hmem).resolve_left hxvnot
    ·
      have hrng : gq.base z ∈ Set.range (sV ≫ U.ι).base ∨ gq.base z ∈ Set.range (sV' ≫ U.ι).base := by
        by_contra hcon
        push_neg at hcon
        exact hW3 ((hW₃ _).mpr hcon)
      have hyη : ∀ (sW : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0})), sW ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
          ∀ y, (sW ≫ U.ι).base y = gq.base z → y = η := by
        intro sW hsW y hy
        apply hηuniq
        have h1 := congrArg (fun k => k.base y) hsW
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Scheme.Hom.id_base, TopCat.id_app] at h1
        have hy' : U.ι.base (sW.base y) = gq.base z := hy
        rw [hy'] at h1
        rw [← h1]
        exact hsnd z
      rcases hrng with ⟨y, hy⟩ | ⟨y, hy⟩
      · exfalso
        apply hzP
        have hyη' := hyη sV hsV y hy
        apply gq.isOpenEmbedding.injective
        rw [hgqP, ← hy, hyη']
        rfl
      · have hyη' := hyη sV' hsV' y hy
        have hxeq : x = sV'.base η := by
          apply U.ι.isOpenEmbedding.injective
          rw [hxz, ← hy, hyη']
          rfl
        have hfx : (f.base x).asIdeal = RingHom.ker L'.toRingHom := by
          have h1 : f.base (sV'.base η) = (sV' ≫ f).base η := rfl
          rw [hxeq, h1, hfsV', PsiKit.specMap_base_asIdeal, hη, ← RingHom.ker_eq_comap_bot]
          rfl
        rw [hfx, RingHom.mem_ker]
        have hL'q : L'.toRingHom q = xv' - xv := by
          show L' q = xv' - xv
          simp only [L', q, map_sub, CrossingQuotient.lift_U, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
        rw [hL'q, sub_eq_zero]
        intro hxx
        exfalso
        apply hzP
        have hyy : yv' = yv := by
          apply mul_left_cancel₀ hxv0
          rw [← hxx]
          nth_rewrite 2 [hxx]
          rw [hxv', hxv]
        subst hxx
        subst hyy
        have hff : sV' ≫ f = sV ≫ f := by rw [hfsV', hfsV]
        have hss : sV' = sV := huqV hff
        apply gq.isOpenEmbedding.injective
        rw [hgqP, ← hxz, hxeq, hss]

  have hW : ∃ z ∈ gq ⁻¹ᵁ W₂, z ≠ P := by
    by_contra hcon
    push Not at hcon
    have hgen : genericPoint Y = P :=
      hcon _ (((genericPoint_spec Y).mem_open_set_iff (gq ⁻¹ᵁ W₂).isOpen).mpr ⟨P, Set.mem_univ _, hPW⟩)
    have hfield : IsField (Y.presheaf.stalk P) := by
      rw [← hgen]
      exact Field.toIsField Y.functionField
    have hgerm0 : Y.presheaf.germ (gq ⁻¹ᵁ W₂) P hPW aY = 0 := by
      have h𝔪 : IsLocalRing.maximalIdeal (Y.presheaf.stalk P) = ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
      have h := Ideal.mem_span_singleton_self (Y.presheaf.germ (gq ⁻¹ᵁ W₂) P hPW aY)
      rw [hagen, h𝔪] at h
      exact h
    have hgX : X.presheaf.germ W₂ (gq.base P) hPW aX = 0 := by
      apply PsiKit.injective_of_isIso (gq.stalkMap P)
      erw [Scheme.Hom.germ_stalkMap_apply gq W₂ P hPW aX, map_zero]
      exact hgerm0
    have hgX' : ∀ (z : X) (hz : z ∈ W₂), z = U.ι.base x₀ → X.presheaf.germ W₂ z hz aX = 0 → gU = 0 := by
      rintro z hz rfl h
      show (U : Scheme.{0}).presheaf.germ ⊤ x₀ trivial (f.appTop av) = 0
      rw [← hιgerm x₀ hz, h, map_zero]
    have hgU : gU = 0 := hgX' _ hPW hgqP hgX
    have hgM : Mdl.presheaf.germ ⊤ (f.base x₀) trivial av = 0 := by
      apply PsiKit.stalkMap_injective_of_etale_restrict f Wet x₀ hx₀W
      rw [hfgerm x₀, map_zero]
      exact hgU
    exact PsiKit.germ_U_sub_ne_zero _ xv yv hxv hxv0 (f.base x₀) hfx₀ hgM

  exact AlgebraicGeometry.Scheme.Hom.ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ
    jb (gq ⁻¹ᵁ W₂) hPW aY ha0 hagen haU hW U' hU

end PsiKit

namespace PsiLight

universe v

theorem pullback_transition {X Y : Scheme.{v}} (g : Y ⟶ X) (L : X.Modules) (W₂ W₃ : X.Opens)
    (t : Γ(X, W₂ ⊓ W₃)) (aL : Γ(L, W₂)) (bL : Γ(L, W₃))
    (htr : L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
      t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL) :
    letI tY : Γ(Y, g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃) := g.app (W₂ ⊓ W₃) t
    ((Scheme.Modules.pullback g).obj L).presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃ ≤ g ⁻¹ᵁ W₃)).op
        (Scheme.Modules.pullbackLocalSection g bL) =
      tY • ((Scheme.Modules.pullback g).obj L).presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃ ≤ g ⁻¹ᵁ W₂)).op
          (Scheme.Modules.pullbackLocalSection g aL) := by
  have e1 := Scheme.Modules.map_homOfLE_pullbackLocalSection g (inf_le_right : W₂ ⊓ W₃ ≤ W₃) bL
  have e2 := Scheme.Modules.map_homOfLE_pullbackLocalSection g (inf_le_left : W₂ ⊓ W₃ ≤ W₂) aL
  rw [htr, Scheme.Modules.pullbackLocalSection_smul, ← e2] at e1
  exact e1

theorem crossing_cross {A : Type v} [CommRing A] (t x' y' w : A) (hxy : x' * y' = t) :
    (CrossingQuotient.U t - algebraMap A (CrossingQuotient A t) (w * x')) * (algebraMap A (CrossingQuotient A t) y' - CrossingQuotient.V t) =
      (CrossingQuotient.U t - algebraMap A (CrossingQuotient A t) x') *
        (algebraMap A (CrossingQuotient A t) y' - algebraMap A (CrossingQuotient A t) w * CrossingQuotient.V t) := by
  have hUV : CrossingQuotient.U t * CrossingQuotient.V t = algebraMap A (CrossingQuotient A t) t := CrossingQuotient.mk_X_mul_mk_X _
  have ht : algebraMap A (CrossingQuotient A t) t = algebraMap A (CrossingQuotient A t) x' * algebraMap A (CrossingQuotient A t) y' := by
    rw [← map_mul, hxy]
  rw [map_mul]
  linear_combination (algebraMap A (CrossingQuotient A t) w - 1) * (hUV.trans ht)

theorem glue_mul_eq {M : Scheme.{v}} (a b aw bw : Γ(M, ⊤)) (gM : Γ(M, M.basicOpen a ⊔ M.basicOpen b))
    (hga : M.presheaf.map (homOfLE (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)).op gM *
        M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op a = M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op aw)
    (hgb : M.presheaf.map (homOfLE (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)).op gM *
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b = M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op bw)
    (hcross : aw * b = a * bw) :
    gM * M.presheaf.map (homOfLE (le_top : M.basicOpen a ⊔ M.basicOpen b ≤ ⊤)).op a =
      M.presheaf.map (homOfLE (le_top : M.basicOpen a ⊔ M.basicOpen b ≤ ⊤)).op aw := by
  have rrM : ∀ {V₁ V₂ V₃ : M.Opens} (h₁₂ : V₁ ≤ V₂) (h₂₃ : V₂ ≤ V₃) (x : Γ(M, V₃)),
      M.presheaf.map (homOfLE h₁₂).op (M.presheaf.map (homOfLE h₂₃).op x) =
        M.presheaf.map (homOfLE (h₁₂.trans h₂₃)).op x := by
    intros; rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
  apply TopCat.Sheaf.eq_of_locally_eq₂ M.sheaf
    (homOfLE (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b))
    (homOfLE (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)) le_rfl
  · show M.presheaf.map _ _ = M.presheaf.map _ _
    rw [map_mul, rrM, hga, rrM]
  · show M.presheaf.map _ _ = M.presheaf.map _ _
    rw [map_mul, rrM, rrM]
    have hbu : IsUnit (M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b) :=
      RingedSpace.isUnit_res_basicOpen _ b
    apply hbu.mul_right_cancel
    have e3 : M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op bw *
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op a =
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op (bw * a) :=
      ((M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op).hom.map_mul bw a).symm
    rw [mul_right_comm, hgb, e3, mul_comm bw a, ← hcross]
    exact (M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op).hom.map_mul aw b

theorem transition_eq {C X U M : Scheme.{v}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)
    (W O : M.Opens) (hOW : O ≤ W) (s : Γ(M, W)) (a aw : Γ(M, ⊤))
    (hs : s * M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op a = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op aw)
    (W₂ W₃ : X.Opens) (hWU : W₂ ≤ ι ''ᵁ ⊤) (hle : W₂ ⊓ W₃ ≤ ι ''ᵁ (f ⁻¹ᵁ O)) :
    letI tC : Γ(C, g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃) :=
      g.app (W₂ ⊓ W₃) (X.presheaf.map (homOfLE hle).op ((ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (M.presheaf.map (homOfLE hOW).op s))))
    tC * C.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃ ≤ g ⁻¹ᵁ W₂)).op
          (g.app W₂ (X.presheaf.map (homOfLE hWU).op ((ι.appIso ⊤).inv (f.appTop a)))) =
      C.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃ ≤ g ⁻¹ᵁ W₂)).op
          (g.app W₂ (X.presheaf.map (homOfLE hWU).op ((ι.appIso ⊤).inv (f.appTop aw)))) := by
  set tC : Γ(C, g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃) :=
    g.app (W₂ ⊓ W₃) (X.presheaf.map (homOfLE hle).op ((ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (M.presheaf.map (homOfLE hOW).op s)))) with htC
  have rrY : ∀ {V₁ V₂ V₃ : C.Opens} (h₁₂ : V₁ ≤ V₂) (h₂₃ : V₂ ≤ V₃) (x : Γ(C, V₃)),
      C.presheaf.map (homOfLE h₁₂).op (C.presheaf.map (homOfLE h₂₃).op x) =
        C.presheaf.map (homOfLE (h₁₂.trans h₂₃)).op x := by
    intros; rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
  have hΨeq := congrArg (CTKit.Ψ g ι f W) hs
  rw [RingHom.map_mul, CTKit.Ψ_res g ι f (le_top : W ≤ ⊤) a, CTKit.Ψ_res g ι f (le_top : W ≤ ⊤) aw] at hΨeq
  have hV : g ⁻¹ᵁ W₂ ⊓ g ⁻¹ᵁ W₃ ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W)) :=
    (g.preimage_mono hle).trans (CTKit.le_of_le g ι f hOW)
  have htY : tC = C.presheaf.map (homOfLE hV).op (CTKit.Ψ g ι f W s) := by
    have h1 : tC = C.presheaf.map (homOfLE (g.preimage_mono hle)).op (CTKit.Ψ g ι f O (M.presheaf.map (homOfLE hOW).op s)) := by
      rw [htC]
      show (X.presheaf.map (homOfLE hle).op ≫ g.app (W₂ ⊓ W₃)) _ = _
      rw [Scheme.Hom.naturality]
      rfl
    rw [h1, CTKit.Ψ_res g ι f hOW s]
    exact rrY _ _ _
  have hV₂ : g ⁻¹ᵁ W₂ ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) := g.preimage_mono hWU
  have haY : g.app W₂ (X.presheaf.map (homOfLE hWU).op ((ι.appIso ⊤).inv (f.appTop a))) =
      C.presheaf.map (homOfLE hV₂).op (CTKit.Ψ g ι f ⊤ a) := by
    show (X.presheaf.map (homOfLE hWU).op ≫ g.app W₂) _ = _
    rw [Scheme.Hom.naturality]
    rfl
  have ha'Y : g.app W₂ (X.presheaf.map (homOfLE hWU).op ((ι.appIso ⊤).inv (f.appTop aw))) =
      C.presheaf.map (homOfLE hV₂).op (CTKit.Ψ g ι f ⊤ aw) := by
    show (X.presheaf.map (homOfLE hWU).op ≫ g.app W₂) _ = _
    rw [Scheme.Hom.naturality]
    rfl
  rw [htY, haY, ha'Y, rrY, rrY]
  have := congrArg (C.presheaf.map (homOfLE hV).op) hΨeq
  rw [map_mul, rrY, rrY] at this
  exact this

end PsiLight

theorem main
    {A : Type} [CommRing A] [Algebra A (AlgebraicClosure ℚ)]
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of A)) [IsSeparated c]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : A →+* ↥Pl)
    (gq : pullback c (specMap A (AlgebraicClosure ℚ)) ⟶ pullback c (Spec.map (CommRingCat.ofHom ρ))) [IsOpenImmersion gq]
    (hgq_snd : gq ≫ pullback.snd c (Spec.map (CommRingCat.ofHom ρ)) =
      pullback.snd c (specMap A (AlgebraicClosure ℚ)) ≫ Spec.map (CommRingCat.ofHom Pl.subtype))
    [hY : IsIntegral (pullback c (specMap A (AlgebraicClosure ℚ)))]

    (ybar₁ ybar₂ : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) c)

    (tt : ↥Pl) (htt0 : tt ≠ 0)
    (U : (pullback c (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme tt)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl tt))) =
      U.ι ≫ pullback.snd _ _)

    (Wet : (U : Scheme.{0}).Opens) [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsW : sU.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet) (hsW' : sU'.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet)
    (hP₂ : graphOver c ybar₂.1 ybar₂.2 ≫ gq = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU ≫ U.ι)
    (hP₁ : graphOver c ybar₁.1 ybar₁.2 ≫ gq = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU' ≫ U.ι)

    (x' y' : ↥Pl) (hxy : x' * y' = tt)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥Pl) (w : (↥Pl)ˣ)

    (hxyw : ((w : ↥Pl) * x') * ((↑w⁻¹ : ↥Pl) * y') = algebraMap ↥Pl ↥Pl tt)
    (hxy₁ : x' * y' = algebraMap ↥Pl ↥Pl tt)
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tt) x' y' hxy₁).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom
      (CrossingQuotient.lift (t := tt) ((w : ↥Pl) * x') ((↑w⁻¹ : ↥Pl) * y') hxyw).toRingHom))

    (huq : sU' ≫ f = sU ≫ f → sU' = sU) :
    letI X : Scheme.{0} := pullback c (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥Pl tt
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →
      IsUnit (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM) →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) →
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback gq).obj L ≅
        (RelEffCartierDiv.ofPoint c ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c ybar₂.1 ybar₂.2).idealModule) := by
  classical
  intro gM hga hgb hgu W₂ W₃ hcov hW₂U hle hW₃ Lm aL bL haL hbL htr

  let X : Scheme.{0} := pullback c (Spec.map (CommRingCat.ofHom ρ))
  let Y : Scheme.{0} := pullback c (specMap A (AlgebraicClosure ℚ))
  let Q := CrossingQuotient ↥Pl tt
  let Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
  let φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q x')
  let b : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - CrossingQuotient.V _)
  let aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x'))
  let bw : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _)
  let O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)
  let gO : Γ(Mdl, O) := Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM
  let t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O gO))
  let tY : Γ(Y, gq ⁻¹ᵁ W₂ ⊓ gq ⁻¹ᵁ W₃) := gq.app (W₂ ⊓ W₃) t

  let I₁ : Y.IdealSheafData := (RelEffCartierDiv.ofPoint c ybar₁.1 ybar₁.2).I
  let I₂ : Y.IdealSheafData := (RelEffCartierDiv.ofPoint c ybar₂.1 ybar₂.2).I

  have hWU : W₂ ≤ U.ι ''ᵁ ⊤ := by rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; exact hW₂U
  let aX : Γ(X, W₂) := X.presheaf.map (homOfLE hWU).op ((U.ι.appIso ⊤).inv (f.appTop a))
  let a'X : Γ(X, W₂) := X.presheaf.map (homOfLE hWU).op ((U.ι.appIso ⊤).inv (f.appTop aw))
  let aY : Γ(Y, gq ⁻¹ᵁ W₂) := gq.app W₂ aX
  let a'Y : Γ(Y, gq ⁻¹ᵁ W₂) := gq.app W₂ a'X

  let sU₂ := Scheme.Modules.pullbackLocalSection gq aL
  let sV₂ := Scheme.Modules.pullbackLocalSection gq bL
  have hsU₂ : Scheme.Modules.IsFrameOn sU₂ (gq ⁻¹ᵁ W₂) := haL.pullbackLocalSection gq
  have hsV₂ : Scheme.Modules.IsFrameOn sV₂ (gq ⁻¹ᵁ W₃) := hbL.pullbackLocalSection gq
  have hcov' : gq ⁻¹ᵁ W₂ ⊔ gq ⁻¹ᵁ W₃ = ⊤ := by rw [← Scheme.Hom.preimage_sup, hcov]; rfl
  have htr' : ((Scheme.Modules.pullback gq).obj Lm).presheaf.map (homOfLE (inf_le_right : gq ⁻¹ᵁ W₂ ⊓ gq ⁻¹ᵁ W₃ ≤ gq ⁻¹ᵁ W₃)).op sV₂ =
      tY • ((Scheme.Modules.pullback gq).obj Lm).presheaf.map (homOfLE (inf_le_left : gq ⁻¹ᵁ W₂ ⊓ gq ⁻¹ᵁ W₃ ≤ gq ⁻¹ᵁ W₂)).op sU₂ :=
    PsiLight.pullback_transition gq Lm W₂ W₃ t aL bL htr

  have hfg_t : tY * Y.presheaf.map (homOfLE (inf_le_left : gq ⁻¹ᵁ W₂ ⊓ gq ⁻¹ᵁ W₃ ≤ gq ⁻¹ᵁ W₂)).op aY =
      Y.presheaf.map (homOfLE (inf_le_left : gq ⁻¹ᵁ W₂ ⊓ gq ⁻¹ᵁ W₃ ≤ gq ⁻¹ᵁ W₂)).op a'Y := by

    have hcross : aw * b = a * bw := by
      show φ _ * φ _ = φ _ * φ _
      rw [← map_mul, ← map_mul, PsiLight.crossing_cross _ x' y' (w : ↥Pl) hxy]
    have hgab := PsiLight.glue_mul_eq a b aw bw gM hga hgb hcross
    exact PsiLight.transition_eq gq U.ι f (Mdl.basicOpen a ⊔ Mdl.basicOpen b) O inf_le_left gM a aw hgab W₂ W₃ hWU hle

  have psi_hpe0 : tt ≠ 0 := htt0
  have psi_hx0 : x' ≠ 0 := fun h => psi_hpe0 (by rw [← hxy, h, zero_mul])
  have psi_hwx0 : (w : ↥Pl) * x' ≠ 0 := mul_ne_zero (Units.ne_zero w) psi_hx0
  have psi_mem : ∀ (s : Q) (m : Mdl), m ∈ Mdl.basicOpen (φ s) → s ∉ m.asIdeal := by
    intro s m hm
    have h : m ∈ Mdl.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv s) := hm
    rw [basicOpen_eq_of_affine] at h
    exact h
  have psi_hO : ∀ m ∈ O, (CrossingQuotient.U _ - algebraMap ↥Pl Q x') ∉ m.asIdeal ∨
      (algebraMap ↥Pl Q y' - CrossingQuotient.V _) ∉ m.asIdeal := by
    intro m hm
    rcases TopologicalSpace.Opens.mem_sup.mp hm.1 with h | h
    · exact Or.inl (psi_mem _ _ h)
    · exact Or.inr (psi_mem _ _ h)
  have psi_hO' : ∀ m ∈ O, (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x')) ∉ m.asIdeal ∨
      (algebraMap ↥Pl Q ((↑w⁻¹ : ↥Pl) * y') - CrossingQuotient.V _) ∉ m.asIdeal := by
    intro m hm
    rcases TopologicalSpace.Opens.mem_sup.mp hm.2 with h | h
    · exact Or.inl (psi_mem _ _ h)
    · right
      intro hr
      apply psi_mem _ _ h
      have hid : algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _ =
          algebraMap ↥Pl Q (w : ↥Pl) * (algebraMap ↥Pl Q ((↑w⁻¹ : ↥Pl) * y') - CrossingQuotient.V _) := by
        rw [map_mul, mul_sub, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
      rw [hid]
      exact Ideal.mul_mem_left _ _ hr
  have ha : ∀ (U' : Y.affineOpens) (hU : (U' : Y.Opens) ≤ gq ⁻¹ᵁ W₂),
      I₂.ideal U' = Ideal.span {Y.presheaf.map (homOfLE hU).op aY} ∧
        Y.presheaf.map (homOfLE hU).op aY ∈ nonZeroDivisors Γ(Y, U') := by
    intro U' hU
    exact PsiKit.key c Pl ρ gq hgq_snd ybar₂ tt U f hf Wet sU sU' hsU hsU' hsW hP₂
      x' y' ((w : ↥Pl) * x') ((↑w⁻¹ : ↥Pl) * y') hxy₁ hxyw psi_hx0 hfs hfs' huq O psi_hO
      W₂ W₃ hcov hW₂U hle hW₃ hWU U' hU
  have ha' : ∀ (U' : Y.affineOpens) (hU : (U' : Y.Opens) ≤ gq ⁻¹ᵁ W₂),
      I₁.ideal U' = Ideal.span {Y.presheaf.map (homOfLE hU).op a'Y} ∧
        Y.presheaf.map (homOfLE hU).op a'Y ∈ nonZeroDivisors Γ(Y, U') := by
    intro U' hU
    exact PsiKit.key c Pl ρ gq hgq_snd ybar₁ tt U f hf Wet sU' sU hsU' hsU hsW' hP₁
      ((w : ↥Pl) * x') ((↑w⁻¹ : ↥Pl) * y') x' y' hxyw hxy₁ psi_hwx0 hfs' hfs (fun h => (huq h.symm).symm) O psi_hO'
      W₂ W₃ hcov hW₂U hle (fun z => (hW₃ z).trans and_comm) hWU U' hU
  have h₃ : ∀ (U' : Y.affineOpens), (U' : Y.Opens) ≤ gq ⁻¹ᵁ W₃ → I₁.ideal U' = ⊤ ∧ I₂.ideal U' = ⊤ := by
    intro U' hU'

    have key : ∀ (yb : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) c) (sV : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0}))
        (hP : graphOver c yb.1 yb.2 ≫ gq = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sV ≫ U.ι)
        (havoid : ∀ z, z ∈ W₃ → z ∉ Set.range (sV ≫ U.ι).base),
        (RelEffCartierDiv.ofPoint c yb.1 yb.2).I.ideal U' = ⊤ := by
      intro yb sV hP havoid
      show (graphOver c yb.1 yb.2).ker.ideal U' = ⊤
      rw [Scheme.Hom.ker_apply]
      have hempty : (graphOver c yb.1 yb.2) ⁻¹ᵁ (U' : Y.Opens) = ⊥ := by
        ext z
        simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        intro hz
        have hz' : gq.base ((graphOver c yb.1 yb.2).base z) ∈ W₃ := hU' hz
        refine havoid _ hz' ⟨(Spec.map (CommRingCat.ofHom Pl.subtype)).base z, ?_⟩
        have := congrArg (fun k => k.base z) hP
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
        simpa [Scheme.Hom.comp_base] using this.symm

      have hsub : Subsingleton Γ(Spec (CommRingCat.of (AlgebraicClosure ℚ)), (graphOver c yb.1 yb.2) ⁻¹ᵁ (U' : Y.Opens)) := by
        rw [hempty]
        exact CommRingCat.subsingleton_of_isTerminal ((Spec (CommRingCat.of (AlgebraicClosure ℚ))).sheaf.isTerminalOfEmpty)
      rw [eq_top_iff]
      intro s _
      exact Subsingleton.elim _ _
    refine ⟨key ybar₁ sU' hP₁ (fun z hz => ((hW₃ z).mp hz).2), key ybar₂ sU hP₂ (fun z hz => ((hW₃ z).mp hz).1)⟩
  obtain ⟨pf, qf, hpf, hqf, htrM⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span
      I₁ I₂ (gq ⁻¹ᵁ W₂) (gq ⁻¹ᵁ W₃) aY a'Y ha ha' h₃ tY hfg_t

  have htYu : IsUnit tY := by
    show IsUnit (gq.app (W₂ ⊓ W₃) t)
    exact ((((hgu.map _).map _).map _).map _)
  obtain ⟨u, hu⟩ := htYu
  refine AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul hcov' hsU₂ hsV₂ hpf hqf (↑u⁻¹) ?_ ?_
  · rw [htr', ← hu, smul_smul, Units.inv_mul, one_smul]
  · rw [htrM, ← hu, smul_smul, Units.inv_mul, one_smul]

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (jη : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hjη₁ : jη ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjη₂ : jη ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom Pl.subtype))

    (ybar₁ ybar₂ : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) (ModularCurve.TwoChart.modelTo A (↥K) j))

    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
      U.ι ≫ pullback.snd _ _)

    (Wet : (U : Scheme.{0}).Opens) [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsW : sU.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet) (hsW' : sU'.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet)
    (hP₂ : graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₂.1 ybar₂.2 ≫ jη = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU ≫ U.ι)
    (hP₁ : graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₁.1 ybar₁.2 ≫ jη = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU' ≫ U.ι)

    (x' y' : ↥Pl) (hxy : x' * y' = (ρ ϖ) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥Pl) (w : (↥Pl)ˣ)

    (hxyw : ((w : ↥Pl) * x') * ((↑w⁻¹ : ↥Pl) * y') = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
    (hxy₁ : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy₁).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom
      (CrossingQuotient.lift (t := (ρ ϖ) ^ e) ((w : ↥Pl) * x') ((↑w⁻¹ : ↥Pl) * y') hxyw).toRingHom))

    (huq : sU' ≫ f = sU ≫ f → sU' = sU) :
    letI X : Scheme.{0} := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥Pl ((ρ ϖ) ^ e)
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →
      IsUnit (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM) →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) →
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback jη).obj L ≅
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₂.1 ybar₂.2).idealModule) := by
  intro gM hga hgb hgu W₂ W₃ hcov hW₂U hle hW₃ Lm aL bL haL hbL htr

  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom Pl.subtype)) := GIKit.isOpenImmersion_subtype Pl hPl
  have hψ2 : Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) = specMap A (AlgebraicClosure ℚ) := by
    show _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  haveI : IsOpenImmersion jη := by
    have e : jη = baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j)
        (⟨Spec.map (CommRingCat.ofHom Pl.subtype), hψ2⟩ : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) (Spec.map (CommRingCat.ofHom ρ))) := by
      apply pullback.hom_ext
      · rw [hjη₁]; unfold RelPicard.baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]
      · rw [hjη₂]; unfold RelPicard.baseChangeSnd; rw [pullback.lift_snd]
    rw [e]; unfold RelPicard.baseChangeSnd; infer_instance
  haveI : IsIntegral (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) := by
    haveI := (ModularCurve.XOneP.smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj).2
    have hcomp : specMap L (AlgebraicClosure ℚ) ≫ specMap A L = specMap A (AlgebraicClosure ℚ) := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A L (AlgebraicClosure ℚ)]
    haveI : IsIntegral (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (specMap L (AlgebraicClosure ℚ))) :=
      inferInstance
    exact IsIntegral.of_isIso ((pullbackLeftPullbackSndIso (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)
      (specMap L (AlgebraicClosure ℚ))).hom ≫ (pullback.congrHom rfl hcomp).hom)
  have htt0 : ((ρ ϖ) ^ e) ≠ 0 := by
    refine pow_ne_zero _ (fun h0 => ?_)
    have hϖ0 : ϖ ≠ 0 := by
      intro h; apply IsDiscreteValuationRing.not_isField A
      exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr (by rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl])
    have h1 : algebraMap A (AlgebraicClosure ℚ) ϖ = 0 := by
      rw [← hρ]; show ((ρ ϖ : ↥Pl) : AlgebraicClosure ℚ) = 0; rw [h0]; rfl
    rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ), map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A L)] at h1
    exact hϖ0 h1
  exact main (ModularCurve.TwoChart.modelTo A (↥K) j) Pl ρ jη hjη₂ ybar₁ ybar₂ ((ρ ϖ) ^ e) htt0 U f hf Wet sU sU' hsU hsU' hsW hsW' hP₂ hP₁
    x' y' hxy hx' hy' w hxyw hxy₁ hfs hfs' huq gM hga hgb hgu W₂ W₃ hcov hW₂U hle hW₃ Lm aL bL haL hbL htr

end S_ModularCurve_XOneP_nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul (solution)
