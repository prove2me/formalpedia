-- Prove2me | solution 1 for GlobalTheory.LocalLift.exists_local_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:34:11.17095+00:00
-- url     : https://prove2.me/submissions/c64439ab-52b3-4ca6-8cf5-69fd130c497b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Theorems.Thm_GlobalTheory_LocalLift_hol_eventually_mem
import Theorems.Thm_GlobalTheory_LocalLift_hol_differentiableAt
import Theorems.Thm_GlobalTheory_LocalLift_isDerivAt0_const
import Theorems.Thm_GlobalTheory_HolChart_derivation_eq_zero
import Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
import Theorems.Thm_GlobalTheory_SCV_analyticAt_iff_eventually_differentiableAt
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff
import Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open Filter Topology
variable {Y : Scheme.{0}}
namespace GlobalTheory.LocalLift
namespace _root_.GlobalTheory.LocalLift
theorem _root_.solution : ∀ (Y : Scheme.{0}) (s : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)
    (g g' : ℕ) (e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)) (e' : (Fin g' → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)),
    Smooth s → (∀ z, e z ≫ s = 𝟙 _) → (∀ z, e' z ≫ s = 𝟙 _) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e' →
    ((∀ w, ∃! v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) ∧
      ∀ v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e' 0 → ∃! w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) →
    e 0 = e' 0 → ∃ k₀ : (Fin g → ℂ) → (Fin g' → ℂ), k₀ 0 = 0 ∧ AnalyticAt ℂ k₀ 0 ∧
      ∀ᶠ z in nhds (0 : Fin g → ℂ), e' (k₀ z) = e z := by
  intro Y s g g' e e' hs he he' hhe hhe' H h00
  obtain ⟨H1, H2⟩ := H
  set y := e' 0 with hy_def
  have hys : y ≫ s = 𝟙 _ := he' 0
  have hsub : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨U, hU, V, hV, hyV, hVU, hsm⟩ := Smooth.exists_isStandardSmooth s (y.base default)
  have hUtop : U = ⊤ := eq_top_iff.2 fun x _ => Subsingleton.elim (s.base (y.base default)) x ▸ hVU hyV
  subst hUtop
  have : ∃ n, (Scheme.Hom.appLE s ⊤ V hVU).hom.IsStandardSmoothOfRelativeDimension n := by
    algebraize [(Scheme.Hom.appLE s ⊤ V hVU).hom]
    obtain ⟨P, σ, hσ, hP, ⟨Q⟩⟩ := hsm
    exact ⟨Q.dimension, ⟨P, σ, hσ, hP, Q, rfl⟩⟩
  obtain ⟨n, hn⟩ := this
  let c : ℂ →+* Γ(Y, V) := (Scheme.Hom.appLE s ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hyV' : ⊤ ≤ y ⁻¹ᵁ V := fun q _ => Subsingleton.elim default q ▸ hyV
  let ev : Γ(Y, V) →+* ℂ := _root_.GlobalTheory.TangentOrigin.evalPt y V hyV'
  have hconst : ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y), x ≫ s = 𝟙 _ → ∀ (hx : ⊤ ≤ x ⁻¹ᵁ V) (a : ℂ),
      _root_.GlobalTheory.TangentOrigin.evalPt x V hx (c a) = a := by
    intro x hxs hx a
    have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_constFn s x V hx a
    have hid : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ) = 𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) := by
      change Spec.map (𝟙 _) = _
      exact Spec.map_id _
    have key : ∀ (z : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (hz : z = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) (h : ⊤ ≤ z ⁻¹ᵁ ⊤),
        _root_.GlobalTheory.TangentOrigin.evalPt z ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by
      rintro _ rfl h
      exact _root_.GlobalTheory.TangentOrigin.evalPt_spMap _ a
    exact h1.trans (key _ (hxs.trans hid.symm) _)
  have hev : ∀ a, ev (c a) = a := hconst y hys hyV'
  obtain ⟨φ, hφC, hφet, hφ0⟩ := _root_.GlobalTheory.HolChart.exists_etale_coords_vanishing c hc ev hev
  letI : Algebra ℂ Γ(Y, V) := c.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, V) := φ.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun a => by
    change c a = φ (MvPolynomial.C a)
    rw [← hφC]; rfl
  haveI : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, V) := hφet
  let evA : Γ(Y, V) →ₐ[ℂ] ℂ := { ev with commutes' := fun a => hev a }
  obtain ⟨W, σ, m, fs, ε, hWo, hW0, hσ0, hε, hσhol, hσX, hσuniq⟩ :=
    _root_.GlobalTheory.exists_holomorphic_section_of_etale n Γ(Y, V) evA hφ0
  have hpt : ∀ w, ∃ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y, ∃ h : ⊤ ≤ x ⁻¹ᵁ V, _root_.GlobalTheory.TangentOrigin.evalPt x V h = (σ w : Γ(Y, V) →+* ℂ) :=
    fun w => _root_.GlobalTheory.TangentOrigin.exists_evalPt_eq hV _
  choose pt hptV hpt using hpt
  let F : (Fin g' → ℂ) → (Fin n → ℂ) := fun z i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (φ (MvPolynomial.X i))
  let G : (Fin g → ℂ) → (Fin n → ℂ) := fun z i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) V (φ (MvPolynomial.X i))
  have hyVe : ⊤ ≤ e 0 ⁻¹ᵁ V := by rw [h00]; exact hyV'
  have hlocal : ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y), x ≫ s = 𝟙 _ → ∀ (hx : ⊤ ≤ x ⁻¹ᵁ V),
      (∀ k, ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (fs k) - ev (fs k)‖ < ε) →
      (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) ∈ W ∧
        x = pt (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) := by
    intro x hxs hx hclose
    let ψ : Γ(Y, V) →ₐ[ℂ] ℂ :=
      { _root_.GlobalTheory.TangentOrigin.evalPt x V hx with commutes' := fun a => hconst x hxs hx a }
    obtain ⟨w, hw, hψw⟩ := hσuniq ψ (fun k => by
      have hk := hclose k
      rwa [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt x V hx] at hk)
    have hcoord : (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) = w := funext fun i => by
      rw [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt x V hx]
      change ψ (φ (MvPolynomial.X i)) = w i
      rw [hψw]
      exact hσX w hw i
    rw [hcoord]
    refine ⟨hw, _root_.GlobalTheory.TangentOrigin.ext_evalPt hV hx (hptV w) ?_⟩
    rw [hpt w]
    exact RingHom.ext fun a => DFunLike.congr_fun hψw a
  have hF_diff : ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), DifferentiableAt ℂ F z := by
    filter_upwards [_root_.GlobalTheory.LocalLift.hol_eventually_mem hhe' (Set.mem_univ 0) hyV'] with z hz
    exact differentiableAt_pi.2 fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' hz.1 hz.2 _
  have hG_diff : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), DifferentiableAt ℂ G z := by
    filter_upwards [_root_.GlobalTheory.LocalLift.hol_eventually_mem hhe (Set.mem_univ 0) hyVe] with z hz
    exact differentiableAt_pi.2 fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe hz.1 hz.2 _
  have hF0 : F 0 = 0 := funext fun i => by
    change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' y V _ = 0
    rw [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt y V hyV']
    exact hφ0 i
  have hG0 : G 0 = 0 := funext fun i => by
    change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e 0) V _ = 0
    rw [h00, _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt y V hyV']
    exact hφ0 i
  have hFe : ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), F z ∈ W ∧ e' z = pt (F z) := by
    have hcl : ∀ k, ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (fs k) - ev (fs k)‖ < ε := by
      intro k
      have hc := (_root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' (Set.mem_univ 0) hyV' (fs k)).continuousAt
      have h0v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' 0) V (fs k) = ev (fs k) :=
        _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ V hyV' _
      filter_upwards [hc.eventually (Metric.ball_mem_nhds _ hε)] with z hz
      rwa [dist_eq_norm, h0v] at hz
    filter_upwards [Filter.eventually_all.2 hcl,
      _root_.GlobalTheory.LocalLift.hol_eventually_mem hhe' (Set.mem_univ 0) hyV'] with z hz hzV
    exact hlocal (e' z) (he' z) hzV.2 hz
  have hGe : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), G z ∈ W ∧ e z = pt (G z) := by
    have hcl : ∀ k, ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) V (fs k) - ev (fs k)‖ < ε := by
      intro k
      have hc := (_root_.GlobalTheory.LocalLift.hol_differentiableAt hhe (Set.mem_univ 0) hyVe (fs k)).continuousAt
      have h0v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e 0) V (fs k) = ev (fs k) := by
        rw [h00]
        exact _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ V hyV' _
      filter_upwards [hc.eventually (Metric.ball_mem_nhds _ hε)] with z hz
      rwa [dist_eq_norm, h0v] at hz
    filter_upwards [Filter.eventually_all.2 hcl,
      _root_.GlobalTheory.LocalLift.hol_eventually_mem hhe (Set.mem_univ 0) hyVe] with z hz hzV
    exact hlocal (e z) (he z) hzV.2 hz
  have hbij : Function.Bijective (fderiv ℂ F 0) := by
    have hevcongr : ∀ (x x' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y) (hxx : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ V)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ V), _root_.GlobalTheory.TangentOrigin.evalPt x V hx = _root_.GlobalTheory.TangentOrigin.evalPt x' V hx' := by
      rintro x _ rfl _ _; rfl
    have hevcongrC : ∀ (x x' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y) (hxx : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ V)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ V), _root_.GlobalTheory.TangentOrigin.evalPt x V hx = _root_.GlobalTheory.TangentOrigin.evalPt x' V hx' := by
      rintro x _ rfl _ _; rfl
    have hFi : ∀ w i, fderiv ℂ F 0 w i = fderiv ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (φ (MvPolynomial.X i))) 0 w := by
      intro w i
      rw [fderiv_pi (fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' (Set.mem_univ 0) hyV' _)]
      rfl
    have hvV : ∀ v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y → ⊤ ≤ v ⁻¹ᵁ V := by
      intro v hvy
      refine (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff v V).2 ?_
      rw [show _root_.GlobalTheory.TangentOrigin.fstC = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom from rfl, hvy]
      exact hyV'
    have hfst : ∀ (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y) (hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y)
        (hv : ⊤ ≤ v ⁻¹ᵁ V) (a : Γ(Y, V)), TrivSqZeroExt.fst (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a) = ev a := by
      intro v hvy hv a
      have h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ V := by rw [hvy]; exact hyV'
      have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v V hv h' a
      rw [hevcongrC _ _ hvy h' hyV'] at h1
      exact h1.symm
    have hcst : ∀ (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y), v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ∀ (hv : ⊤ ≤ v ⁻¹ᵁ V) (a : ℂ), _root_.GlobalTheory.TangentOrigin.evalPt v V hv (c a) = algebraMap ℂ (DualNumber ℂ) a := by
      intro v hvs hv a
      have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_constFn s v V hv a
      have key : ∀ (z : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (hz : z = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)))
          (h : ⊤ ≤ z ⁻¹ᵁ ⊤), _root_.GlobalTheory.TangentOrigin.evalPt z ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
            algebraMap ℂ (DualNumber ℂ) a := by
        rintro _ rfl h
        exact _root_.GlobalTheory.TangentOrigin.evalPt_spMap _ a
      exact h1.trans (key _ hvs _)
    let v0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y
    have hv0y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v0 = y := by
      change Spec.map _ ≫ Spec.map _ ≫ _ = _
      rw [← Spec.map_comp_assoc]
      have hid : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext a
        simp
      rw [hid, Spec.map_id, Category.id_comp]
    have hv0s : v0 ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) := by
      change _ ≫ y ≫ s = _
      rw [hys, Category.comp_id]
    constructor
    · refine (injective_iff_map_eq_zero (fderiv ℂ F 0)).2 fun w hw => ?_
      obtain ⟨v, ⟨hvs, hvd⟩, -⟩ := H1 w
      have hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y := hvd.1
      have hv := hvV v hvy
      let D : Γ(Y, V) →+ ℂ :=
        { toFun := fun a => TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a)
          map_zero' := by simp
          map_add' := fun a b => by simp }
      have hD : D = 0 := by
        refine _root_.GlobalTheory.HolChart.derivation_eq_zero φ hφet ev D (fun a => ?_) (fun a b => ?_) (fun i => ?_)
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (φ (MvPolynomial.C a))) = 0
          rw [← RingHom.comp_apply φ, hφC, hcst v hvs hv a]
          exact TrivSqZeroExt.snd_inl _ _
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (a * b)) =
            ev a * TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv b) +
              ev b * TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a)
          rw [map_mul, TrivSqZeroExt.snd_mul, hfst v hvy hv a, hfst v hvy hv b]
          simp [smul_eq_mul, mul_comm]
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (φ (MvPolynomial.X i))) = 0
          have h2 := hvd.2 V hv (φ (MvPolynomial.X i))
          refine h2.trans ?_
          rw [← hFi, hw]
          rfl
      have hv0V : ⊤ ≤ v0 ⁻¹ᵁ V := hvV v0 hv0y
      have hvv0 : v = v0 := by
        refine _root_.GlobalTheory.TangentOrigin.ext_evalPt hV hv hv0V (RingHom.ext fun a => ?_)
        have h0 := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) y V hyV' hv0V a
        rw [h0]
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [hfst v hvy hv a]; rfl
        · exact (DFunLike.congr_fun hD a).trans (TrivSqZeroExt.snd_inl _ _).symm
      have h0d : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' 0 v0 :=
        _root_.GlobalTheory.LocalLift.isDerivAt0_const e' 0 (fun U f _ => map_zero _)
      exact (H2 v0 hv0s hv0y).unique (hvv0 ▸ hvd) h0d
    · intro u
      let S : Γ(Y, V) → (Fin n → ℂ) → ℂ := fun a w => σ w a
      have hSd : ∀ a, DifferentiableAt ℂ (S a) 0 := fun a =>
        (hσhol a 0 hW0).differentiableAt (hWo.mem_nhds hW0)
      have hS0 : ∀ a, S a 0 = ev a := fun a => by
        change σ 0 a = ev a
        rw [hσ0]
        rfl
      let χ : Γ(Y, V) →+* DualNumber ℂ :=
        { toFun := fun a => TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (fderiv ℂ (S a) 0 u)
          map_one' := by
            have h1 : S 1 = fun _ => 1 := funext fun w => map_one (σ w)
            rw [h1]
            ext <;> simp
          map_mul' := fun a b => by
            have hm : S (a * b) = S a * S b := funext fun w => map_mul (σ w) a b
            have hd : fderiv ℂ (S (a * b)) 0 u = S a 0 * fderiv ℂ (S b) 0 u + S b 0 * fderiv ℂ (S a) 0 u := by
              rw [hm, ((hSd a).hasFDerivAt.mul (hSd b).hasFDerivAt).fderiv]
              simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
            rw [hd, hS0, hS0]
            ext
            · simp
            · simp [smul_eq_mul]
              ring
          map_zero' := by
            have h0 : S 0 = fun _ => 0 := funext fun w => map_zero (σ w)
            rw [h0]
            ext <;> simp
          map_add' := fun a b => by
            have ha : S (a + b) = S a + S b := funext fun w => map_add (σ w) a b
            rw [ha, fderiv_add (hSd a) (hSd b)]
            ext <;> simp }
      have hχapp : ∀ a, χ a = TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (fderiv ℂ (S a) 0 u) := fun a => rfl
      obtain ⟨v, hv, hχ⟩ := _root_.GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
      have hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y := by
        have h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ V :=
          (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff v V).1 hv
        refine _root_.GlobalTheory.TangentOrigin.ext_evalPt hV h' hyV' (RingHom.ext fun a => ?_)
        rw [_root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp _ v V hv h' a, hχ]
        change TrivSqZeroExt.fst (χ a) = ev a
        rw [hχapp]
        simp
      have hvs : v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) := by
        refine _root_.GlobalTheory.TangentOrigin.eq_spMap_of_evalPt (v ≫ s) _ fun a => ?_
        rw [← _root_.GlobalTheory.TangentOrigin.evalPt_constFn s v V hv a, hχ]
        have hc' : S (c a) = fun _ => a := funext fun w => (σ w).commutes a
        change χ (c a) = _
        rw [hχapp]
        rw [hc', hev]
        refine TrivSqZeroExt.ext ?_ ?_
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
      obtain ⟨w, hw, -⟩ := H2 v hvs hvy
      refine ⟨w, funext fun i => ?_⟩
      rw [hFi, ← hw.2 V hv (φ (MvPolynomial.X i))]
      change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv _) = u i
      rw [hχ]
      have hXi : S (φ (MvPolynomial.X i)) =ᶠ[𝓝 0] fun w => w i := by
        filter_upwards [hWo.mem_nhds hW0] with w hw
        exact hσX w hw i
      rw [hχapp]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, hXi.fderiv_eq]
      rw [(hasFDerivAt_apply i (0 : Fin n → ℂ)).fderiv]
      rfl
  have hFan : AnalyticAt ℂ F 0 := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hF_diff
  have hGan : AnalyticAt ℂ G 0 := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hG_diff
  let L : (Fin g' → ℂ) ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofBijective (fderiv ℂ F 0)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hL : HasFDerivAt F (L : (Fin g' → ℂ) →L[ℂ] (Fin n → ℂ)) 0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hFan.differentiableAt.hasFDerivAt
  have hFc : ContDiffAt ℂ 1 F 0 := hFan.contDiffAt
  have hS : HasStrictFDerivAt F (L : (Fin g' → ℂ) →L[ℂ] (Fin n → ℂ)) 0 :=
    hFc.hasStrictFDerivAt' hL one_ne_zero
  let Finv := HasStrictFDerivAt.localInverse F L 0 hS
  have hinvc : ContDiffAt ℂ 1 Finv (F 0) := hFc.to_localInverse hL one_ne_zero
  have hinvan : AnalyticAt ℂ Finv (F 0) := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2
    ((hinvc.eventually (by simp)).mono fun p hp => hp.differentiableAt one_ne_zero)
  have hinv0 : Finv (F 0) = 0 := hS.localInverse_apply_image
  refine ⟨Finv ∘ G, ?_, ?_, ?_⟩
  · change Finv (G 0) = 0
    rw [hG0, ← hF0, hinv0]
  · have hA : AnalyticAt ℂ Finv (G 0) := by rw [hG0, ← hF0]; exact hinvan
    exact hA.comp hGan
  · have hGt : Tendsto G (𝓝 0) (𝓝 (F 0)) := by
      rw [hF0, ← hG0]; exact hGan.continuousAt.tendsto
    have hFt : Tendsto Finv (𝓝 (F 0)) (𝓝 0) := by
      have ht := hinvan.continuousAt.tendsto
      rwa [hinv0] at ht
    filter_upwards [hGt.eventually hS.eventually_right_inverse, (hFt.comp hGt).eventually hFe, hGe]
      with z h1 h2 h3
    simp only [Function.comp_apply] at h2 ⊢
    rw [h2.2, h1, ← h3.2]
end _root_.GlobalTheory.LocalLift
end GlobalTheory.LocalLift
