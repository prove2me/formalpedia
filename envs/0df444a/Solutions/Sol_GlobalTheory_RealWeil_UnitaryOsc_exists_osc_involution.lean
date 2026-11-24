-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.exists_osc_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:13.944687+00:00
-- url     : https://prove2.me/submissions/63bcc8ec-83f7-4724-898d-a24dc5950787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_sm_comp_iff
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_isHeis_comp
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_fderiv_comp_clm
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_isOsc_comp
import Theorems.Thm_P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2
import Theorems.Thm_P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_one__5bca5be2c3a0
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_continuous_dP
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_norm_sq_crd
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_continuous_kL
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_crd_cplx
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_cplx_cplx
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_omJ_cplx
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist
import Theorems.Thm_GlobalTheory_RealWeil_proj_eq_self_of_annihilated
import Theorems.Thm_GlobalTheory_T_exists_oscillatorAction_of_gaussianPairings
import Theorems.Thm_GlobalTheory_T_gaussianPairing_unitaryGroup_two_three
import Theorems.Thm_GlobalTheory_cartanInvolution_conj_of_posDef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RealWeil.UnitaryOsc
theorem _root_.solution (H : Matrix ι ι ℂ) (h1 : Hᴴ = H) (h2 : H * H = 1) (B : Type) [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B) (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ)
    (G : Type) [Group G] (m : G →* Matrix ι ι ℂ) (hm : ∀ g, (m g)ᴴ * H * m g = H) :
    ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧
      (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧
      ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f →
        (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) →
        Ω g f = dP s (m g) • f := by
  have hJ := cplx_cplx H h1 h2
  have hρ' : IsHeis (omJ (cplx H h1 h2)) fun v => ρ (crd ι v) :=
    isHeis_comp hρ (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) fun x y => (omJ_cplx H h1 h2 x y).symm
  obtain ⟨hl, hmu⟩ := GlobalTheory.T.gaussianPairing_unitaryGroup_two_three (EuclideanSpace ℂ ι) ι (crd ι) norm_sq_crd H h1 h2 (cplx H h1 h2) (crd_cplx H h1 h2)
  have hom : ∀ (g : uGrp H) x y, omJ (cplx H h1 h2) (kU H g x) (kU H g y) = omJ (cplx H h1 h2) x y := by
    intro g x y
    have hg : (g.1 : Matrix ι ι ℂ)ᴴ * H * g.1 = H := g.2
    rw [omJ_cplx, omJ_cplx]
    change (star (crd ι (kL _ y)) ⬝ᵥ H *ᵥ crd ι (kL _ x)).im = _
    rw [crd_kL, crd_kL, form_mulVec, hg]
  obtain ⟨Ω, hΩ, hc, hv⟩ := GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ hρ' (uGrp H) (kU H)
    (fun g => dP H (g.1 : Matrix ι ι ℂ)) hom (detPlus_one₂ H)
    (fun g => by
      obtain ⟨e1, e2, e3⟩ := hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)
      have : star (dP H (g.1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      rw [e3, e2]
      field_simp)
    (fun g g' => by
      obtain ⟨e1, e2, e3⟩ := hl ((g * g').1 : Matrix ι ι ℂ) (kU H (g * g')) (g * g').2 (crd_kL _)
      have e4 := (hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)).1
      have e5 := (hl (g'.1 : Matrix ι ι ℂ) (kU H g') g'.2 (crd_kL _)).1
      have : star (dP H ((g * g').1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      have e6 : (g.1 : Matrix ι ι ℂ)⁻¹ * ((g * g').1 : Matrix ι ι ℂ) = g'.1 := by
        rw [← Matrix.coe_units_inv, Subgroup.coe_mul, Units.val_mul, Units.inv_mul_cancel_left]
      rw [hmu ((g * g').1 : Matrix ι ι ℂ) (g.1 : Matrix ι ι ℂ) (kU H (g * g')) (kU H g) (g * g').2 g.2 (crd_kL _)
        (crd_kL _), e3, e2, e6]
      field_simp)
  let φ : G →* uGrp H := m.toHomUnits.codRestrict (uGrp H) hm
  have hφ : ∀ g, ((φ g).1 : Matrix ι ι ℂ) = m g := fun _ => rfl
  refine ⟨fun g => Ω (φ g), isOsc_comp (crd ι) φ (fun g v => crd_kL _ v) hΩ, fun g hg f hf => ?_,
    fun hmc f hf => ?_, fun s g hs hpos hsg f hf hD => ?_⟩
  · have : φ g = 1 := Subtype.ext (Units.ext hg)
    simp only [this]
    exact hΩ.2.2.2.1 f ((sm_comp_iff _ _ _).2 hf)
  · exact hc G φ (continuous_kL.comp hmc) ((continuous_dP H).comp hmc) f ((sm_comp_iff _ _ _).2 hf)
  · obtain ⟨a, ha, has⟩ := GlobalTheory.cartanInvolution_conj_of_posDef ι H s h1 h2 hs hpos
    have hdet : a.det ≠ 0 := by
      intro h0
      have e := congrArg Matrix.det ha
      have e' := congrArg Matrix.det h2
      rw [det_mul, h0, mul_zero] at e
      rw [det_mul, ← e, det_one] at e'
      simp at e'
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det a).2 hdet.isUnit
    let a' : uGrp H := ⟨u, ha⟩
    let g₀ : uGrp H := a'⁻¹ * φ g * a'
    have hg₀ : (u : Matrix ι ι ℂ) * g₀.1 = m g * u := by
      have : a' * g₀ = φ g * a' := by simp only [g₀]; group
      exact congrArg (fun x : uGrp H => (x.1 : Matrix ι ι ℂ)) this
    have hcomm : H * (g₀.1 : Matrix ι ι ℂ) = g₀.1 * H := by
      refine (Units.mul_right_inj u).1 ?_
      rw [← mul_assoc, ← mul_assoc, has, hg₀, mul_assoc, hg₀, mul_assoc, has, ← mul_assoc, ← mul_assoc, hsg]
    have hiso : (g₀.1 : Matrix ι ι ℂ)ᴴ * g₀.1 = 1 := by
      have e : (g₀.1 : Matrix ι ι ℂ)ᴴ * H * g₀.1 = H := g₀.2
      rw [mul_assoc, hcomm, ← mul_assoc] at e
      have e' := congrArg (· * H) e
      simpa only [mul_assoc, h2, mul_one] using e'
    let E : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ) := (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) ∘L kU H a'
    have hE : ∀ z, E z = (u : Matrix ι ι ℂ) *ᵥ crd ι z := fun z => crd_kL _ z
    have hvac := GlobalTheory.RealWeil.proj_eq_self_of_annihilated (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ (hρ'.twist (kU H a') (hom a')) f
      (ContDiff.comp (g := fun v => ρ v f) hf E.contDiff) fun z => by
        have e1 := fderiv_comp_clm hf E z
        have e2 := fderiv_comp_clm hf E (cplx H h1 h2 z)
        have e3 : E (cplx H h1 h2 z) = I • s *ᵥ E z := by
          rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec, has]
        rw [e3] at e2
        have e4 := hD (E z)
        rw [← e1, ← e2] at e4
        exact e4
    have key := hv a' g₀ (norm_kL hiso) f ((sm_comp_iff _ _ _).2 hf) hvac
    have e : a' * g₀ * a'⁻¹ = φ g := by simp only [g₀]; group
    rw [e, detPlus_conj₂ hdet has hg₀] at key
    exact key
end GlobalTheory.RealWeil.UnitaryOsc
