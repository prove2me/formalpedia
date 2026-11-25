-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.exists_osc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:28.830696+00:00
-- url     : https://prove2.me/submissions/f32ef092-e3a2-4092-9b27-5bb261a77394

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
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_exists_osc_involution
import Theorems.Thm_GlobalTheory_hermitian_congr_involution


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  intro ι _ _ H h1 h2 B _ _ _ ρ hρ G _ m hm
  obtain ⟨R, s₀, hR, hs1, hs2, rfl⟩ := GlobalTheory.hermitian_congr_involution ι H h1 h2
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hR.isUnit
  have hback : ∀ X : Matrix ι ι ℂ, (u⁻¹).1ᴴ * (u.1ᴴ * X * u.1) * (u⁻¹).1 = X := fun X =>
    calc _ = (u.1 * (u⁻¹).1)ᴴ * X * (u.1 * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = X := by simp
  let E : (ι → ℂ) ≃L[ℝ] (ι → ℂ) := ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
    (fun v => by simp) fun v => by simp
  have hE : ∀ v, E v = (u⁻¹).1 *ᵥ v := fun _ => rfl
  have hρ' : IsHeis (fun x y => (star y ⬝ᵥ s₀ *ᵥ x).im) fun v => ρ (E v) :=
    isHeis_comp hρ (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) fun x y => by
      change (star ((u⁻¹).1 *ᵥ y) ⬝ᵥ _ *ᵥ (u⁻¹).1 *ᵥ x).im = _
      rw [form_mulVec, hback]
  let m' : G →* Matrix ι ι ℂ :=
    { toFun := fun g => u.1 * m g * (u⁻¹).1
      map_one' := by simp
      map_mul' := fun g g' => by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left] }
  have hm' : ∀ g, m' g = u.1 * m g * (u⁻¹).1 := fun _ => rfl
  obtain ⟨Ω, hΩ, ho, hc, hv⟩ := exists_osc_involution s₀ hs1 hs2 B _ hρ' G m' fun g => by
    calc _ = (u⁻¹).1ᴴ * ((m g)ᴴ * (u.1ᴴ * s₀ * u.1) * m g) * (u⁻¹).1 := by
          simp only [hm', mul_assoc, conjTranspose_mul]
      _ = s₀ := by rw [hm, hback]
  refine ⟨Ω, isOsc_comp E (MonoidHom.id G) (fun g v => ?_) hΩ, fun g hg f hf => ?_, fun hmc f hf => ?_,
    fun s g hs hpos hsg f hf hD => ?_⟩
  · simp only [hE, hm', MonoidHom.id_apply, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
  · exact ho g (by simp [hm', hg]) f ((sm_comp_iff _ _ _).2 hf)
  · exact hc ((continuous_const.mul hmc).mul continuous_const) f ((sm_comp_iff _ _ _).2 hf)
  · have hpos' : (s₀ * (u.1 * s * (u⁻¹).1)).PosDef := by
      have := hpos.conjTranspose_mul_mul_same (B := (u⁻¹).1) (Matrix.mulVec_injective_of_isUnit (u⁻¹).isUnit)
      have e : s₀ * (u.1 * s * (u⁻¹).1) = (u⁻¹).1ᴴ * (u.1ᴴ * s₀ * u.1 * s) * (u⁻¹).1 := by
        calc _ = (u.1 * (u⁻¹).1)ᴴ * (s₀ * (u.1 * s * (u⁻¹).1)) := by simp
          _ = _ := by simp only [mul_assoc, conjTranspose_mul]
      rw [e]
      exact this
    have key := hv (u.1 * s * (u⁻¹).1) g
      (by simp only [mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hs, one_mul, Units.mul_inv]) hpos'
      (by simp only [hm', mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hsg, mul_assoc]) f
      ((sm_comp_iff _ _ _).2 hf) fun z => by
        have e1 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) z
        have e2 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) (I • (u.1 * s * (u⁻¹).1) *ᵥ z)
        have e3 : E (I • (u.1 * s * (u⁻¹).1) *ᵥ z) = I • s *ᵥ E z := by
          simp only [hE, mulVec_smul, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
        simp only [ContinuousLinearEquiv.coe_coe] at e1 e2
        rw [e1, e2, e3]
        exact hD _
    rw [key, ← detPlus_conj₂ (s := s) (g := m g) hR (by simp) (by simp [hm'])]
end GlobalTheory.RealWeil.UnitaryOsc
