-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.wtLink
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:25.432362+00:00
-- url     : https://prove2.me/submissions/838b4505-548e-430c-b367-8b77f61a66f9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_add
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_mem_UJ
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_tor_mem_K
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_deriv_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_hasDerivAt_exp_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_one_param
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution : CompanionTheory.D.DSIC.WtLink := by
  intro n ε H _ _ σ S E hrep h μ v
  have hG : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (a * b) = σ a * σ b := by
    intro a ha b hb
    rw [ContinuousLinearMap.mul_def]
    exact hrep.1.2 a ha b hb
  have h1 : σ 1 = 1 := hrep.1.1
  constructor
  · intro hw θ _
    have hw' : ∀ a, E a a v = (μ a : ℂ) • v := hw
    let φ : ℝ → (H →L[ℂ] H) := fun t => σ (tor (t • θ))
    have hadd : ∀ s t, φ (s + t) = φ s * φ t := by
      intro s t
      show σ (tor ((s + t) • θ)) = σ (tor (s • θ)) * σ (tor (t • θ))
      rw [add_smul, tor_add]
      exact hG _ (tor_mem_UJ ε _) _ (tor_mem_UJ ε _)
    have hz : φ 0 = 1 := by
      show σ (tor ((0 : ℝ) • θ)) = 1
      rw [zero_smul, tor_zero]
      exact h1
    have hd : HasDerivAt (fun t => φ t (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H)) 0 := by
      have := deriv_zero h θ v
      convert this using 1
      simp only [hw', Submodule.coe_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have key := one_param φ hadd hz (v : H) _ hd
    show σ (tor θ) (v : H) = _
    rw [show tor θ = tor ((1 : ℝ) • θ) by rw [one_smul]]
    exact key
  · intro hK a
    apply Subtype.ext
    rw [Submodule.coe_smul]
    let θ : Fin n → ℝ := Pi.single a 1
    have hf : (fun t : ℝ => σ (tor (t • θ)) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have ht := hK (t • θ) (tor_mem_K ε _)
      rw [show tor (t • θ) = Matrix.diagonal (fun b => Complex.exp ((((t • θ) b : ℝ) : ℂ) * Complex.I)) from rfl, ht]
      congr 2
      simp [θ, Pi.single_apply]
      try (push_cast; ring)
    have d1 := deriv_zero h θ v
    rw [hf] at d1
    have d2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := (hasDerivAt_exp_mul ((μ a : ℂ) * Complex.I) 0).smul_const (v : H)
      simpa using this
    have hu := d1.unique d2
    have hsum : ∑ b, ((θ b : ℂ) * Complex.I) • (E b b v : H) = Complex.I • (E a a v : H) := by
      rw [Finset.sum_eq_single a]
      · simp [θ]
      · intro b _ hb
        simp [θ, Pi.single_apply, hb]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [hsum] at hu
    calc (E a a v : H) = (-Complex.I * Complex.I) • (E a a v : H) := by
          rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
      _ = (-Complex.I) • (Complex.I • (E a a v : H)) := by rw [smul_smul]
      _ = (-Complex.I) • (((μ a : ℂ) * Complex.I) • (v : H)) := by rw [hu]
      _ = (μ a : ℂ) • (v : H) := by
          rw [smul_smul]
          congr 1
          rw [show -Complex.I * ((μ a : ℂ) * Complex.I) = (μ a : ℂ) * -(Complex.I * Complex.I) by ring,
            Complex.I_mul_I, neg_neg, mul_one]
end GlobalTheory.CompanionTheory.WtLinkPf
