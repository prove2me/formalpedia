-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:57.361793+00:00
-- url     : https://prove2.me/submissions/fdc9abff-735f-4132-a799-5ba42b631aeb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_adjoint_of_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_isInvInvariant
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
namespace GlobalTheory.CompanionTheory.HeckeAdj
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by
  intro F _ _ _ _ ι _ _ K e he
  obtain ⟨hKo, hKc, hc, hbi⟩ := he
  refine ⟨⟨hKo, hKc, ?_, ?_⟩, ?_⟩
  · have h1 : HasCompactSupport (fun g : GL ι F => e g⁻¹) := hc.comp_homeomorph (Homeomorph.inv _)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro k₁ h₁ k₂ h₂ g
    show starRingEnd ℂ (e (k₁ * g * k₂)⁻¹) = starRingEnd ℂ (e g⁻¹)
    rw [show (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ by group, hbi _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
  · intro V _ _ ρ B hB v hv w hw
    borelize F
    haveI := isInvInvariant (Measure.haar : Measure (GL ι F)) K hKo hKc
    exact adjoint_of_inv Measure.haar K hKo hKc e hc hbi ρ B hB v w
      (fun k hk => by simpa using hv ⟨k, hk⟩) (fun k hk => by simpa using hw ⟨k, hk⟩)
end GlobalTheory.CompanionTheory.HeckeAdj
