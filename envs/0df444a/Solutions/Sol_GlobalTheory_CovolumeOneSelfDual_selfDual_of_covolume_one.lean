-- Prove2me | solution 1 for GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:19.149892+00:00
-- url     : https://prove2.me/submissions/01367630-0267-4b2d-b480-54f1d5c645da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne
import Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_inversion_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual
namespace GlobalTheory.CovolumeOneSelfDual
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hμ hF h1
  refine ⟨hμ, fun Φ hΦ hs hI z => ?_⟩
  have he : ∀ y, ∫ x, Φ (x - z) * B x y ∂μ = (∫ x, Φ x * B x y ∂μ) * B y z := by
    intro y
    rw [← integral_add_right_eq_self (fun x => Φ (x - z) * B x y) z, ← integral_mul_const]
    congr 1
    funext x
    rw [add_sub_cancel_right, hadd, hsy z y, mul_assoc]
  have hs' : HasCompactSupport fun x => Φ (x - z) := hs.comp_homeomorph (Homeomorph.subRight z)
  have hI' : Integrable (fun y => ∫ x, Φ (x - z) * B x y ∂μ) μ := by
    simp only [he]
    exact hI.mul_bdd (c := 1) (hc z).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y z).le)
  have key := inversion_zero Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1
    (Φ := fun x => Φ (x - z)) (by fun_prop) hs' hI'
  simp only [he, zero_sub] at key
  exact key
end GlobalTheory.CovolumeOneSelfDual
