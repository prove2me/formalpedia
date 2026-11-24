-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:18:57.226468+00:00
-- url     : https://prove2.me/submissions/3221edc2-4732-477d-a581-56756459558e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
import Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_measure_preimage_inter_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FiberInt
variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']
namespace GlobalTheory.CompanionTheory.FiberInt
theorem _root_.solution : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  intro A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π s hπc _ hs Γ Γ' hΓc hΓ'c hΓ _ lam lam' hlam hlam' 𝓖 𝓖' hG h1 hG' h1' G hGc hGinv
  have := hΓc
  have := hΓ'c
  have := hlam
  have := hlam'
  have hπ : Measurable π := hπc.measurable
  have hGm : Measurable G := hGc.measurable
  have key : Measure.map G (Measure.map π (lam.restrict 𝓖)) = Measure.map G (lam'.restrict 𝓖') := by
    ext B hB
    have hinvB : ∀ γ ∈ Γ', ∀ x, γ + x ∈ G ⁻¹' B ↔ x ∈ G ⁻¹' B := fun γ hγ x => by
      simp only [Set.mem_preimage, hGinv γ hγ x]
    rw [Measure.map_apply hGm hB, Measure.map_apply hGm hB, Measure.map_apply hπ (hGm hB),
      Measure.restrict_apply (hπ (hGm hB)), Measure.restrict_apply (hGm hB)]
    exact measure_preimage_inter_eq hπ hs hΓ hG h1 hG' h1' (hGm hB) hinvB
  calc ∫ x in 𝓖, G (π x) ∂lam = ∫ y, G y ∂(Measure.map π (lam.restrict 𝓖)) :=
        (integral_map hπ.aemeasurable hGc.aestronglyMeasurable).symm
    _ = ∫ z, z ∂(Measure.map G (Measure.map π (lam.restrict 𝓖))) :=
        (integral_map hGm.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ z, z ∂(Measure.map G (lam'.restrict 𝓖')) := by rw [key]
    _ = ∫ x in 𝓖', G x ∂lam' := integral_map hGm.aemeasurable aestronglyMeasurable_id
end GlobalTheory.CompanionTheory.FiberInt
