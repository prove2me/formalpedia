-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.PtTest.slice_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:54.235821+00:00
-- url     : https://prove2.me/submissions/9e7c3fe8-2642-4e37-9e53-f43c00f2b001

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp GlobalTheory.JR.Hyp.PtTest
namespace GlobalTheory.JR.Hyp.PtTest
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : ∀ᶠ a' in 𝓝 a, (fun b => Φ (a', b)) = fun b => Φ (a, b) := by
  have hC : IsCompact (Prod.snd '' tsupport Φ) := hΦ.2.isCompact.image continuous_snd
  have h := hC.eventually_forall_of_forall_eventually (x₀ := a) (P := fun a' b => Φ (a', b) = Φ (a, b))
    fun y _ => by
      have h1 : ∀ᶠ z in 𝓝 (a, y), Φ z = Φ (a, y) := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y)
      have hc : Continuous fun z : X × Y => (a, z.2) := continuous_const.prodMk continuous_snd
      have h2 : ∀ᶠ z in 𝓝 (a, y), Φ (a, z.2) = Φ (a, y) :=
        (hc.tendsto (a, y)).eventually ((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y))
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
  filter_upwards [h] with a' ha'
  funext b
  by_cases hb : b ∈ Prod.snd '' tsupport Φ
  · exact ha' b hb
  · have h0 : ∀ c, Φ (c, b) = 0 := fun c => by
      by_contra hne
      exact hb ⟨(c, b), subset_tsupport _ hne, rfl⟩
    rw [h0, h0]
end GlobalTheory.JR.Hyp.PtTest
