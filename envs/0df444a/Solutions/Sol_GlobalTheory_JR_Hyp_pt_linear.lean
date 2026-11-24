-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.pt_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:49.134669+00:00
-- url     : https://prove2.me/submissions/415ac168-3084-4e7f-834f-c4c331a8fd65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierLinearOnTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring
end GlobalTheory.JR.Hyp
