-- Prove2me | solution 1 for GlobalTheory.PeriodLift.tendsto_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:50.562827+00:00
-- url     : https://prove2.me/submissions/d4426113-b815-471a-a26e-e885fc54d91a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PeriodCoordinatesFramesLiftTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.PeriodLift
namespace GlobalTheory.PeriodLift
theorem _root_.solution {E : Type} [Field E] {r : ℕ} {ι : Type} {𝓕 : Filter ι}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ι → (Fin r → E) → ℂ) (Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v))) (v : Fin r → E) :
    Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v)) := by
  have hv : v ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e : (0 : Fin r → E) = (0 : E) • (0 : Fin r → E) := by simp
    rw [e]
    simp only [hs, hs₀, hσ, zero_mul]
    exact tendsto_const_nhds
  | add x y _ _ hx hy => simpa only [ha, ha₀] using hx.add hy
  | smul c x _ hx => simpa only [hs, hs₀] using hx.const_mul (σ c)
end GlobalTheory.PeriodLift
