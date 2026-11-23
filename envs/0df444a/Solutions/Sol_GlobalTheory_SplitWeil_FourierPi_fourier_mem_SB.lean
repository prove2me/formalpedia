-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:39.628033+00:00
-- url     : https://prove2.me/submissions/99dfd36c-c101-4609-b52a-1e2a9486da99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) := by
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro (isCompact_box (c * s⁻¹)) fun y hy => fourier_eq_zero_pi μ h hs hy⟩
  have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport f, ψ (x ⬝ᵥ z) = ψ (x ⬝ᵥ y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (ψ (q.2 ⬝ᵥ q.1), ψ (q.2 ⬝ᵥ y)) :=
      (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)).prodMk
        (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_const))
    filter_upwards [h2.eventually_eq (y, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
  filter_upwards [h1] with z hz
  congr 1
  funext x
  by_cases hx : x ∈ tsupport f
  · rw [hz x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]
end GlobalTheory.SplitWeil.FourierPi
