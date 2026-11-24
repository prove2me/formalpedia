-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:08.975875+00:00
-- url     : https://prove2.me/submissions/23a7cd4b-fbf6-4ef2-b10d-3d60935f95f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_inversion_pi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_vol_mul_vol_dual
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
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
theorem _root_.solution {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧
      ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  refine ⟨fourier_mem_SB _ h hf, ?_⟩
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => ν) h hf
  have hb : ∀ r : kˣ, (Measure.pi fun _ : n => ν).real (box n r) = ν.real (cball r) ^ Fintype.card n := by
    intro r
    simp [Measure.real, box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, vol_mul_vol_dual h hν]
  simp
end GlobalTheory.SplitWeil.FourierPi
