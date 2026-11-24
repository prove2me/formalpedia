-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.vol_mul_vol_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:30.699523+00:00
-- url     : https://prove2.me/submissions/783c125b-8c8d-4101-8154-b5ba9bb811ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_inversion
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_measureReal_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
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
theorem _root_.solution {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν) (s : kˣ) :
    ν.real (cball s) * ν.real (cball (c * s⁻¹)) = 1 := by
  haveI := hν.1
  haveI := t2Space k
  have hcl : IsClopen (cball (1 : kˣ)) := ⟨(isCompact_cball 1).isClosed, isOpen_cball 1⟩
  have hf : (cball (1 : kˣ)).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro (isCompact_cball 1) fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hx : x ∈ cball (1 : kˣ)
    · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  have h1 := (fourier_inversion ν h hf).symm.trans (hν.2 _ hf)
  rw [Set.indicator_of_mem (by simp [cball]), mul_one] at h1
  have h2 : ν.real (𝒪[k] : Set k) ^ 2 * nabs k c = 1 := by exact_mod_cast h1
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [measureReal_cball, measureReal_cball, ← h2, h4]; ring
end GlobalTheory.SplitWeil.FourierPi
