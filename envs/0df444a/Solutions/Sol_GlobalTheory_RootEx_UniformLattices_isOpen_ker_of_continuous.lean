-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:33.332801+00:00
-- url     : https://prove2.me/submissions/41b27c41-c21f-4e4e-9ffa-e12db5e01ec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_eq_one_of_pow_near
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_isOpen_ker_of_cball
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_cball_mem_nhds
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (μ : kˣ →* ℂˣ) (hμ : Continuous μ) : IsOpen (μ.ker : Set kˣ) := by
  have hV : {u | ‖((μ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : kˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hμ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  have h1 : (fun b : k => 1 + b) ⁻¹' T ∩ cball 1 ∈ 𝓝 (0 : k) :=
    inter_mem ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hT))
      (cball_mem_nhds 1)
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine isOpen_ker_of_cball μ s fun x hx => Units.ext (eq_one_of_pow_near fun n => ?_)
  have hx1 : valuation k (x : k) ≤ 1 := by
    have := add_mem_cball (hs hx).2 (show (1 : k) ∈ cball 1 by simp [cball])
    simpa [cball] using this
  have hn : (x : k) ^ n - 1 ∈ cball s := by
    induction n with
    | zero => simp [cball]
    | succ n ih =>
      have e : (x : k) ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      rw [e]
      refine add_mem_cball ?_ hx
      show valuation k _ ≤ valuation k (s : k)
      rw [map_mul]
      exact (mul_le_of_le_one_left' hx1).trans ih
  have := hTV (a := x ^ n) (by simpa using (hs hn).1)
  simpa using this
end GlobalTheory.RootEx.UniformLattices
