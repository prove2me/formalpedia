-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.integral_psi_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:08.870982+00:00
-- url     : https://prove2.me/submissions/c819be44-1245-4e3a-b727-2b062bf06d54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_coe_psi_sum
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_integral_psi_O
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
open Classical
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (u : n → k) :
    ∫ y, (if ∀ r, y r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ : n => ν) =
      if ∀ r, u r ∈ 𝒪[k] then 1 else 0 := by
  haveI := hν.1
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (fun y : n → k => (if ∀ r, y r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u ⬝ᵥ y)) : ℂ)) =
      fun y => ∏ r, (fun r t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u r * t)) : ℂ)) r (y r) := by
    funext y
    simp only [Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
    rw [← coe_psi_sum, dotProduct, Finset.mul_sum]
  rw [e, integral_fintype_prod_eq_prod (fun r t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u r * t)) : ℂ))]
  simp only [integral_psi_O hψ hν, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
end GlobalTheory.LocFlat.UnramFlat
