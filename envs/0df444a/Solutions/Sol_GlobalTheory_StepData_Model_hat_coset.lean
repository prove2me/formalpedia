-- Prove2me | solution 1 for GlobalTheory.StepData.Model.hat_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:06.666811+00:00
-- url     : https://prove2.me/submissions/ec782004-e60d-4e6d-8058-48cdfbee8b58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n]
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n 1) (Submodule.Quotient.mk y₀)) η = ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n 1) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => (𝒪[k] : Set k)).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n 1) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
      simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
    by_cases h : y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k)
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := mul_mem hε (sum_mem fun i _ => mul_mem (hη i) (h i trivial))
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_int k).measurableSet), Measure.real,
    Measure.pi_pi]
  simp [hν.2]
end GlobalTheory.StepData.Model
