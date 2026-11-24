-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:44.39015+00:00
-- url     : https://prove2.me/submissions/ed771d6f-c16e-448d-85c7-ea54b05594dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_parPhi_of_mem
import Theorems.Thm_GlobalTheory_StepData_parPhi_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_parPhi_ne_zero_iff
import Theorems.Thm_GlobalTheory_StepData_eq_mul_of_support
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_tame_det_of_mem_KOne


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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}
omit [Fintype s] [DecidableEq s]
namespace GlobalTheory.StepData
theorem _root_.solution (hδ : IsTame δ) (g : (TypeDatum.full k r).stepJ s') (x : Matrix (r ⊕ s) (r ⊕ s') k) :
    parPhi δ (x * (g : GL (r ⊕ s') k).val) =
      (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g) * parPhi δ x := by
  refine eq_mul_of_support (G := (TypeDatum.full k r).stepJ s') (fun g x => x * (g : GL (r ⊕ s') k).val)
    (fun g x => by simp [Matrix.mul_assoc]) (c := fun g => (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g))
    (fun g x hx => ?_) g x
  obtain ⟨⟨u, hu, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
  obtain ⟨-, -, hB, hC, D, hD, eD⟩ := g.2
  set A := (TypeDatum.full k r).corner g
  have hA := intM_of_mem_KO A.2
  have eA : (A : GL r k).val = _ := TypeDatum.corner_val _ g
  obtain ⟨w, hw, ew⟩ := exists_mul_KOne (mul_mem hu A.2)
    (M := u.val * (A : GL r k).val + x.toBlocks₁₂ * (g : GL (r ⊕ s') k).val.toBlocks₂₁)
    (by simpa using h12.mul_maxM hC)
  rw [parPhi_of_mem δ hu e h21 h12 h22, ← fromBlocks_toBlocks x, ← fromBlocks_toBlocks (g : GL (r ⊕ s') k).val,
    fromBlocks_multiply, ← e, ← eA, ← eD,
    parPhi_fromBlocks δ (mul_mem (mul_mem hu A.2) (KOne_le_KO hw)) ew ((h21.mul_intM hA).add (h22.mul_maxM hC))
      (((intM_of_mem_KO hu).mul hB).add (h12.mul (intM_of_mem_KO hD)))
      ((h21.intM.mul hB).add (h22.mul (intM_of_mem_KO hD))),
    map_mul, map_mul, map_mul, map_mul, tame_det_of_mem_KOne hδ hw, TypeDatum.rho_apply]
  change _ = ((1 * _ : ℂˣ) : ℂ) * _
  simp
end GlobalTheory.StepData
