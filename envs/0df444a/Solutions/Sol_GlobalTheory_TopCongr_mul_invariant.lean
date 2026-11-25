-- Prove2me | solution 1 for GlobalTheory.TopCongr.mul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:05.992694+00:00
-- url     : https://prove2.me/submissions/324eef6b-0665-432e-8731-1d292a2e36f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.TopCongr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TopCongr
theorem _root_.solution {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by
  by_cases hx : IntM x
  · have e : g * x = x + (g - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, hp x _ hx (hg.mul_intM hx)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (u.val * x) = 0 := by_contra fun h => hx (by
      have := (mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)
      rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)
    rw [h1, h2]
end GlobalTheory.TopCongr
