-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Four.unitaryFourUpperLeftBlock_injective_on_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:20.874469+00:00
-- url     : https://prove2.me/submissions/072553d0-ff7d-43a3-9c5b-c77a232ac733

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
import Theorems.Thm_GlobalTheory_SatakeWeyl_Four_unitaryFourUpperLeftBlock_mul_of_mem_levi
import Theorems.Thm_GlobalTheory_SatakeWeyl_Four_unitaryFourUpperLeftBlock_one
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Four
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Four
theorem _root_.solution {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)
end GlobalTheory.SatakeWeyl.Four
