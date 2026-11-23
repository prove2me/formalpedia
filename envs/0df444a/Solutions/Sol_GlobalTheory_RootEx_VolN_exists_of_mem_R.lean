-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.exists_of_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:33.404112+00:00
-- url     : https://prove2.me/submissions/62801028-b2d2-4eb9-97d2-ddad1f0ba155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {g | ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, u, hu, rfl⟩ ⟨y, v, hv, rfl⟩
        exact ⟨x * y, _, mul_mem (conj_mem hu y) hv, by simp [mul_assoc]⟩
      inv_mem' := by
        rintro _ ⟨x, u, hu, rfl⟩
        exact ⟨x⁻¹, _, conj_mem (inv_mem hu) x⁻¹, by simp [mul_assoc]⟩ }
  have : R k n c p ≤ S := sup_le (by rintro _ ⟨x, rfl⟩; exact ⟨x, 1, one_mem _, by simp⟩)
    fun u hu => ⟨1, u, hu, by simp⟩
  exact this hg
end GlobalTheory.RootEx.VolN
