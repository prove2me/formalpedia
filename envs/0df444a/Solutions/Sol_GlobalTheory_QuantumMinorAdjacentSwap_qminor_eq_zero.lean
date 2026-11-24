-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.qminor_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:09.763065+00:00
-- url     : https://prove2.me/submissions/2be48c55-71e9-443d-b196-66f12b2dbb00

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_eq_zero_of_eq_neg
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_qminor_comp_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a : Fin t → Fin n) (u : ℂ) (b : Fin t → Fin n) (hb : ¬ Function.Injective b) :
    qminor E a b u = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hb
  have h := qminor_comp_perm E hE a u (Equiv.swap i j) b
  have hb' : b ∘ Equiv.swap i j = b := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [hb', Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_eq_neg
  simpa using h
end GlobalTheory.QuantumMinorAdjacentSwap
