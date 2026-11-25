-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.eOf_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:41.605377+00:00
-- url     : https://prove2.me/submissions/57f740df-76b2-4132-8c14-c59b1d4853c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (P : Matrix (Fin n) (Fin (r + 1)) E) (c : Fin r → E) :
    eOf P *ᵥ c = P *ᵥ (Fin.snoc c 0 : Fin (r + 1) → E) := by
  ext i
  simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
end GlobalTheory.SgGlob.Iota
