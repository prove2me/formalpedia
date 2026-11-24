-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.mulVec_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:41.957632+00:00
-- url     : https://prove2.me/submissions/01484f28-3636-45a9-a914-33c4755df099

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
theorem _root_.solution (hg : (g : E) ≠ 0) (P P' : Matrix (Fin n) (Fin (r + 1)) E) (a : Fin (r + 1) → E) :
    P' *ᵥ a = P *ᵥ a + (g : E) • (((g : E)⁻¹ • (P' - P)) *ᵥ a) := by
  rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hg, one_smul, Matrix.sub_mulVec, add_sub_cancel]
end GlobalTheory.SgGlob.Iota
