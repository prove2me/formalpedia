-- Prove2me | solution 1 for GlobalTheory.SgGlob.isUn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:49.738801+00:00
-- url     : https://prove2.me/submissions/ce0c0e3a-44e1-49fb-a9ec-0203d38c00f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs

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
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob
theorem _root_.solution {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]
end GlobalTheory.SgGlob
