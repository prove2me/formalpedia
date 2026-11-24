-- Prove2me | solution 1 for GlobalTheory.SgGlob.isUn_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.707834+00:00
-- url     : https://prove2.me/submissions/8cdbde33-aaed-42fc-8a94-6edf6bffe402

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
theorem _root_.solution {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (h : γ * δ = 1) :
    IsUn σ J δ := by
  have e : cT σ δ * cT σ γ = 1 := by
    rw [cT, cT, ← Matrix.transpose_mul, ← Matrix.map_mul, h]
    simp [Matrix.map_one]
  rw [IsUn, ← hγ, show cT σ δ * (cT σ γ * J * γ) * δ = cT σ δ * cT σ γ * J * (γ * δ) by
    simp only [Matrix.mul_assoc], e, h, Matrix.one_mul, Matrix.mul_one, hγ]
end GlobalTheory.SgGlob
