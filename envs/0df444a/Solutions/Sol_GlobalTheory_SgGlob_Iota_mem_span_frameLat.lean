-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.mem_span_frameLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:27.75652+00:00
-- url     : https://prove2.me/submissions/bf01e1a5-492c-43f3-b547-2c1d4e319a01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_one_mem_dInv
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_frameLat

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
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ Submodule.span E (frameLat P : Set (Fin n → E)) ↔ ∃ a, P *ᵥ a = v := by
  constructor
  · intro hv
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun w hw => ?_) hv
    obtain ⟨a, -, rfl⟩ := (mem_frameLat P w).1 hw
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span ⟨b, 1, one_mem_dInv _, (one_smul _ _).symm⟩))
end GlobalTheory.SgGlob.Iota
