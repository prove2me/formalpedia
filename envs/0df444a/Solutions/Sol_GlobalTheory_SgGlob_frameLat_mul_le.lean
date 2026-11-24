-- Prove2me | solution 1 for GlobalTheory.SgGlob.frameLat_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:05.084945+00:00
-- url     : https://prove2.me/submissions/0ecfa267-3388-4461-a1af-624b6562d23d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_mul_mem_dInv
import Theorems.Thm_GlobalTheory_SgGlob_UO_entry_mem

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
variable {n r : ℕ}
namespace GlobalTheory.SgGlob
theorem _root_.solution (P : Matrix (Fin n) (Fin (r + 1)) E) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hu : u ∈ UO E r) : frameLat (P * u) ≤ frameLat P := by
  rw [frameLat, Submodule.span_le]
  rintro _ ⟨b, c, hc, rfl⟩
  have e : (c • fun i => (P * u) i b) = ∑ a, (c * u a b) • fun i => P i a := by
    ext i
    simp only [Matrix.mul_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases lt_or_ge b a with h | h
  · rw [(hu.1 a b).1 h, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ⟨a, _, ?_, rfl⟩
    have h1 : (a : ℕ) ≤ b := h
    have h2 := b.2
    rw [show r - (a : ℕ) = r - (b : ℕ) + ((b : ℕ) - a) by omega]
    exact mul_mem_dInv hc (UO.entry_mem hu a b)
end GlobalTheory.SgGlob
