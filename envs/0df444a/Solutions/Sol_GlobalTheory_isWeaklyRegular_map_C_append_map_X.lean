-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_map_C_append_map_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:29.438104+00:00
-- url     : https://prove2.me/submissions/d6049255-4040-4e9a-9285-00963e52a5fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_mem_of_X_mul_mem
import Theorems.Thm_GlobalTheory_ofList_map_C_append_map_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution {rs : List R} (hrs : IsWeaklyRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by
  induction l using List.reverseRecOn with
  | nil => simpa using hrs.of_flat (S := MvPolynomial σ R)
  | append_singleton l x ih =>
    rw [List.nodup_append] at hl
    have hx : x ∉ {x | x ∈ l} := fun h => hl.2.2 x h x (by simp) rfl
    rw [List.map_append, ← List.append_assoc, isWeaklyRegular_append_iff]
    refine ⟨ih hl.1, ?_⟩
    rw [List.map_singleton, isWeaklyRegular_singleton_iff, isSMulRegular_quotient_iff_mem_of_smul_mem,
      smul_eq_mul, Ideal.mul_top, ofList_map_C_append_map_X]
    intro p hp
    exact mem_of_X_mul_mem hx _ hp
end GlobalTheory
