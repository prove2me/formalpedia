-- Prove2me | solution 1 for GlobalTheory.isRegular_map_C_append_map_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:25.106362+00:00
-- url     : https://prove2.me/submissions/a5c01204-7959-4835-8baf-5287e203aaa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_ker_map_comp_killVars
import Theorems.Thm_GlobalTheory_ofList_map_C_append_map_X
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_C_append_map_X

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
theorem _root_.solution {rs : List R} (hrs : RingTheory.Sequence.IsRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by
  refine ⟨isWeaklyRegular_map_C_append_map_X hrs.1 hl, ?_⟩
  have h := hrs.2
  rw [smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [ofList_map_C_append_map_X, ← ker_map_comp_killVars]
  haveI : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.2 h.symm
  exact (RingHom.ker_ne_top _).symm
end GlobalTheory
