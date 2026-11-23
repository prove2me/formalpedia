-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.rep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.04613+00:00
-- url     : https://prove2.me/submissions/3f3af54c-53e9-40fe-b3b3-e39c85297972

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V]
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution {B A : AddSubgroup V} (a : A) :
    ∃ l, l ∈ A ∧ l ∈ B ∧ rep (QuotientAddGroup.mk a : A ⧸ B.addSubgroupOf A) = a + l := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul (B.addSubgroupOf A) a
  refine ⟨((h : A) : V), (h : A).2, h.2, ?_⟩
  unfold rep; rw [hh]; rfl
end GlobalTheory.TripleIntertwiner
