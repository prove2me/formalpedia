-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.rep_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.128414+00:00
-- url     : https://prove2.me/submissions/e959cb66-0d36-4620-998a-da956b34ea52

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
theorem _root_.solution {B A : AddSubgroup V} (q : A ⧸ B.addSubgroupOf A) : rep q ∈ A := (Quotient.out q : A).2
end GlobalTheory.TripleIntertwiner
