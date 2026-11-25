-- Prove2me | solution 1 for GlobalTheory.Klein.Red.add_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:54.492457+00:00
-- url     : https://prove2.me/submissions/d366c391-b32a-44e7-9ee4-6e17f4a0d157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
namespace Red
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) :=
  ⟨fun h' => h.1 ((L.lattice.add_mem_iff_left hω).1 h'), by
    have e : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    rw [e]; exact h.2⟩
end Red
end GlobalTheory.Klein
