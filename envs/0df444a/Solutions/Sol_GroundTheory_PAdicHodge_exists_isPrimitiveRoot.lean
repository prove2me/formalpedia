-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:16.630682+00:00
-- url     : https://prove2.me/submissions/ea45d8e4-2a3d-4d56-b5bf-d0383372dbd0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) := by
  haveI : NeZero ((p ^ n : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero n (Fact.out : p.Prime).ne_zero)⟩
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic (p ^ n) (PadicAlgCl p))
    (degree_cyclotomic_pos (p ^ n) (PadicAlgCl p) hpos).ne'
  exact ⟨ζ, (isRoot_cyclotomic_iff).1 hζ⟩
end GroundTheory.PAdicHodge
