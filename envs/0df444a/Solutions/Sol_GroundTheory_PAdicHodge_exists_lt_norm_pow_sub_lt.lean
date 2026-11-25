-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_lt_norm_pow_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:31.391552+00:00
-- url     : https://prove2.me/submissions/fabc9446-b41b-4a89-9a71-8a7dcef6bba7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_lt_norm_pow_sub_pow_lt_09ba910a808a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {c : PadicAlgCl p} (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (f : ℕ → ℕ) : ∃ k₀ k₁, k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε :=
  _root_.GroundTheory.Variant₂.N1.exists_lt_norm_pow_sub_pow_lt hc hε f
end GroundTheory.PAdicHodge
