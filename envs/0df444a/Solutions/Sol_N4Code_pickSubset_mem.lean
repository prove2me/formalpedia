-- Prove2me | solution 1 for N4Code.pickSubset_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:30.878971+00:00
-- url     : https://prove2.me/submissions/f3c3624b-e426-43ad-9bfc-af6cc94c6483

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ∈ s.powersetCard k :=
  Classical.choose_spec (Finset.powersetCard_nonempty_of_le hk)
end N4Code
