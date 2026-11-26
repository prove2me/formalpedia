-- Prove2me | solution 1 for N4Code.pickSubset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:12.587688+00:00
-- url     : https://prove2.me/submissions/c633f763-6a5e-4ff8-860f-b5593c2647ca

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_pickSubset_mem

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    (pickSubset s k hk).card = k :=
  (Finset.mem_powersetCard.mp (pickSubset_mem hk)).2
end N4Code
