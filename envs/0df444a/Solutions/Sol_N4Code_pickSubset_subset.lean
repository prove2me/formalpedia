-- Prove2me | solution 1 for N4Code.pickSubset_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:05.151313+00:00
-- url     : https://prove2.me/submissions/d1d8c329-d84e-4c16-9ce1-c440197c1393

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_pickSubset_mem

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ⊆ s :=
  (Finset.mem_powersetCard.mp (pickSubset_mem hk)).1
end N4Code
