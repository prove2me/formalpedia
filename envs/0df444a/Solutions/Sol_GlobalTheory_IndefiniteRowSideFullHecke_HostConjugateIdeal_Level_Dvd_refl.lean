-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level.Dvd.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:11.960172+00:00
-- url     : https://prove2.me/submissions/a049f19c-444d-4af1-a974-a421c6eb69e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
variable {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
namespace Dvd
theorem _root_.solution (L : Level H) : L.Dvd L := ⟨dvd_rfl, dvd_rfl, dvd_rfl⟩
end Dvd
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
