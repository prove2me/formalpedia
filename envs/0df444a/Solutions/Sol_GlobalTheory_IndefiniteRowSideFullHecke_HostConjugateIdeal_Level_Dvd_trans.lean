-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level.Dvd.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:46.855239+00:00
-- url     : https://prove2.me/submissions/4371734b-6551-4710-b6ee-e6635a42546d

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
theorem _root_.solution {L L₂ L₃ : Level H} (h : L.Dvd L₂) (h' : L₂.Dvd L₃) : L.Dvd L₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩
end Dvd
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
