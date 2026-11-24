-- Prove2me | solution 1 for GlobalTheory.ProjModClasses.mk0_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:47.520037+00:00
-- url     : https://prove2.me/submissions/95395d8a-e35c-4454-94f7-84a2c919a89e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModClasses
theorem _root_.solution (c : ClassGroup R) : ClassGroup.mk0 ⟨rep c, rep_mem c⟩ = c :=
  (ClassGroup.mk0_surjective (R := R) c).choose_spec
end GlobalTheory.ProjModClasses
