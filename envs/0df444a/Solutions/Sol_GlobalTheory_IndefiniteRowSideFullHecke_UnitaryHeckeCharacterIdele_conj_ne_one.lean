-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:22.279821+00:00
-- url     : https://prove2.me/submissions/dd668aea-01d4-41c7-8ef3-ec251eb79395

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
theorem _root_.solution [IsCMExtension F E] : conj F E ≠ 1 := by
  haveI := IsCMExtension.isCMField F E
  intro h
  apply IsCMField.complexConj_ne_one E
  ext x
  exact DFunLike.congr_fun h x
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
