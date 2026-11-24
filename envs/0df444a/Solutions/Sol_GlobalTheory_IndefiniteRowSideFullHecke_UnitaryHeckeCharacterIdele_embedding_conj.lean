-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:35.280255+00:00
-- url     : https://prove2.me/submissions/f4508cd8-d33f-41c7-8253-8422ce3c709b

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
theorem _root_.solution [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (φ : E →+* ℂ) (x : E) :
    φ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E x) = starRingEnd ℂ (φ (x)) := by
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField F E
  exact (IsCMField.isConj_complexConj E φ).eq x
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
