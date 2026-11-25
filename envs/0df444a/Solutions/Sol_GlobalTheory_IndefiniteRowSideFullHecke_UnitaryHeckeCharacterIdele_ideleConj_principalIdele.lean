-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:59:34.111625+00:00
-- url     : https://prove2.me/submissions/56940af9-49b8-4cb2-8315-1bc747e0f094

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (x : Eˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E
        (Units.map (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toMonoidHom x) :=
  @_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele E E _ _ _ _
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra x
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
