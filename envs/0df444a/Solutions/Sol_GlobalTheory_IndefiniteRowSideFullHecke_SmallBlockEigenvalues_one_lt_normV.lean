-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.one_lt_normV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:08.614471+00:00
-- url     : https://prove2.me/submissions/bfac8ccd-900b-4ad1-a11d-90513bf6ff06

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
theorem _root_.solution {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  unfold normV
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact Finite.one_lt_card
end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
