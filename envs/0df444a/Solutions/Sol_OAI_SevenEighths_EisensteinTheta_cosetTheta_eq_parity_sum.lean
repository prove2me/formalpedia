-- Prove2me | solution 1 for OAI.SevenEighths.EisensteinTheta.cosetTheta_eq_parity_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:15.227672+00:00
-- url     : https://prove2.me/submissions/68e4ea5c-110e-4d14-af7f-a83899003dfe

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_cosetTheta_hasSum

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    cosetTheta a b L t = ∑ e : Fin 2, (parityPair a b L hL e).f t :=
  (cosetTheta_hasSum a b L hL ht).tsum_eq
end OAI.SevenEighths.EisensteinTheta
