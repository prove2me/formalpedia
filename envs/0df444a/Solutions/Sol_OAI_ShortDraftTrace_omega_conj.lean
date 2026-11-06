-- Prove2me | solution 1 for OAI.ShortDraftTrace.omega_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:16:55.96204+00:00
-- url     : https://prove2.me/submissions/afef1f61-7fbc-464f-a6be-ad10fe3e5d25

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftTrace
open Complex
open scoped ComplexConjugate
namespace OAI.ShortDraftTrace
theorem _root_.solution : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring
end OAI.ShortDraftTrace
