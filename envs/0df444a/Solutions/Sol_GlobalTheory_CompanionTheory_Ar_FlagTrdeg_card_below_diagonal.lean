-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagTrdeg.card_below_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:37.174399+00:00
-- url     : https://prove2.me/submissions/4de5f56c-8d0a-4618-8f79-5b3715961e03

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg
theorem _root_.solution (n : ℕ) :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n * (n - 1) / 2 := by
  rw [show Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = Fintype.card (Σ a : Fin n, {b : Fin n // b < a}) from
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => b < a), Fintype.card_sigma]
  have h : ∀ a : Fin n, Fintype.card {b : Fin n // b < a} = a := by
    intro a
    rw [Fintype.card_subtype]
    have e : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by
      ext b
      simp
    rw [e, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
