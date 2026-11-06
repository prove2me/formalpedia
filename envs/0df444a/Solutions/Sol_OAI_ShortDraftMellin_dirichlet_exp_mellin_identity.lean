-- Prove2me | solution 1 for OAI.ShortDraftMellin.dirichlet_exp_mellin_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:40.427203+00:00
-- url     : https://prove2.me/submissions/424e76a9-d67d-44e0-8e1b-6d2e8001b89c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exponential_mellin_identity
import Theorems.Thm_OAI_ShortDraftMellin_mobius_char_exp_summable

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s *
      mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s) =
        Complex.Gamma s := by
  apply dirichlet_exponential_mellin_identity χ (mobiusExpSum χ)
  · intro t ht
    exact (mobius_char_exp_summable χ t ht).hasSum
  · exact hs
end OAI.ShortDraftMellin
