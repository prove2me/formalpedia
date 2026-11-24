-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricUnit.char_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:54.242971+00:00
-- url     : https://prove2.me/submissions/040874f5-ce04-4388-8263-8217b98f503d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
theorem _root_.solution {k α : Type} [AddCommGroup k] (ψ : AddChar k ℂ) (s : Finset α) (f : α → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
end GlobalTheory.CompanionTheory.SW.QuadricUnit
