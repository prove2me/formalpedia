-- Prove2me | solution 1 for GlobalTheory.T.multiset_conjugate_neg_of_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:35.492637+00:00
-- url     : https://prove2.me/submissions/74d74c64-070c-497d-b00c-d098bea0ed68

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProd
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProdStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Clozel_multiset_eq_map_neg_conj_of_polyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | exact GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | (intros; apply GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq <;> assumption)
end _root_.GlobalTheory.T
