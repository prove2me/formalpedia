-- Prove2me | solution 1 for GlobalTheory.T.weakly_regular_of_cotangent_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:44.554589+00:00
-- url     : https://prove2.me/submissions/aa970456-bfd4-4dfa-8dbb-b9b05d1fba51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndep
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndepStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_isWeaklyRegular_and_length_quotient_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ) (a : Fin d → R), ringKrullDim R ≤ d → LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} => ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) → RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧ Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | exact GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | (intros; apply GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one <;> assumption)
end _root_.GlobalTheory.T
