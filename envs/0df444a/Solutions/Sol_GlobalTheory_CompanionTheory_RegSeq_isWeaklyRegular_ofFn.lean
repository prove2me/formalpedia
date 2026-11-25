-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:34.254138+00:00
-- url     : https://prove2.me/submissions/99d59540-a7f0-4edb-94e2-6cd036c8a311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndep
import Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_exists_ofList_append_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_isRegular_of_length_eq_spanFinrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing RingTheory.Sequence
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RegSeq
namespace GlobalTheory.CompanionTheory.RegSeq
theorem _root_.solution {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    IsWeaklyRegular R (List.ofFn f) := by
  obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal f hf hli
  exact ((isWeaklyRegular_append_iff R _ _).1
    (GlobalTheory.isRegular_of_length_eq_spanFinrank h1 h2).toIsWeaklyRegular).1
end GlobalTheory.CompanionTheory.RegSeq
