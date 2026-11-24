-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.card_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:07.17092+00:00
-- url     : https://prove2.me/submissions/580c4eb5-53b6-4fbc-b018-aa6aae297e37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_sup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    (pts (D ⊔ Submodule.span R {x})).card = Fintype.card (R ⧸ P) * (pts D).card := by
  have h := sum_sup hP (fun _ => (1 : ℕ))
  simpa [Finset.sum_const, Finset.card_univ] using h
end GlobalTheory.HermitianGauss
