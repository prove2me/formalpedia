-- Prove2me | solution 1 for GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:46.730724+00:00
-- url     : https://prove2.me/submissions/e7066572-ae81-41ca-a67c-46a2a49e09bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Hilbert90AdeleRingTensorQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (g : E ≃ₐ[F] E) : g = 1 ∨ g = c := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  by_contra hg
  push Not at hg
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact hg.2 ((hx g hg.1).trans (hx c hc).symm)
end GlobalTheory.AdLat
