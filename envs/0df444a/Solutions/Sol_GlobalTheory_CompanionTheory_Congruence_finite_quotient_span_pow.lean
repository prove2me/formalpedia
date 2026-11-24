-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:16.396792+00:00
-- url     : https://prove2.me/submissions/028382c6-c462-4fd8-a2e1-10f6d253ec93

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteCosetsPrincipalCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Congruence
open Matrix
namespace GlobalTheory.CompanionTheory.Congruence
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (ϖ : R) (m : ℕ) (hϖ : Irreducible ϖ) :
    Finite (R ⧸ Ideal.span {ϖ ^ m}) := by
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    (inferInstance : Finite (IsLocalRing.ResidueField R))
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m
end GlobalTheory.CompanionTheory.Congruence
