-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.finite_quotient_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:50.126177+00:00
-- url     : https://prove2.me/submissions/74193569-7cea-4271-9a2e-5f1a1b087c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O m : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Finite m] {c : O}
    (hc : c ≠ 0) : Finite ((m → O) ⧸ (Ideal.span {c} • (⊤ : Submodule O (m → O)))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {c}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  exact Submodule.finite_quotient_smul (Ideal.span {c}) (N := ⊤) Module.Finite.fg_top
end GlobalTheory.LatticeIndicator
