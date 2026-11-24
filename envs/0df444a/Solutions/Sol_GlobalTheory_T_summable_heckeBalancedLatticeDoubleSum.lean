-- Prove2me | solution 1 for GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:18.583799+00:00
-- url     : https://prove2.me/submissions/dd252d41-436d-4173-9f62-c0cc8327185a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSumStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_summable_balanced_latSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  first | exact @GlobalTheory.HeckeTwo.summable_balanced_latSum | exact GlobalTheory.HeckeTwo.summable_balanced_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_balanced_latSum <;> assumption)
end _root_.GlobalTheory.T
