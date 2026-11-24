-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:53.250681+00:00
-- url     : https://prove2.me/submissions/c047a643-0fdf-431d-85b3-bcac33a040c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinFourierTermMoveUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBalancedUnitMultipleTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoTermIteratedFDerivSummableBound
import Theorems.Thm_GlobalTheory_T_exists_balanced_unit_multiple_totallyReal
import Theorems.Thm_GlobalTheory_T_heckeEisensteinFourierTerm_move_unit
import Theorems.Thm_GlobalTheory_T_norm_iteratedFDeriv_fTerm_le_of_isCompact
import Theorems.Thm_GlobalTheory_T_summable_heckeBalancedLatticeDoubleSum


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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  intro F _ _ _ 𝔞 𝔟 K hK hKH L hL hLU n
  obtain ⟨m, hm⟩ := GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact F K hK hKH L hL hLU n
  obtain ⟨C₀, -, hC₀⟩ := GlobalTheory.T.exists_balanced_unit_multiple_totallyReal F
  obtain ⟨N, hN⟩ := GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum F 𝔞 𝔟 C₀ m
  obtain ⟨C, hC⟩ := hm N
  choose ε hε using fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => hC₀ c.out.1 c.out.2.2
  refine ⟨fun p => C * ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N, (hN ε hε).mul_left C, ?_⟩
  rintro ⟨c, ν⟩ σ hσ z hz
  have hee : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
  have hfun : (fun z : Emb F → ℂ => fTerm σ z c.out.1 ν.1) =
      fun z => fTerm σ z (((ε c : 𝓞 F) : F) * c.out.1) (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) := by
    funext z
    have hb : c.out.1 = ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((ε c : 𝓞 F) : F) * c.out.1) := by
      rw [← mul_assoc, hee, one_mul]
    conv_lhs => rw [hb]
    exact GlobalTheory.T.heckeEisensteinFourierTerm_move_unit F σ z _ _ (ε c)⁻¹
  have hb0 : ((ε c : 𝓞 F) : F) * c.out.1 ≠ 0 := mul_ne_zero (right_ne_zero_of_mul_eq_one hee) c.out.2.2
  have hν0 : ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hee) ν.2.2
  dsimp only
  rw [hfun]
  refine (hC σ hσ z hz _ _ hb0 hν0).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrArg τ hee
  rw [map_mul, map_one] at h1
  have h2 : τ (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) * τ (((ε c : 𝓞 F) : F) * c.out.1) = τ ν.1 * τ c.out.1 := by
    rw [map_mul, map_mul]; linear_combination (τ ν.1 * τ c.out.1) * h1
  rw [h2]
end GlobalTheory.HeckeTwo
