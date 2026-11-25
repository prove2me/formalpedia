-- Prove2me | solution 1 for GlobalTheory.CMLatticeRow.statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:54.766941+00:00
-- url     : https://prove2.me/submissions/976c2ff0-4b0f-44ec-b1bb-8c5188deefa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DividedPowersValuationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfTraceDualElementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFirstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecondStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThirdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFourthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodValuationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarisationDualStatement
import Theorems.Thm_GlobalTheory_CMLatticeRow_qt
import Theorems.Thm_GlobalTheory_CMLatticeRow_condT
import Theorems.Thm_GlobalTheory_CMLatticeRow_dualCrit
import Theorems.Thm_GlobalTheory_CMLatticeRow_unram
import Theorems.Thm_GlobalTheory_CMLatticeRow_diffEx
import Theorems.Thm_GlobalTheory_CMLatticeRow_valPow
import Theorems.Thm_GlobalTheory_CMLatticeRow_a1
import Theorems.Thm_GlobalTheory_CMLatticeRow_a2
import Theorems.Thm_GlobalTheory_CMLatticeRow_a3
import Theorems.Thm_GlobalTheory_CMLatticeRow_a4
import Theorems.Thm_GlobalTheory_CMLatticeRow_a5
import Theorems.Thm_GlobalTheory_CMLatticeRow_pb
import Theorems.Thm_GlobalTheory_CMLatticeRow_la
import Theorems.Thm_GlobalTheory_CMLatticeRow_lb1
import Theorems.Thm_GlobalTheory_CMLatticeRow_lb2
import Theorems.Thm_GlobalTheory_CMLatticeRow_lb3
import Theorems.Thm_GlobalTheory_CMLatticeRow_lc
import Theorems.Thm_GlobalTheory_CMLatticeRow_det
import Theorems.Thm_GlobalTheory_CMLatticeRow_fa
import Theorems.Thm_GlobalTheory_CMLatticeRow_fb
import Theorems.Thm_GlobalTheory_CMLatticeRow_dp0
import Theorems.Thm_GlobalTheory_CMLatticeRow_dp1
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConductorValuations_condExp_bdd
import Theorems.Thm_GlobalTheory_T_divided_powers_valuations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.CMLatticeRow
namespace GlobalTheory.CMLatticeRow
theorem _root_.solution : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ _ 𝔣 h𝔣 l hl O _ _ _ _ K _ _ _ hlO hcard
    refine ⟨?_, fun Q _ hQl D => qt E 𝔣 Q l hl hQl O K hlO D⟩
    by_cases hdiv : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
    · obtain ⟨v, hv𝔣, hvl⟩ := hdiv
      have hl' : ¬ (l : ℤ) ∣ discr E := by
        obtain ⟨_, _, l', hl'p, _, hl'v, hdisc, _⟩ := h𝔣.2.2 v hv𝔣
        have hll : l' = l := by
          by_contra hne
          have hcop : IsCoprime ((l' : ℤ) : OF E) ((l : ℤ) : OF E) :=
            (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl'p hl).2 hne)).intCast
          obtain ⟨a, b, hab⟩ := hcop
          have h1 : (1 : OF E) ∈ v.asIdeal := by
            rw [← hab]
            push_cast
            exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hl'v) (v.asIdeal.mul_mem_left _ hvl)
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        exact hll ▸ hdisc
      refine ⟨(l : O) ^ condExp 𝔣 l, fun P _ => ?_, ?_⟩
      · rw [cNum_vp, if_pos ⟨v, hv𝔣, hvl⟩]
        exact valPow O K l hl.ne_zero hlO _
      · have h1 : ClearsIdem K (⊤ : Ideal (OF E)) (1 : O) := dualCrit E O K hcard 1 (fun σ y hy => by
          obtain ⟨z, hz⟩ := unram E l hl hl' O K hlO σ y hy
          exact ⟨z, by rw [hz, map_one, one_mul]⟩)
        have := condT E 𝔣 h𝔣.1 l hl (condExp 𝔣 l)
          (fun w hw => le_csSup (condExp_bdd 𝔣 hl.ne_zero) ⟨w, hw, rfl⟩) O K hlO 1 h1
        rwa [mul_one] at this
    · obtain ⟨D, hv, hD⟩ := diffEx E l hl O K hlO hcard
      refine ⟨D, fun P hP => ?_, ?_⟩
      · rw [cNum_vp, if_neg hdiv]
        exact hv P hP
      · have hz : ∀ w : HeightOneSpectrum (OF E), (l : OF E) ∈ w.asIdeal → expIn 𝔣 w ≤ 0 := by
          intro w hw
          have : ¬ w.asIdeal ∣ 𝔣 := fun h => hdiv ⟨w, h, hw⟩
          exact le_of_eq (multiplicity_eq_zero.2 this)
        have := condT E 𝔣 h𝔣.1 l hl 0 hz O K hlO D (dualCrit E O K hcard D hD)
        rwa [pow_zero, one_mul] at this
  · intro E _ _ _ 𝔣 h𝔣 l hl Q _ hQl O _ _ _ _ K _ _ _ hlO hcard D hD0 hD I _ φ hφ H _ _ ρ Fil B hL
    have hc : condQ 𝔣 Q ≠ ⊥ := by
      unfold condQ
      rw [Ne, Ideal.mul_eq_bot, not_or]
      refine ⟨h𝔣.1, ?_⟩
      rw [← Ne, ← Ideal.zero_eq_bot]
      exact Finset.prod_ne_zero_iff.2 fun q _ => by rw [Ideal.zero_eq_bot]; exact q.ne_bot
    have hDc : ClearsIdem K (condQ 𝔣 Q) D := (qt E 𝔣 Q l hl hQl O K hlO D).2 hD
    have hE : EigenClaims φ ρ Fil B D := by
      have hI := a1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL
      exact ⟨hI, a2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hI,
        a4 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL,
        a5 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL⟩
    refine ⟨hE, fun e f hg => ?_⟩
    have hP := pb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg
    refine ⟨hP, ⟨la E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg, fun N hN => ?_⟩,
      det E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg,
      fb E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg hP
        (fa E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE)⟩
    obtain ⟨h1, h2⟩ := lb2 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    obtain ⟨h3, h4⟩ := lb3 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN
    exact ⟨lb1 E _ hc l hl O K hlO hcard D hD0 hDc I φ hφ H ρ Fil B hL hE e f hg N hN, h1, h2, h3, h4,
      fun M hM R _ _ t => lc E _ O K H hL.1 ρ B I N D M hM h1 h2 h3 h4 l R t⟩
  · intro l hl
    have hnum : ∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧
        m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m) := by
      obtain ⟨h1, h2, _⟩ := GlobalTheory.T.divided_powers_valuations
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      by_cases h2l : l = 2
      · subst h2l
        have := h2 m hm
        rw [show lPrimeExp 2 = 2 from rfl]
        omega
      · have := h1 l m hl h2l hm
        rw [show lPrimeExp l = 1 from if_neg h2l]
        omega
    refine ⟨hnum, fun O _ _ _ _ hlO R _ _ htf => ?_⟩
    obtain ⟨γ₀, hγ₀⟩ := dp0 l hl O hlO R htf
    obtain ⟨γ, hγ⟩ := dp1 l hl hnum O hlO R htf γ₀ hγ₀
    exact ⟨γ, γ₀, hγ.1, hγ₀, hγ.2⟩
end GlobalTheory.CMLatticeRow
