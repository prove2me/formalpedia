-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_norm_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:04.309667+00:00
-- url     : https://prove2.me/submissions/c653223d-1ea8-49f8-832e-fd26565fc861

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_lift_pow
import Theorems.Thm_GlobalTheory_SimMult_exists_norm_maximal
import Theorems.Thm_GlobalTheory_SimMult_exists_norm_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution [IsDedekindDomain O] [Module.Free ℤ O] [Module.Finite ℤ O] [CharZero O]
    (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1)
    (hne : ∀ P : Ideal O, P.IsMaximal → ∃ t, σ t - t ∉ P) (n : ℕ) (hn : 0 < n) (ν : ℤ)
    (hν : IsCoprime ν (n : ℤ)) : ∃ c, (n : O) ∣ c * σ c - ν := by
  set J : Ideal O := Ideal.span {(n : O)}
  have hJ : J ≠ ⊥ := by
    simp only [J, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  obtain ⟨μ, b, hμ⟩ := hν
  have hμ' : (ν : O) * μ - 1 ∈ J := by
    have := congrArg (Int.cast : ℤ → O) hμ
    push_cast at this
    exact Ideal.mem_span_singleton.2 ⟨-b, by linear_combination this⟩
  have hmax : ∀ P ∈ J.minimalPrimes, P.IsMaximal := fun P hP =>
    hP.1.1.isMaximal (fun h => hJ (le_bot_iff.1 (h ▸ hP.1.2)))
  obtain ⟨c, hc⟩ := exists_norm_finset σ hσ ν J.minimalPrimes
    (Ideal.finite_minimalPrimes_of_isNoetherianRing O J) hmax (by
      intro P hP
      have := hmax P hP
      have := Ideal.finiteQuotientOfFreeOfNeBot P (fun h => hJ (le_bot_iff.1 (h ▸ hP.1.2)))
      refine exists_norm_maximal σ hσ P (hne P (hmax P hP)) ν fun h => ?_
      apply (hmax P hP).ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.sub_mem (P.mul_mem_right (μ : O) h) (hP.1.2 hμ')
      simpa using this)
  have hc' : c * σ c - ν ∈ J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Ideal.mem_sInf.2 fun {P} hP => hc P hP
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg J (IsNoetherian.noetherian _)
  obtain ⟨c', -, h⟩ := lift_pow σ hσ hw J.radical ν μ (Ideal.le_radical hμ') c hc' k
  exact ⟨c', Ideal.mem_span_singleton.1 (hk h)⟩
end GlobalTheory.SimMult
