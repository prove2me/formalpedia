-- Prove2me | solution 1 for GlobalTheory.Unipotence.eq_zero_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:23.449049+00:00
-- url     : https://prove2.me/submissions/43f77b8b-c584-422c-acfc-bf3ce22994b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Theorems.Thm_GlobalTheory_SerreTorsion_eq_one_of_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.Unipotence
open Polynomial
namespace GlobalTheory.Unipotence
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {K : Type} [Field K] [CharZero K]
    [Algebra ℤ_[l] K] (μ : K) (hμ : IsIntegral ℤ_[l] μ) (m : ℕ) (hm : m ≠ 0)
    (h : (1 + l • μ) ^ m = 1) : μ = 0 := by
  let E := Algebra.adjoin ℤ_[l] ({μ} : Set K)
  haveI : Module.Finite ℤ_[l] E := Module.Finite.iff_fg.mpr hμ.fg_adjoin_singleton
  let ψ : E := ⟨μ, Algebra.self_mem_adjoin_singleton _ _⟩
  have hl0 : l ≠ 0 := by omega
  have key : (1 : E) + l • ψ = 1 := by
    refine SerreTorsion.eq_one_of_pow (E := E) (q := l) (c := l) ?_ hl.out ?_ hl0 dvd_rfl
      (fun h2 => by omega) m hm ψ ?_
    · intro n x hn hx
      have : (n : K) * (x : K) = 0 := by
        have := congrArg (Subtype.val : E → K) hx
        simpa using this
      exact Subtype.ext ((mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn))
    · intro x hx
      have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := ℤ_[l]) (M := E)
        (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      rw [← Submodule.mem_bot ℤ_[l], ← hk, Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy⟩ := hx k
      rw [hy, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
      refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ k) Submodule.mem_top
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    · apply Subtype.ext
      simpa [ψ] using h
  have := congrArg (Subtype.val : E → K) key
  simpa [ψ, hl0] using this
end GlobalTheory.Unipotence
