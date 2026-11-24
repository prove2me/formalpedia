-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.normsEscape_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:30.551916+00:00
-- url     : https://prove2.me/submissions/79eb7ccf-d95f-44bc-a1d9-a9121bfe7f9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_exists_sqrt_basis
import Theorems.Thm_GlobalTheory_Published_HasseNormSt_of_isSquare
import Theorems.Thm_GlobalTheory_QuadNormBase_norm_of_basis
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A B C : Type} [Field A] [Field B] [Field C]
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution [CharZero A] [Algebra A B] (hA : IndexTwo A)
    (hr : Module.finrank A B = 2) : NormsEscape A B := by
  intro d hd
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_sqrt_basis A B hr
  haveI : FiniteDimensional A B := Module.Finite.of_basis e
  by_contra hall
  push Not at hall
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hdA : ¬ IsSquare d := fun h => hd (h.map _)
  have hd0 : d ≠ 0 := fun h => hdA (h ▸ IsSquare.zero)
  have H1 : ∀ c : A, c ≠ 0 → Nm δ c → Nm d c := by
    rintro c hc ⟨a, b, h⟩
    have hn := GlobalTheory.QuadNormBase.norm_of_basis e δ h0
      (by rw [h1, h0, Algebra.algebraMap_eq_smul_one]) a b
    rw [← h] at hn
    rw [← hn]
    exact hall _ (Algebra.norm_ne_zero_iff.1 (by rw [hn]; exact hc))
  have H2 : ∀ c : A, c ≠ 0 → Nm d c → Nm δ c := by
    intro c hc hn
    obtain ⟨c', hc', hn'⟩ := (hA d hdA).1
    by_contra h
    exact hn' (Nm.of_mul hc hn (H1 _ (mul_ne_zero hc' hc)
      ((hA δ hδ).2 c' c hc' hc (fun h => hn' (H1 _ hc' h)) h)))
  have hdδ : ¬ IsSquare (d * δ) := by
    rintro ⟨r, hr⟩
    have ht : e 1 ≠ 0 := e.ne_zero 1
    refine hd ⟨algebraMap A B r / e 1, ?_⟩
    have := congrArg (algebraMap A B) hr
    rw [map_mul, map_mul, ← h1] at this
    field_simp
    linear_combination this
  obtain ⟨c, hc0, hc⟩ := (hA _ hdδ).1
  have hcs : ¬ IsSquare c := fun h => hc (Nm.of_isSquare _ h)
  refine hc (Nm.symm two_ne_zero (mul_ne_zero hd0 hδ0) ?_)
  by_cases h : Nm c d
  · exact h.mul ((H2 c hc0 (h.symm two_ne_zero hd0)).symm two_ne_zero hc0)
  · exact (hA c hcs).2 d δ hd0 hδ0 h
      fun h' => h ((H1 c hc0 (h'.symm two_ne_zero hδ0)).symm two_ne_zero hc0)
end GlobalTheory.QuadSymbol.NormBaseChange
