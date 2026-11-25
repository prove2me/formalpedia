-- Prove2me | solution 1 for GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:15:34.115906+00:00
-- url     : https://prove2.me/submissions/eea5e109-2120-4255-ac8a-710885144fa1

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Theorems.Thm_GlobalTheory_QuadraticValuationIndexTwo_exists_subgroup_index_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex
open GlobalTheory GlobalTheory.QuadraticValuationIndexTwo
namespace GlobalTheory.QuadraticValuationIndexTwo
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
      ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  obtain ⟨N, hN, hmem⟩ := exists_subgroup_index_two F v B d hd
  refine ⟨?_, ?_⟩
  ·
    have hne : N ≠ ⊤ := by
      rintro rfl
      rw [Subgroup.index_top] at hN
      exact absurd hN (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : Bˣ, c ∉ N := by
      by_contra hall
      apply hne
      rw [eq_top_iff]
      intro c _
      by_contra hc
      exact hall ⟨c, hc⟩
    exact ⟨c, c.ne_zero, fun h => hc ((hmem c).mpr h)⟩
  · intro x y hx hy hnx hny
    have hx' : Units.mk0 x hx ∉ N := fun h => hnx ((hmem _).mp h)
    have hy' : Units.mk0 y hy ∉ N := fun h => hny ((hmem _).mp h)
    have : Units.mk0 x hx * Units.mk0 y hy ∈ N :=
      (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hx' hy')
    exact (hmem _).mp this
end GlobalTheory.QuadraticValuationIndexTwo
