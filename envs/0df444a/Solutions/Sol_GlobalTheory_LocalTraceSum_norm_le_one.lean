-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:09.126015+00:00
-- url     : https://prove2.me/submissions/9347a450-7300-463a-a2e2-6e8c1b1fba19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_mem_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution (σ : F →+* Ω) (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal = ker σ)
    {a : F} (ha : p.valuation F a ≤ 1) : ‖σ a‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
  have hd : ¬ ‖σ (d : 𝓞 F)‖ < 1 := by
    rw [← mem_ker, ← hp]; exact d.2
  have h1 : ‖σ a‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun x => ‖σ x‖) h
  have h2 := norm_int_le σ n
  nlinarith [norm_nonneg (σ a), not_lt.1 hd]
end GlobalTheory.LocalTraceSum
