-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.trace_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:14.263446+00:00
-- url     : https://prove2.me/submissions/ef334708-61a1-4059-88e6-c221a03c1147

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {y : w.adicCompletion L}
    (hy : y ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y ∈ v.adicCompletionIntegers K := by
  open ValuativeRel in
  have hint : IsIntegral 𝒪[v.adicCompletion K] y :=
    isIntegral_of_mem_integer v w ((mem_valuationInteger_iff w y).2 hy)
  have htr : IsIntegral 𝒪[v.adicCompletion K]
      (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y) :=
    Algebra.isIntegral_trace hint
  exact (mem_valuationInteger_iff v _).1 ((Valuation.integer.integers
    (ValuativeRel.valuation (v.adicCompletion K))).mem_of_integral htr)
end GroundTheory.Global.AdeleBaseChange
