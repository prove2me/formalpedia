-- Prove2me | solution 1 for GroundTheory.Global.valued_adicCompletionRingHomOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:13.548346+00:00
-- url     : https://prove2.me/submissions/7079cb01-3afe-4a17-afdb-00a77ee13cdc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
variable {w}
namespace GroundTheory.Global
theorem _root_.solution (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (adicCompletionRingHomOf w σ hσ y) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hz : Valued.v (adicCompletionRingHomOf w σ hσ y) ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const hy'
  have h2 := (continuous_adicCompletionRingHomOf σ hσ).continuousAt.preimage_mem_nhds
    (Valued.locally_const hz)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, adicCompletionRingHomOf_algebraMap]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' w]
  exact valuation_algEquiv_apply_of_smul_eq w hσ k
end GroundTheory.Global
