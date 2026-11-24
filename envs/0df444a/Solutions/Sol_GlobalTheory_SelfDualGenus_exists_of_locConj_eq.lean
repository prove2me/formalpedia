-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_of_locConj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:35.231053+00:00
-- url     : https://prove2.me/submissions/d2b100e4-5e52-478a-83bb-a38acb2579bb

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_coord
import Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution {z : LocAlg v} (hz : locConj v z = z) :
    ∃ a : v.adicCompletion (maximalRealSubfield E), algebraMap _ (LocAlg v) a = z := by
  obtain ⟨θ, h0, hθ⟩ := Published.exists_cc_eq_neg E
  obtain ⟨p, q, rfl⟩ := exists_coord v h0 hθ z
  rw [map_add, map_mul, locConj_algebraMap, locConj_algebraMap, locConj_locEmb, hθ, map_neg] at hz
  have hu : IsUnit (locEmb v (2 * θ)) := (IsUnit.mk0 _ (mul_ne_zero two_ne_zero h0)).map _
  have : algebraMap _ (LocAlg v) q = 0 := by
    rw [← hu.mul_left_eq_zero, map_mul, map_ofNat]
    linear_combination -hz
  exact ⟨p, by rw [this, zero_mul, add_zero]⟩
end GlobalTheory.SelfDualGenus
