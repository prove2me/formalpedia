-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:36.390698+00:00
-- url     : https://prove2.me/submissions/012063d6-5387-4d17-bc74-71b6bd00e667

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff

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
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  let f : 𝓞 K →+* ResidueField (v.adicCompletionIntegers K) :=
    (residue _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  have hker : ∀ s ∈ v.asIdeal, f s = 0 := fun s hs => by
    change residue _ _ = 0
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_iff]
    exact fun h => h hs
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine Finite.of_surjective (Ideal.Quotient.lift v.asIdeal f hker) fun y => ?_
  obtain ⟨y, rfl⟩ := residue_surjective y
  obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion K)) y.2 1
  refine ⟨Ideal.Quotient.mk _ s, ?_⟩
  rw [Ideal.Quotient.lift_mk]
  change residue _ _ = _
  rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  intro h
  have h' : Valued.v ((y : v.adicCompletion K) -
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K s)) = 1 := h
  rw [h', ← WithZero.exp_zero, WithZero.exp_le_exp] at hs
  omega
end GlobalTheory.SelfDualGenus
