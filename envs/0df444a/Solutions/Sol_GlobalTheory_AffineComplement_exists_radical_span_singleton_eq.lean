-- Prove2me | solution 1 for GlobalTheory.AffineComplement.exists_radical_span_singleton_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:29.070287+00:00
-- url     : https://prove2.me/submissions/89488e6d-55cd-472c-9b70-dbd8956331c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AffineComplement
open ReciprocityTheory.AnForm.R
namespace GlobalTheory.AffineComplement
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {a : A} (ha : a ≠ 0) :
    ∃ t ∈ nonZeroDivisors A, (Ideal.span {a}).radical = Ideal.span {t} := by
  obtain ⟨y, n, hy, hya, hay⟩ := exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨y, mem_nonZeroDivisors_of_ne_zero hy.ne_zero, le_antisymm ?_ ?_⟩
  · rw [← (isRadical_iff_span_singleton.1 hy.isRadical).radical]
    exact Ideal.radical_mono (Ideal.span_singleton_le_span_singleton.2 hya)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact ⟨n, Ideal.mem_span_singleton.2 hay⟩
end GlobalTheory.AffineComplement
