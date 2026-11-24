-- Prove2me | solution 1 for GlobalTheory.DifferentElement.ord_vw_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:38.960474+00:00
-- url     : https://prove2.me/submissions/2f4ad969-d544-49a4-9348-cc0cde4f84c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement
namespace GlobalTheory.DifferentElement
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    ord_vw O (algebraMap O K (ϖ ^ n * u)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (u : O)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K ϖ) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  unfold ord_vw
  rw [map_mul, map_pow, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp
end GlobalTheory.DifferentElement
