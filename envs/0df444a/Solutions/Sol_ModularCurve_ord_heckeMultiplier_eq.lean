-- Prove2me | solution 1 for ModularCurve.ord_heckeMultiplier_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/45142d30-a0e6-5cab-af4c-aaca5af00899

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_heckeMultiplier_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve KaehlerDifferential

theorem solution
    (k : Type*) [Field k] [PerfectField k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (hα : (heckeAlphaC k N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC k N ℓ).toRingHom.IsIntegral)
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)]
    [FiniteDimensional ↥(IntermediateField.adjoin k ({heckeAlphaC k N ℓ (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ))) ↥(charLDegeneracyRoof k N ℓ)]
    (h : ↥(charLDegeneracyRoof k N ℓ))
    (hD : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N))
          = h • pullbackDiff (heckeAlphaC k N ℓ) (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)))
    (hDα : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeAlphaC k N ℓ (jGeomGen k N)) ≠ 0)
    (hDβ : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N)) ≠ 0)
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (heα : ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℕ) : k) ≠ 0)
    (heβ : ((Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℕ) : k) ≠ 0) :
    y.ord h
      = ((Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ)
            * (y.restrictAlong (heckeBetaC k N ℓ) hβ).ordDiff
                (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
          + (Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ))
        - ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ)
            * (y.restrictAlong (heckeAlphaC k N ℓ) hα).ordDiff
                (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
          + (Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ)) := by

  have hDj : KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N) ≠ 0 := by
    intro h0
    apply hDα
    rw [← pullbackDiff_D, h0, map_zero]

  have hh : h ≠ 0 := by
    intro h0
    apply hDβ
    rw [hD, h0, zero_smul]

  have hωα : pullbackDiff (heckeAlphaC k N ℓ) (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)) ≠ 0 := by
    rw [pullbackDiff_D]; exact hDα

  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({(heckeAlphaC k N ℓ) (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ))) ↥(charLDegeneracyRoof k N ℓ) :=
    Algebra.IsAlgebraic.of_finite _ _

  have e1 : y.ordDiff (KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) ((heckeBetaC k N ℓ) (jGeomGen k N)))
      = (Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ) * (y.restrictAlong (heckeBetaC k N ℓ) hβ).ordDiff (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
        + ((Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ) - 1) := by
    rw [← pullbackDiff_D]
    exact Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero (jGeomGen k N) ((heckeAlphaC k N ℓ) (jGeomGen k N)) (heckeBetaC k N ℓ) hβ y hDj heβ

  have e2 : y.ordDiff (KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) ((heckeBetaC k N ℓ) (jGeomGen k N)))
      = y.ord h + ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ) * (y.restrictAlong (heckeAlphaC k N ℓ) hα).ordDiff (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
        + ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ) - 1)) := by
    rw [hD, Place.ordDiff_smul_of_perfectField ((heckeAlphaC k N ℓ) (jGeomGen k N)) y hh hωα,
      Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero (jGeomGen k N) ((heckeAlphaC k N ℓ) (jGeomGen k N)) (heckeAlphaC k N ℓ) hα y hDj heα]

  have e3 := e1.symm.trans e2
  linarith

end S_ModularCurve_ord_heckeMultiplier_eq
end P2MW
export P2MW.S_ModularCurve_ord_heckeMultiplier_eq (solution)
