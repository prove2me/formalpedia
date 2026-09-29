-- Prove2me | solution 1 for ModularCurve.apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d76ab997-658e-5b86-8335-c6212d369a87

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_ModularCurve_heckeInputsFibre_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (q : ℕ) [NeZero q] [Fact q.Prime] (hqp : q ≠ p)
    (δ : Pic0.torsion K (modularFunctionFieldC K N) p →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldC K N)) (g : modularFunctionFieldC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) g)
    (x y : Pic0.torsion K (modularFunctionFieldC K N) p)
    (hy : (y : Pic0 K (modularFunctionFieldC K N)) =
      heckePic0Fibre K N q (x : Pic0 K (modularFunctionFieldC K N))) :
    δ y = Differential.traceAlong (heckeAlphaC K N q)
      (Differential.pullbackAlong (heckeBetaC K N q) (δ x)) := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hNK : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).mp h0)
  have hqK : (q : K) ≠ 0 := fun h0 =>
    hqp (((Nat.prime_dvd_prime_iff_eq hp hq).mp ((CharP.cast_eq_zero_iff K p q).mp h0)).symm)
  have hpNq : ¬ p ∣ N * q := fun h => by
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
    · exact hpN h1
    · exact hqp (((Nat.prime_dvd_prime_iff_eq hp hq).mp h2).symm)
  haveI hP : HasPrincipalDivisors K (charLDegeneracyRoof K N q) :=
    hasPrincipalDivisors_charLDegeneracyRoof K N q hNK hqK
  obtain ⟨hP', hβ, hα, hdesc⟩ := heckeInputsFibre_of_natCast_ne_zero K N q hqK
  have hsep : SeparableAlong K (heckeAlphaC K N q) :=
    (separableAlong_heckeAlphaC_heckeBetaC K N q hpNq).1
  have hfin : FiniteAlong K (heckeAlphaC K N q) := finiteAlong_heckeAlphaC K N q
  have hN : NormFormulaAlong K (heckeAlphaC K N q) hfin := normFormulaAlong_of_separableAlong _ hfin hsep
  rw [heckePic0Fibre_eq K N q hβ hα hdesc] at hy
  refine Pic0.torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence (heckeBetaC K N q)
    (heckeAlphaC K N q) hβ hα hfin hN hsep (fun E hE => hdesc.1 E hE)
    (Divisor.toPic0End (heckeDivFibre K N q hβ hα)) (fun E => ?_) p δ hδ x y hy
  rw [Divisor.toPic0End_mk _ hdesc]
  rfl

end S_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
end P2MW
export P2MW.S_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre (solution)
