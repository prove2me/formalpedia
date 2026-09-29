-- Prove2me | solution 1 for ModularCurve.derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8ca88980-ec35-5c17-978e-94338df73401

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne_of_isSeparable
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one.ModularCurve Polynomial"

namespace ModularCurve p2m_export "ModularCurve" "jqModC modularFunctionFieldC qExpand_one_apply jq jqN dedekindPsi_one ModularPolynomialData swapBivar swapBivar_X swapBivar_C_X jGeomGen jNGeomGen transcendental_jqNModC evalModularPair evalModularPair_jGeomGen_eq_zero IsCentreOf exists_isCentreOf_of_isRational transcendental_jqModC finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero ModularPolynomialData.evalSymm_of_one_lt swapBivar_eq_of_evalSymm ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero place_deg_eq_one_of_isAlgClosed" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.evalEval_map_map_intCast_eq_evalModularPair {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (x y : S) :
    ((Φ.map (Polynomial.mapRingHom (Int.castRingHom R))).map (Polynomial.mapRingHom f)).evalEval x y
      = evalModularPair x y Φ := by
  rw [Polynomial.map_map, Polynomial.mapRingHom_comp,
    RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]
  unfold evalModularPair Polynomial.evalEval
  rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂, Polynomial.coe_evalRingHom,
    Polynomial.eval_C]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval_map]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.evalModularPair_swapBivar {R : Type*} [CommRing R] (x y : R) (Φ : Polynomial (Polynomial ℤ)) :
    evalModularPair x y (swapBivar Φ) = evalModularPair y x Φ := by
  have h : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) y).comp swapBivar
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) y) x := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp only [RingHom.comp_apply, swapBivar_C_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
    · simp only [RingHom.comp_apply, swapBivar_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
  have h' := congrArg (fun g : Polynomial (Polynomial ℤ) →+* R => g Φ) h
  simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom] at h'
  exact h'

theorem solution
    (q : ℕ) (k : Type*) [Field k] [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (v : Place k ↥(modularFunctionFieldC k N)) (c : k × k) (hc : IsCentreOf k N c v)
    (huniq : ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v)
    (hord : v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1) :
    (Polynomial.derivative ((swapBivar data.Φ).map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval c.2 c.1 ≠ 0 := by
  classical
  have hNk : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  rcases Nat.lt_or_ge 1 N with hN1 | hN1
  ·

    have hsym : swapBivar data.Φ = data.Φ :=
      swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_one_lt N hN1 data)
    rw [hsym]

    have hrat : ∀ w : Place k ↥(modularFunctionFieldC k N), w.IsRational := fun w =>
      (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed k N w)

    obtain ⟨hfd, hsepF⟩ := finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero k N hNk data
    haveI hfd' : FiniteDimensional
        ↥(IntermediateField.adjoin k ({jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
        ↥(modularFunctionFieldC k N) := hfd
    haveI hsepF' : Algebra.IsSeparable
        ↥(IntermediateField.adjoin k ({jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
        ↥(modularFunctionFieldC k N) := hsepF

    set G : Polynomial (Polynomial k) := data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)) with hGdef
    have hGmonic : G.Monic := data.monic.map _
    have hGirr : Irreducible G :=
      (hGmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).mpr
        (ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero k N data hNk)

    have hz : Transcendental k (jNGeomGen k N) := by
      rw [← transcendental_algebraMap_iff
        (algebraMap ↥(modularFunctionFieldC k N) (LaurentSeries k)).injective]
      exact transcendental_jqNModC k N

    have hGrel : (G.map (Polynomial.mapRingHom (algebraMap k ↥(modularFunctionFieldC k N)))).evalEval
        (jNGeomGen k N) (jGeomGen k N) = 0 := by
      rw [hGdef, evalEval_map_map_intCast_eq_evalModularPair, ← evalModularPair_swapBivar, hsym]
      exact evalModularPair_jGeomGen_eq_zero k N data

    have hvz : v.evalAt (jNGeomGen k N) = c.2 := hc.evalAt_jNGeomGen
    have hvy : v.evalAt (jGeomGen k N) = c.1 := hc.evalAt_jGeomGen
    have he : v.ord (jNGeomGen k N
        - algebraMap k ↥(modularFunctionFieldC k N) (v.evalAt (jNGeomGen k N))) = 1 := by
      rw [hvz]; exact hord
    have hlead : G.leadingCoeff.eval (v.evalAt (jNGeomGen k N)) ≠ 0 := by
      rw [hGmonic.leadingCoeff, Polynomial.eval_one]; exact one_ne_zero

    have hsep : ∀ Q' : Place k ↥(modularFunctionFieldC k N), Q' ≠ v →
        jNGeomGen k N ∈ Q'.toValuationSubring → Q'.evalAt (jNGeomGen k N) = v.evalAt (jNGeomGen k N) →
        jGeomGen k N ∈ Q'.toValuationSubring → Q'.evalAt (jGeomGen k N) ≠ v.evalAt (jGeomGen k N) := by
      intro Q' hne hz' hzv hy' hyv
      apply hne
      apply huniq
      have hc' := exists_isCentreOf_of_isRational (hrat Q') ⟨hy', hz'⟩
      rw [hzv, hyv, hvz, hvy] at hc'
      simpa only [Prod.mk.eta] using hc'

    have key := Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne_of_isSeparable
      (jNGeomGen k N) hrat hz G hGirr hGrel v hc.jNGeomGen_mem hc.jGeomGen_mem he hlead hsep
    rwa [hvz, hvy] at key
  ·

    have hN : N = 1 := le_antisymm hN1 NeZero.one_le
    subst hN
    have hΦ : data.Φ = Polynomial.X - Polynomial.C Polynomial.X := by
      have hdeg : data.Φ.natDegree = 1 := by rw [data.natDegree_eq, dedekindPsi_one]
      have hXa := data.monic.eq_X_add_C hdeg
      have hrel := data.eval_eq_zero
      rw [hXa, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C] at hrel
      have hj1 : jqN 1 = jq := qExpand_one_apply _
      rw [hj1] at hrel

      have h2 : Polynomial.aeval (jqModC ℚ) ((Polynomial.X + data.Φ.coeff 0).map (Int.castRingHom ℚ)) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map,
          RingHom.ext_int ((algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ))
            (algebraMap ℤ (LaurentSeries ℚ)),
          ← Polynomial.aeval_def, map_add, Polynomial.aeval_X]
        exact hrel
      have h3' := transcendental_iff.mp (transcendental_jqModC ℚ) _ h2
      have h3 : Polynomial.X + data.Φ.coeff 0 = 0 :=
        Polynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
          (by rw [h3', Polynomial.map_zero])
      rw [hXa, eq_neg_of_add_eq_zero_right h3, map_neg, ← sub_eq_add_neg]
    rw [hΦ]
    simp only [map_sub, swapBivar_X, swapBivar_C_X, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X]
    simp [Polynomial.evalEval]

end S_ModularCurve_derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one
end P2MW
export P2MW.S_ModularCurve_derivative_swapBivar_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jNGeomGen_sub_eq_one (solution)
