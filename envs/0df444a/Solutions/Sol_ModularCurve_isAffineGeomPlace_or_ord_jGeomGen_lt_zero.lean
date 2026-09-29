-- Prove2me | solution 1 for ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f0349c2e-038f-5cda-b0a3-d0f30e2b0468

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve Polynomial

namespace CoverGlue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem heightOneSpectrum_eq (v : Place K F) (u : IsDedekindDomain.HeightOneSpectrum v.toValuationSubring) :
    u = v.heightOneSpectrum := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have h1 : u.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.eq_maximalIdeal (u.isPrime.isMaximal u.ne_bot))
  have h2 : v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.eq_maximalIdeal (v.heightOneSpectrum.isPrime.isMaximal v.heightOneSpectrum.ne_bot))
  rw [h1, h2]

theorem mem_of_adicValuation_le_one (v : Place K F) {f : F} (hf : v.adicValuation f ≤ 1) :
    f ∈ v.toValuationSubring := by
  have hall : ∀ u : IsDedekindDomain.HeightOneSpectrum v.toValuationSubring, u.valuation F f ≤ 1 := by
    intro u
    rw [heightOneSpectrum_eq v u]
    exact hf
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F f hall
  rw [← hy]
  exact y.2

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) : v.ord f < 0 :=
  v.not_adicValuation_le_one_iff.mp (fun h => hf (mem_of_adicValuation_le_one v h))

end CoverGlue

open CoverGlue in
theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    IsAffineGeomPlace K N w ∨ w.ord (jGeomGen K N) < 0 := by
  classical
  by_cases hJ : jGeomGen K N ∈ w.toValuationSubring
  · left
    refine ⟨hJ, ?_⟩
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N

    set O := w.toValuationSubring with hO
    let jO : O := ⟨jGeomGen K N, hJ⟩
    let Q : Polynomial O := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom O) jO)
    have hQm : Q.Monic := data.monic.map _
    have hQ0 : Polynomial.eval₂ (algebraMap O ↥(modularFunctionFieldC K N)) (jNGeomGen K N) Q = 0 := by
      show Polynomial.eval₂ (algebraMap O ↥(modularFunctionFieldC K N)) (jNGeomGen K N)
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom O) jO)) = 0
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap O ↥(modularFunctionFieldC K N)).comp (Polynomial.eval₂RingHom (Int.castRingHom O) jO)
          = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
        refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        rfl
      rw [hcomp]
      exact evalModularPair_jGeomGen_eq_zero K N data
    have hint : IsIntegral O (jNGeomGen K N) := ⟨Q, hQm, hQ0⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := ↥(modularFunctionFieldC K N))).mp hint
    rw [← hy]
    exact y.2
  · right
    exact ord_neg_of_not_mem w hJ

end S_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
end P2MW
export P2MW.S_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero (solution)
