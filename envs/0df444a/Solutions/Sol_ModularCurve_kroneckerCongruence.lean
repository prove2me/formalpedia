-- Prove2me | solution 1 for ModularCurve.kroneckerCongruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/995f4c2e-ac78-5946-8c13-4bff1497467b

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerCongruence
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_kroneckerCongruence.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "ModularPolynomialData jqModC jqNModC map_jqModC jqInt jqIntN reduceModBivar KroneckerCongruence jqMod jqNMod modularPolynomial_kronecker" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.jqInt_eq_jqModC : jqInt = jqModC ℤ := by
  rw [jqInt, jqModC]
  congr 1

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.jqMod_eq_jqModC (ℓ : ℕ) : jqMod ℓ = jqModC (ZMod ℓ) := by
  rw [jqMod, jqInt_eq_jqModC]
  exact map_jqModC (Int.castRingHom (ZMod ℓ))

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.jqIntN_eq_jqNModC (N : ℕ) [NeZero N] : jqIntN N = jqNModC ℤ N := by
  rw [jqIntN, jqNModC, jqInt_eq_jqModC]

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.jqNMod_eq_jqNModC (ℓ N : ℕ) [NeZero N] :
    jqNMod ℓ N = jqNModC (ZMod ℓ) N := by
  rw [jqNMod, jqNModC, jqMod_eq_jqModC]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.kroneckerCongruence_of_map_eq (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ)
    (h : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ)) :
    KroneckerCongruence ℓ data := by
  show reduceModBivar ℓ data.Φ = _
  rw [reduceModBivar]
  exact h

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.kroneckerCongruence (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (data : ModularPolynomialData ℓ) : KroneckerCongruence ℓ data :=
  ModularCurve.kroneckerCongruence_of_map_eq ℓ data
    (ModularCurve.modularPolynomial_kronecker ℓ data)

namespace ModularCurve p2m_export "ModularCurve" "ModularPolynomialData jqModC jqNModC map_jqModC jqInt jqIntN reduceModBivar KroneckerCongruence jqMod jqNMod modularPolynomial_kronecker" namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "Φ" end ModularCurve.ModularPolynomialData
p2m_open_scoped "ModularCurve ModularCurve.ModularPolynomialData" in

theorem ModularCurve.ModularPolynomialData.aeval_diag_eq_zero_of_pow_eq_of_kronecker
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (data : ModularCurve.ModularPolynomialData ℓ)
    (hk : KroneckerCongruence ℓ data)
    {R : Type*} [CommRing R] [CharP R ℓ] (x : R) (hx : x ^ ℓ = x) :
    Polynomial.aeval x (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0 := by
  classical

  set k₁ : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) x with hk₁
  set k₂ : Polynomial (ZMod ℓ) →+* R :=
    Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) R) x with hk₂
  have hfac : k₁ = k₂.comp (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · exact RingHom.ext_int _ _
    · rw [RingHom.comp_apply]
      simp [hk₁, hk₂]

  have hX : k₁ Polynomial.X = x := by
    rw [hk₁]
    simp
  have h1 : Polynomial.aeval x (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X)
      = data.Φ.eval₂ k₁ x := by
    rw [Polynomial.aeval_def, algebraMap_int_eq, ← Polynomial.coe_eval₂RingHom, ← hk₁,
      Polynomial.hom_eval₂, RingHom.comp_id, hX]
  rw [h1, hfac, ← Polynomial.eval₂_map]
  have h2 : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))
      = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
          (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hk
  rw [h2, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
  simp only [hk₂, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hx, sub_self, zero_mul]

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_kroneckerCongruence.ModularCurve in

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : KroneckerCongruence ℓ data :=
  ModularCurve.kroneckerCongruence ℓ data

#print axioms solution

end S_ModularCurve_kroneckerCongruence
end P2MW
export P2MW.S_ModularCurve_kroneckerCongruence (solution)
