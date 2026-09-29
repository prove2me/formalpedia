-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/16fe19b4-2f37-59cf-9bdf-1f98f4308add

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import Theorems.Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi
import Theorems.Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot
import Theorems.Thm_ModularCurve_separable_cosetTwoVarPoly
import Theorems.Thm_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_single qExpand_injective jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg ModularPolynomialData jqModC primCosetReps cosetConj cosetTwoVarPoly algebraMap_laurentSeries_eq_single card_primCosetReps_eq_dedekindPsi eq_cosetTwoVarPoly_of_forall_isRoot separable_cosetTwoVarPoly ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex transcendental_jqModC"
namespace IgusaSepAux
p2m_open "ModularCurve"

theorem separable_map_ratFunc_of_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : Transcendental F x) (P : Polynomial (Polynomial F))
    (h : (P.map (Polynomial.aeval x).toRingHom).Separable) :
    (P.map (algebraMap (Polynomial F) (RatFunc F))).Separable := by
  have hinj : Function.Injective (Polynomial.aeval (R := F) x).toRingHom :=
    fun a b hab => (transcendental_iff_injective.mp hx) hab
  let θ : RatFunc F →+* E := IsFractionRing.lift hinj
  have hθ : θ.comp (algebraMap (Polynomial F) (RatFunc F)) = (Polynomial.aeval x).toRingHom :=
    RingHom.ext fun p => IsFractionRing.lift_algebraMap hinj p
  rw [← Polynomial.separable_map θ, Polynomial.map_map, hθ]
  exact h

theorem map_aeval_comp_mapRingHom_intCast {K E : Type*} [Field K] [CommRing E] [Algebra K E] (x : E)
    (Φ : Polynomial (Polynomial ℤ)) :
    (Φ.map (mapRingHom (Int.castRingHom K))).map (Polynomial.aeval x).toRingHom
      = Φ.map (eval₂RingHom (Int.castRingHom E) x) := by
  rw [Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* E => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem coeff_jqModC_neg_one (R : Type*) [CommRing R] : (jqModC R).coeff (-1) = 1 := by
  have h := HahnSeries.coeff_single_mul_add (a := (0 : ℤ)) (b := (-1 : ℤ)) (r := (1 : R))
    (x := HahnSeries.ofPowerSeries ℤ R (jNum.map (Int.castRingHom R)))
  rw [zero_add, one_mul] at h
  rw [jqModC, h]
  have h0 := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (jNum.map (Int.castRingHom R)) 0
  rw [Nat.cast_zero] at h0
  rw [h0, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]

theorem coeff_jqModC_of_lt (R : Type*) [CommRing R] {m : ℤ} (hm : m < -1) : (jqModC R).coeff m = 0 := by
  have h := HahnSeries.coeff_single_mul_add (a := m + 1) (b := (-1 : ℤ)) (r := (1 : R))
    (x := HahnSeries.ofPowerSeries ℤ R (jNum.map (Int.castRingHom R)))
  rw [show m + 1 + -1 = m by ring, one_mul] at h
  rw [jqModC, h, ofPowerSeries_coeff_of_neg _ (by omega)]

def qExpandAlg (L : Type*) [Field L] (M : ℕ) [NeZero M] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L M with
    commutes' := fun c => by
      show qExpand L M (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

theorem transcendental_qExpand_jqModC (L : Type*) [Field L] (M : ℕ) [NeZero M] :
    Transcendental L (qExpand L M (jqModC L)) := by
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  apply transcendental_jqModC L
  refine ⟨p, hp0, ?_⟩
  have h := Polynomial.aeval_algHom_apply (qExpandAlg L M) (jqModC L) p
  have h' : (qExpandAlg L M) (jqModC L) = qExpand L M (jqModC L) := rfl
  rw [h'] at h
  rw [h] at hp
  exact qExpand_injective M (by rw [map_zero]; exact hp)

end ModularCurve.IgusaSepAux

open ModularCurve.IgusaSepAux in
theorem solution (K : Type*) [Field K]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let L := AlgebraicClosure K
  let E := LaurentSeries L
  letI : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have halgK : ∀ c : K, algebraMap K E c = algebraMap L E (algebraMap K L c) := fun c => rfl

  haveI : NeZero ((N : ℕ) : K) := ⟨hNK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := N)
  set ζ : Lˣ := (hz.isUnit hN0).unit with hζdef
  have hζ : IsPrimitiveRoot ζ N := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [hζdef] using hz

  set x : E := qExpand L N (jqModC L) with hx
  set P : Polynomial E := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom E) x) with hP
  have hroots : ∀ t ∈ primCosetReps N, P.IsRoot (cosetConj ζ (jqModC L) t) :=
    ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex N data
      (ModularCurve.ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N data) L ζ hζ
  have hmonic : P.Monic := data.monic.map _
  have hdeg : P.natDegree = (primCosetReps N).card := by
    rw [hP, (data.monic).natDegree_map, data.natDegree_eq, ModularCurve.card_primCosetReps_eq_dedekindPsi N hN0]
  have hPeq : P = cosetTwoVarPoly ζ N (jqModC L) :=
    ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot L N hN0 ζ hζ (jqModC L)
      (by rw [coeff_jqModC_neg_one]; exact one_ne_zero) (fun m hm => coeff_jqModC_of_lt L hm)
      P hmonic hdeg hroots
  have hPsep : P.Separable := by
    rw [hPeq]
    exact ModularCurve.separable_cosetTwoVarPoly L N hN0 ζ hζ (jqModC L)
      (by rw [coeff_jqModC_neg_one]; exact one_ne_zero) (fun m hm => coeff_jqModC_of_lt L hm)

  have hxK : Transcendental K x := by
    rintro ⟨p, hp0, hp⟩
    apply transcendental_qExpand_jqModC L N
    refine ⟨p.map (algebraMap K L), (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hp
    convert hp using 2 <;> first | with_reducible_and_instances rfl | rfl
  apply separable_map_ratFunc_of_transcendental x hxK
  rw [map_aeval_comp_mapRingHom_intCast]
  exact hPsep

end

end S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero (solution)
