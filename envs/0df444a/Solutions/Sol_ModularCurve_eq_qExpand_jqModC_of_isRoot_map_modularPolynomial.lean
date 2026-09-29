-- Prove2me | solution 1 for ModularCurve.eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6284fa9d-63da-5930-b734-2161b41af880

import Mathlib
import Definitions.Def_ModularCurve_ModularEquationQ
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve~coeffMap_qExpand"

namespace RootUniq

variable {p : ℕ} [Fact p.Prime]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem coeff_jqModC_neg_one (K : Type*) [Field K] : (jqModC K).coeff (-1) ≠ 0 := by
  have h := order_jqModC_def K
  rw [← h]
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) (jqModC_ne_zero_def K)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N x hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem eq_qExpand_sq_of_isRoot_of_coeff_eq_zero
    (L : Type*) [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (data : ModularPolynomialData p)
    (r : LaurentSeries L) (hsupp : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → r.coeff k = 0)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (qExpand L p (jqModC L)))).IsRoot r) :
    r = qExpand L (p * p) (jqModC L) := by
  obtain ⟨-, -, -, hroots⟩ := ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly L p data ζ hζ
  have hmem : r ∈ (data.toJqNField L).rootSet (LaurentSeries L) := by
    rw [Polynomial.mem_rootSet']
    refine ⟨(Polynomial.map_monic_ne_zero (data.toJqNField_monic L)), ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ModularPolynomialData.toJqNField_map]
    exact hroot
  rw [hroots] at hmem
  obtain ⟨⟨a, b, d⟩, ht, rfl⟩ := hmem
  have hp : p.Prime := Fact.out
  obtain ⟨had, hbd, -⟩ := (mem_primCosetReps hp.ne_zero).mp (Finset.mem_coe.mp ht)
  have ha : a = 1 ∨ a = p := (Nat.dvd_prime hp).mp ⟨d, had.symm⟩
  rcases ha with rfl | rfl
  ·
    exfalso
    have h1 := hsupp (-1) (by
      rintro ⟨c, hc⟩
      have : (p : ℤ) ∣ 1 := ⟨-c, by linarith⟩
      have hp1 := Int.eq_one_of_dvd_one (by positivity) this
      exact hp.one_lt.ne' (by exact_mod_cast hp1))
    rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply,
      qExpand_congr (show 1 * 1 = 1 by norm_num), qExpand_one_apply, qTwist_coeff] at h1
    exact (mul_ne_zero (Units.ne_zero _) (coeff_jqModC_neg_one L)) h1
  ·
    have hd : d = 1 := by
      have := had; rw [Nat.mul_eq_left hp.ne_zero] at this; exact this
    subst hd
    have hb : b = 0 := by omega
    subst hb
    rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply, mul_zero, pow_zero, qTwist_one_apply]

theorem eq_qExpand_jqModC_of_isRoot (K : Type*) [Field K] [CharZero K] (data : ModularPolynomialData p) (r : LaurentSeries K)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K))).IsRoot r) :
    r = qExpand K p (jqModC K) := by
  have hζ := IsCyclotomicExtension.zeta_spec p K (CyclotomicField p K)
  have hζ0 : IsCyclotomicExtension.zeta p K (CyclotomicField p K) ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  let ζ : (CyclotomicField p K)ˣ := Units.mk0 _ hζ0
  have hζu : IsPrimitiveRoot ζ p := (IsPrimitiveRoot.coe_units_iff).mp (by simpa [ζ] using hζ)
  let ι : K →+* CyclotomicField p K := algebraMap K (CyclotomicField p K)
  let φ : LaurentSeries K →+* LaurentSeries (CyclotomicField p K) := (qExpand (CyclotomicField p K) p).comp (coeffMap ι)
  have hιj : coeffMap ι (jqModC K) = jqModC (CyclotomicField p K) := by
    ext k; rw [coeffMap_coeff, ← map_jqModC ι, HahnSeries.map_coeff]
  have hφj : φ (jqModC K) = qExpand (CyclotomicField p K) p (jqModC (CyclotomicField p K)) := by
    show qExpand _ p (coeffMap ι (jqModC K)) = _
    rw [hιj]

  have hroot' : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (CyclotomicField p K)))
      (qExpand (CyclotomicField p K) p (jqModC (CyclotomicField p K))))).IsRoot (φ r) := by
    have hcomp : φ.comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K)) =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (CyclotomicField p K)))
          (qExpand (CyclotomicField p K) p (jqModC (CyclotomicField p K))) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.eval₂_X, hφj]
    have := Polynomial.hom_eval₂ data.Φ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K)) φ r
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← hcomp, ← this]
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hroot
    rw [hroot, map_zero]
  have hsupp : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → (φ r).coeff k = 0 := fun k hk =>
    qExpand_coeff_of_not_dvd p _ hk
  have key := eq_qExpand_sq_of_isRoot_of_coeff_eq_zero (CyclotomicField p K) ζ hζu data (φ r) hsupp hroot'

  have : φ r = φ (qExpand K p (jqModC K)) := by
    rw [key]
    show _ = qExpand _ p (coeffMap ι (qExpand K p (jqModC K)))
    rw [coeffMap_qExpand, qExpand_qExpand, hιj]
  exact (coeffMap_injective ι ι.injective) (qExpand_injective (R := CyclotomicField p K) p this)

end RootUniq
p2m_reactivate "P2MW.S_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial.RootUniq"

theorem solution
    (K : Type*) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (data : ModularCurve.ModularPolynomialData p)
    (r : LaurentSeries K)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (ModularCurve.jqModC K))).IsRoot r) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    r = ModularCurve.qExpand K p (ModularCurve.jqModC K) := by
  exact RootUniq.eq_qExpand_jqModC_of_isRoot K data r hroot

end S_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
end P2MW
export P2MW.S_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial (solution)
