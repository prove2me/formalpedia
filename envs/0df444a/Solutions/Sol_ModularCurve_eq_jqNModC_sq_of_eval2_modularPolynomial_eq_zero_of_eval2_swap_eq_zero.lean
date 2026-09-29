-- Prove2me | solution 1 for ModularCurve.eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/23121b04-5435-554e-ac32-dd4f19e57a39

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_ModularCurve_ModularEquationQ
import Theorems.Thm_ModularCurve_ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr qExpand_qExpand ModularPolynomialData jqModC jqNModC map_jqModC coeffMap coeffMap_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist cosetSubst primCosetReps mem_primCosetReps cosetConj cosetConj_eq cosetTwoVarPoly ModularPolynomialData.toJqNField_map ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly coeff_jqModC_neg_one coeff_jqModC_pow_of_lt coeffMap_qExpand"
p2m_open "ModularCurve"

namespace CommonRoot

section Generic

variable {K : Type*} [Field K]

theorem aeval_toRingHom_eq (x : LaurentSeries K) :
    (Polynomial.aeval (R := ℤ) x).toRingHom =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  show Polynomial.aeval x (Polynomial.X : Polynomial ℤ) = _
  rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem jqNModC_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    jqNModC K m = jqNModC K n := by
  subst h
  rfl

theorem exists_eq_qExpand_cosetConj (M : ℕ) [NeZero M] (data : ModularPolynomialData M)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ M) (e : ℕ) [NeZero e] (y : LaurentSeries K)
    (h : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (e * M))).toRingHom y = 0) :
    ∃ t ∈ primCosetReps M, y = qExpand K e (cosetConj ζ (jqModC K) t) := by
  obtain ⟨hprod, -, -, -⟩ := data.map_adjoin_jqNModC_eq_cosetTwoVarPoly K M ζ hζ
  rw [ModularPolynomialData.toJqNField_map] at hprod
  have hmap := congrArg (Polynomial.map (qExpand K e)) hprod
  rw [Polynomial.map_map] at hmap
  have hcomp : (qExpand K e).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K M (jqModC K))) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqNModC K (e * M)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.eval₂_X, qExpand_qExpand]
    rfl
  rw [hcomp] at hmap
  have hrhs : (cosetTwoVarPoly ζ M (jqModC K)).map (qExpand K e) =
      (primCosetReps M).prod fun t =>
        (Polynomial.X - Polynomial.C (qExpand K e (cosetConj ζ (jqModC K) t))) := by
    rw [cosetTwoVarPoly, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hrhs] at hmap
  have hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (jqNModC K (e * M)))).eval y = 0 := by
    rw [Polynomial.eval_map, ← aeval_toRingHom_eq]
    exact h
  rw [hmap, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hy
  obtain ⟨t, ht, ht0⟩ := hy
  refine ⟨t, ht, ?_⟩
  rwa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at ht0

def LowestAt (x : LaurentSeries K) (m : ℤ) : Prop :=
  x.coeff m ≠ 0 ∧ ∀ k < m, x.coeff k = 0

theorem LowestAt.unique {x : LaurentSeries K} {m m' : ℤ} (h : LowestAt x m) (h' : LowestAt x m') :
    m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd (h'.2 m hlt) h.1
  · exact heq
  · exact absurd (h.2 m' hgt) h'.1

theorem lowestAt_jqModC : LowestAt (jqModC K) (-1) := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [coeff_jqModC_neg_one]
    exact one_ne_zero
  · have h := coeff_jqModC_pow_of_lt K (b := 1) (m := k) (by simpa using hk)
    rwa [pow_one] at h

theorem lowestAt_qTwist (u : Kˣ) {x : LaurentSeries K} {m : ℤ} (h : LowestAt x m) :
    LowestAt (qTwist u x) m := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [qTwist_coeff]
    exact mul_ne_zero (Units.ne_zero _) h.1
  · rw [qTwist_coeff, h.2 k hk, mul_zero]

theorem lowestAt_qExpand (n : ℕ) [NeZero n] {x : LaurentSeries K} {m : ℤ} (h : LowestAt x m) :
    LowestAt (qExpand K n x) ((n : ℤ) * m) := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [qExpand_coeff_mul]
    exact h.1
  · by_cases hd : (n : ℤ) ∣ k
    · obtain ⟨i, rfl⟩ := hd
      rw [qExpand_coeff_mul]
      refine h.2 i ?_
      have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      exact lt_of_mul_lt_mul_left hk hn.le
    · exact qExpand_coeff_of_not_dvd n x hd

theorem lowestAt_qExpand_cosetSubst (ζ : Kˣ) (e a b : ℕ) [NeZero e] [NeZero a] :
    LowestAt (qExpand K e (cosetSubst ζ a b (jqModC K))) (-((e * (a * a) : ℕ) : ℤ)) := by
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  have h1 : LowestAt (cosetSubst ζ a b (jqModC K)) (((a * a : ℕ) : ℤ) * (-1 : ℤ)) := by
    unfold cosetSubst
    rw [RingHom.comp_apply]
    exact lowestAt_qExpand (a * a) (lowestAt_qTwist _ lowestAt_jqModC)
  have h2 := lowestAt_qExpand e h1
  have he : ((e : ℕ) : ℤ) * (((a * a : ℕ) : ℤ) * (-1 : ℤ)) = -((e * (a * a) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he] at h2
  exact h2

theorem map_eval₂_aeval (G : LaurentSeries K →+* LaurentSeries K) (P : Polynomial (Polynomial ℤ))
    (x w : LaurentSeries K) :
    G (P.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom w) =
      P.eval₂ (Polynomial.aeval (R := ℤ) (G x)).toRingHom (G w) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply]
  show G (Polynomial.aeval x (Polynomial.X : Polynomial ℤ)) =
    Polynomial.aeval (G x) (Polynomial.X : Polynomial ℤ)
  rw [Polynomial.aeval_X, Polynomial.aeval_X]

theorem core7 (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (ζN ζℓ : Kˣ) (hζN : IsPrimitiveRoot ζN N) (hζℓ : IsPrimitiveRoot ζℓ ℓ)
    (dataN : ModularPolynomialData N) (dataℓ : ModularPolynomialData ℓ) (y : LaurentSeries K)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K ℓ)).toRingHom y = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom (jqNModC K (N * ℓ * ℓ)) = 0) :
    y = jqNModC K (ℓ * ℓ) := by
  have hprime : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hprime.ne_zero⟩

  have h₁' : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (1 * ℓ))).toRingHom y = 0 := by
    rw [jqNModC_congr (show 1 * ℓ = ℓ from one_mul ℓ)]
    exact h₁
  obtain ⟨⟨a, b, d⟩, ht, hy1⟩ := exists_eq_qExpand_cosetConj ℓ dataℓ ζℓ hζℓ 1 y h₁'
  rw [mem_primCosetReps (NeZero.ne ℓ)] at ht
  obtain ⟨had, hbd, -⟩ := ht
  have ha : a = 1 ∨ a = ℓ := (Nat.dvd_prime hprime).1 ⟨d, had.symm⟩
  rcases ha with ha | ha
  ·
    exfalso
    subst ha
    set u : Kˣ := ζℓ ^ (1 * b) with hu
    have hTy : qTwist u⁻¹ y = jqModC K := by
      rw [hy1, qExpand_one_apply, cosetConj_eq]
      unfold cosetSubst
      rw [RingHom.comp_apply, qExpand_congr (show 1 * 1 = 1 from rfl), qExpand_one_apply, ← hu,
        qTwist_qTwist, inv_mul_cancel, qTwist_one_apply]

    have h₂' := congrArg (qTwist u⁻¹) h₂
    rw [map_zero, map_eval₂_aeval, hTy] at h₂'
    have h₂'' := congrArg (qExpand K N) h₂'
    rw [map_zero, map_eval₂_aeval] at h₂''
    set z : LaurentSeries K := qExpand K N (qTwist u⁻¹ (jqNModC K (N * ℓ * ℓ))) with hz
    have h₂''' : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (1 * N))).toRingHom z = 0 := by
      rw [jqNModC_congr (show 1 * N = N from one_mul N)]
      exact h₂''
    obtain ⟨⟨a', b', d'⟩, ht', hz'⟩ := exists_eq_qExpand_cosetConj N dataN ζN hζN 1 z h₂'''
    rw [mem_primCosetReps (NeZero.ne N)] at ht'
    obtain ⟨had', -, -⟩ := ht'
    have ha' : a' ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (by simpa using had'.symm)
    haveI : NeZero a' := ⟨ha'⟩

    have hL1 : LowestAt z ((N : ℤ) * (((N * ℓ * ℓ : ℕ) : ℤ) * (-1 : ℤ))) := by
      rw [hz]
      exact lowestAt_qExpand N (lowestAt_qTwist _ (lowestAt_qExpand (N * ℓ * ℓ) lowestAt_jqModC))
    have hL2 : LowestAt z (-((1 * (a' * a') : ℕ) : ℤ)) := by
      rw [hz', cosetConj_eq]
      exact lowestAt_qExpand_cosetSubst ζN 1 a' b'
    have heq : (N : ℤ) * (((N * ℓ * ℓ : ℕ) : ℤ) * (-1 : ℤ)) = -((1 * (a' * a') : ℕ) : ℤ) := hL1.unique hL2
    have hnat : (N * ℓ) * (N * ℓ) = a' * a' := by
      have : ((N * ℓ * (N * ℓ) : ℕ) : ℤ) = ((a' * a' : ℕ) : ℤ) := by
        push_cast at heq ⊢
        linarith
      exact_mod_cast this
    have ha'eq : a' = N * ℓ := (Nat.mul_self_inj.mp hnat).symm
    rw [ha'eq] at had'

    have h1 : ℓ * d' = 1 := by
      have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have : N * (ℓ * d') = N * 1 := by rw [← mul_assoc, had', mul_one]
      exact Nat.eq_of_mul_eq_mul_left hN0 this
    exact hprime.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h1)
  ·
    subst ha
    have hd : d = 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne a)) (had.trans (mul_one a).symm)
    subst hd
    have hb : b = 0 := Nat.lt_one_iff.mp hbd
    subst hb
    rw [hy1, qExpand_one_apply, cosetConj_eq]
    unfold cosetSubst
    rw [mul_zero, pow_zero, RingHom.comp_apply, qTwist_one_apply]
    rfl

end Generic

theorem main7 (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hN : (N : κ) ≠ 0) (hℓ : (ℓ : κ) ≠ 0)
    (dataN : ModularPolynomialData N) (dataℓ : ModularPolynomialData ℓ)
    (y : LaurentSeries κ)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC κ ℓ)).toRingHom y = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom (jqNModC κ (N * ℓ * ℓ)) = 0) :
    y = jqNModC κ (ℓ * ℓ) := by
  have hprime : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hprime.ne_zero⟩
  let L := AlgebraicClosure κ
  let f : κ →+* L := algebraMap κ L
  have hf : Function.Injective f := (algebraMap κ L).injective

  haveI : NeZero ((N : ℕ) : κ) := ⟨hN⟩
  haveI : NeZero ((ℓ : ℕ) : κ) := ⟨hℓ⟩
  obtain ⟨rN, hrN⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  obtain ⟨rℓ, hrℓ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  let ζN : Lˣ := (hrN.isUnit (NeZero.ne N)).unit
  let ζℓ : Lˣ := (hrℓ.isUnit hprime.ne_zero).unit
  have hζN : IsPrimitiveRoot ζN N :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [IsUnit.unit_spec]; exact hrN)
  have hζℓ : IsPrimitiveRoot ζℓ ℓ :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [IsUnit.unit_spec]; exact hrℓ)

  let F : LaurentSeries κ →+* LaurentSeries L := coeffMap f
  have hF : Function.Injective F := by
    intro x x' hxx'
    ext k
    apply hf
    rw [← coeffMap_coeff, ← coeffMap_coeff]
    exact congrArg (fun s => HahnSeries.coeff s k) hxx'
  have hFj0 : F (jqModC κ) = jqModC L := by
    ext k
    show (coeffMap f (jqModC κ)).coeff k = (jqModC L).coeff k
    rw [coeffMap_coeff, ← map_jqModC (K := κ) f, HahnSeries.map_coeff]
  have hFj : ∀ (m : ℕ) [NeZero m], F (jqNModC κ m) = jqNModC L m := by
    intro m _
    show coeffMap f (qExpand κ m (jqModC κ)) = qExpand L m (jqModC L)
    rw [coeffMap_qExpand, ← hFj0]
  have hT : ∀ (P : Polynomial (Polynomial ℤ)) (x w : LaurentSeries κ),
      F (P.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom w) =
        P.eval₂ (Polynomial.aeval (R := ℤ) (F x)).toRingHom (F w) := by
    intro P x w
    rw [Polynomial.hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply]
    show F (Polynomial.aeval x (Polynomial.X : Polynomial ℤ)) =
      Polynomial.aeval (F x) (Polynomial.X : Polynomial ℤ)
    rw [Polynomial.aeval_X, Polynomial.aeval_X]
  have h₁' := congrArg F h₁
  rw [map_zero, hT, hFj] at h₁'
  have h₂' := congrArg F h₂
  rw [map_zero, hT, hFj] at h₂'
  have hcore := core7 N ℓ ζN ζℓ hζN hζℓ dataN dataℓ (F y) h₁' h₂'
  apply hF
  rw [hcore, hFj]

end CommonRoot

end ModularCurve

end

theorem solution
    (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hN : (N : κ) ≠ 0) (hℓ : (ℓ : κ) ≠ 0)
    (dataN : ModularCurve.ModularPolynomialData N) (dataℓ : ModularCurve.ModularPolynomialData ℓ)
    (y : LaurentSeries κ)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC κ ℓ)).toRingHom y = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom (ModularCurve.jqNModC κ (N * ℓ * ℓ)) = 0) :
    y = ModularCurve.jqNModC κ (ℓ * ℓ) :=
  ModularCurve.CommonRoot.main7 κ N ℓ hN hℓ dataN dataℓ y h₁ h₂

#print axioms solution

end S_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
end P2MW
export P2MW.S_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero (solution)
