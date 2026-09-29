-- Prove2me | solution 1 for LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ab2e8a45-3fe6-5810-a9d7-a7083ce543fc

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell

set_option autoImplicit false

namespace R2NormInj

open Matrix LT.TwistedNorm LT.TwistedNorm.GL2

section H90
open Finset

theorem exists_ne_zero_mul_map_eq {R : Type*} [CommRing R] [IsDomain R]
    (τ : R →+* R) (m : ℕ) (hm : 0 < m) (hτm : ∀ x, τ^[m] x = x)
    (hdist : ∀ i j : ℕ, i < m → j < m → (∀ x, τ^[i] x = τ^[j] x) → i = j)
    (v : R) (hv : ∏ i ∈ range m, τ^[i] v = 1) :
    ∃ x : R, x ≠ 0 ∧ v * τ x = x := by
  classical

  set P : ℕ → R := fun i => ∏ j ∈ range i, τ^[j] v with hP
  have hP0 : P 0 = 1 := by simp [hP]
  have hPsucc : ∀ i, P (i + 1) = v * τ (P i) := by
    intro i
    simp only [hP]
    rw [prod_range_succ', map_prod]
    simp only [Function.iterate_zero, id_eq]
    rw [mul_comm]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [Function.iterate_succ_apply']
  have hPm : P m = 1 := hv

  let f : Fin m → (R →* R) := fun i => ((τ ^ (i : ℕ) : R →+* R) : R →* R)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hdist i j i.2 j.2
    intro x
    have := congrArg (fun g : R →* R => g x) hij
    simpa [f, RingHom.coe_pow] using this
  have hli := (linearIndependent_monoidHom R R).comp f hf

  have hne : (∑ i : Fin m, P i • ((f i : R →* R) : R → R)) ≠ 0 := by
    intro h0
    have h := linearIndependent_iff'.mp hli Finset.univ (fun i => P i) h0 ⟨0, hm⟩ (mem_univ _)
    simp [hP0] at h
  obtain ⟨c, hc⟩ : ∃ c, (∑ i : Fin m, P i • ((f i : R →* R) : R → R)) c ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun c => by simpa using h c)
  refine ⟨∑ i ∈ range m, P i * τ^[i] c, ?_, ?_⟩
  ·
    have : (∑ i : Fin m, P i • ((f i : R →* R) : R → R)) c = ∑ i ∈ range m, P i * τ^[i] c := by
      rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range (fun i => P i * τ^[i] c)]
      refine sum_congr rfl fun i _ => ?_
      simp [f, RingHom.coe_pow]
    rw [← this]; exact hc
  ·
    rw [map_sum, mul_sum]
    have hstep : ∀ i, v * τ (P i * τ^[i] c) = P (i + 1) * τ^[i + 1] c := by
      intro i
      rw [map_mul, ← mul_assoc, ← hPsucc, Function.iterate_succ_apply']
    simp_rw [hstep]
    have h1 := sum_range_succ' (fun k => P k * τ^[k] c) m
    have h2 := sum_range_succ (fun k => P k * τ^[k] c) m
    rw [hPm, hτm, one_mul] at h2
    rw [hP0, one_mul, Function.iterate_zero, id_eq, h2] at h1

    exact (add_right_cancel h1).symm

end H90

section Companion

variable {L : Type*} [Field L] (t d : L)

theorem eq_lin_of_comm (X : Matrix (Fin 2) (Fin 2) L)
    (h : traceDetCompanion t d * X = X * traceDetCompanion t d) :
    X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) L) + X 1 0 • traceDetCompanion t d := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion] at h00 h10

  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceDetCompanion]
  · linear_combination -h00
  · linear_combination -h10

theorem lin_comm (p r : L) :
    traceDetCompanion t d * (p • (1 : Matrix (Fin 2) (Fin 2) L) + r • traceDetCompanion t d)
      = (p • (1 : Matrix (Fin 2) (Fin 2) L) + r • traceDetCompanion t d) * traceDetCompanion t d := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem companion_sq :
    traceDetCompanion t d * traceDetCompanion t d
      = t • traceDetCompanion t d - d • (1 : Matrix (Fin 2) (Fin 2) L) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion] <;> ring

theorem det_lin (p r : L) :
    (p • (1 : Matrix (Fin 2) (Fin 2) L) + r • traceDetCompanion t d).det = p ^ 2 + p * r * t + r ^ 2 * d := by
  simp [Matrix.det_fin_two, traceDetCompanion]; ring

def Z : Subalgebra L (Matrix (Fin 2) (Fin 2) L) :=
  Subalgebra.centralizer L {traceDetCompanion t d}

theorem mem_Z_iff {X : Matrix (Fin 2) (Fin 2) L} :
    X ∈ Z t d ↔ traceDetCompanion t d * X = X * traceDetCompanion t d := by
  simp [Z, Subalgebra.mem_centralizer_iff]

theorem eq_lin_of_mem_Z {X : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) :
    X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) L) + X 1 0 • traceDetCompanion t d :=
  eq_lin_of_comm t d X ((mem_Z_iff t d).mp hX)

theorem lin_mem_Z (p r : L) :
    p • (1 : Matrix (Fin 2) (Fin 2) L) + r • traceDetCompanion t d ∈ Z t d :=
  (mem_Z_iff t d).mpr (lin_comm t d p r)

theorem companion_mem_Z : traceDetCompanion t d ∈ Z t d :=
  (mem_Z_iff t d).mpr rfl

theorem mul_comm_of_mem_Z {X Y : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) (hY : Y ∈ Z t d) :
    X * Y = Y * X := by
  rw [eq_lin_of_mem_Z t d hX, eq_lin_of_mem_Z t d hY]
  set C := traceDetCompanion t d
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  module

scoped instance instCommRingZ : CommRing (Z t d) :=
  { (inferInstance : Ring (Z t d)) with
    mul_comm := fun x y => Subtype.ext (mul_comm_of_mem_Z t d x.2 y.2) }

theorem det_ne_zero_of_mem_Z_of_ne_zero (hirr : ∀ a : L, a ^ 2 - t * a + d ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) (h0 : X ≠ 0) : X.det ≠ 0 := by
  rw [eq_lin_of_mem_Z t d hX] at h0 ⊢
  rw [det_lin]
  set p := X 0 0
  set r := X 1 0
  by_cases hr : r = 0
  · have hp : p ≠ 0 := by
      rintro hp
      apply h0
      rw [hp, hr, zero_smul, zero_smul, add_zero]
    rw [hr]; simpa using pow_ne_zero 2 hp
  · intro h
    apply hirr (-p / r)
    field_simp
    linear_combination h

theorem isDomain_Z (hirr : ∀ a : L, a ^ 2 - t * a + d ≠ 0) : IsDomain (Z t d) := by
  have hnzd : NoZeroDivisors (Z t d) := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hdet : (x : Matrix (Fin 2) (Fin 2) L).det ≠ 0 :=
        det_ne_zero_of_mem_Z_of_ne_zero t d hirr x.2 (fun h => hx (Subtype.ext h))
      have hxy' : (x : Matrix (Fin 2) (Fin 2) L) * (y : Matrix (Fin 2) (Fin 2) L) = 0 :=
        congrArg Subtype.val hxy
      apply Subtype.ext
      have hu : IsUnit (x : Matrix (Fin 2) (Fin 2) L).det := isUnit_iff_ne_zero.mpr hdet
      calc (y : Matrix (Fin 2) (Fin 2) L)
          = (x : Matrix (Fin 2) (Fin 2) L)⁻¹ * ((x : Matrix (Fin 2) (Fin 2) L) * y) := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
        _ = 0 := by rw [hxy', Matrix.mul_zero]
  have hnt : Nontrivial (Z t d) := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  exact NoZeroDivisors.to_isDomain _

theorem isUnit_of_ne_zero_Z (hirr : ∀ a : L, a ^ 2 - t * a + d ≠ 0) {x : Z t d} (hx : x ≠ 0) :
    IsUnit x := by
  have hdet : (x : Matrix (Fin 2) (Fin 2) L).det ≠ 0 :=
    det_ne_zero_of_mem_Z_of_ne_zero t d hirr x.2 (fun h => hx (Subtype.ext h))
  have hu : IsUnit (x : Matrix (Fin 2) (Fin 2) L).det := isUnit_iff_ne_zero.mpr hdet

  have hinv : (x : Matrix (Fin 2) (Fin 2) L)⁻¹ ∈ Z t d := by
    rw [mem_Z_iff]
    have hx' := (mem_Z_iff t d).mp x.2
    set C := traceDetCompanion t d
    set M := (x : Matrix (Fin 2) (Fin 2) L)
    calc C * M⁻¹ = 1 * C * M⁻¹ := by rw [Matrix.one_mul]
      _ = M⁻¹ * M * C * M⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu]
      _ = M⁻¹ * (M * C) * M⁻¹ := by rw [Matrix.mul_assoc M⁻¹]
      _ = M⁻¹ * (C * M) * M⁻¹ := by rw [← hx']
      _ = M⁻¹ * C * (M * M⁻¹) := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * C := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  refine ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (Matrix.mul_nonsing_inv _ hu), Subtype.ext (Matrix.nonsing_inv_mul _ hu)⟩,
    rfl⟩

theorem inv_mem_Z {X : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) (hu : IsUnit X.det) : X⁻¹ ∈ Z t d := by
  rw [mem_Z_iff] at hX ⊢
  set C := traceDetCompanion t d
  calc C * X⁻¹ = 1 * C * X⁻¹ := by rw [Matrix.one_mul]
    _ = X⁻¹ * X * C * X⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu]
    _ = X⁻¹ * (X * C) * X⁻¹ := by rw [Matrix.mul_assoc X⁻¹]
    _ = X⁻¹ * (C * X) * X⁻¹ := by rw [← hX]
    _ = X⁻¹ * C * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
    _ = X⁻¹ * C := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
end Companion

section Sigma

variable {L : Type*} [Field L] (t d : L) (σ : L →+* L) (ht : σ t = t) (hd : σ d = d)

include ht hd in
theorem companion_map : (traceDetCompanion t d).map σ = traceDetCompanion t d := by
  rw [traceDetCompanion_map, ht, hd]

include ht hd in
theorem map_mem_Z {X : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) : X.map σ ∈ Z t d := by
  rw [mem_Z_iff] at hX ⊢
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M.map σ) hX
  simp only [Matrix.map_mul, companion_map t d σ ht hd] at h
  exact h

noncomputable def ZMap : Z t d →+* Z t d :=
  (σ.mapMatrix : Matrix (Fin 2) (Fin 2) L →+* Matrix (Fin 2) (Fin 2) L).restrict (Z t d) (Z t d)
    (fun X hX => by rw [RingHom.mapMatrix_apply]; exact map_mem_Z t d σ ht hd hX)

@[scoped simp] theorem coe_ZMap (x : Z t d) :
    ((ZMap t d σ ht hd x : Z t d) : Matrix (Fin 2) (Fin 2) L) = (x : Matrix (Fin 2) (Fin 2) L).map σ :=
  rfl

theorem coe_ZMap_iterate (i : ℕ) (x : Z t d) :
    (((ZMap t d σ ht hd)^[i] x : Z t d) : Matrix (Fin 2) (Fin 2) L)
      = (x : Matrix (Fin 2) (Fin 2) L).map (σ^[i]) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', coe_ZMap, ih, Matrix.map_map, ← Function.iterate_succ']

theorem smul_one_mem_Z (p : L) : p • (1 : Matrix (Fin 2) (Fin 2) L) ∈ Z t d := by
  rw [mem_Z_iff, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem ZMap_iterate_smul_one (i : ℕ) (p : L) :
    (((ZMap t d σ ht hd)^[i] ⟨p • 1, smul_one_mem_Z t d p⟩ : Z t d) : Matrix (Fin 2) (Fin 2) L)
      = (σ^[i] p) • (1 : Matrix (Fin 2) (Fin 2) L) := by
  rw [coe_ZMap_iterate]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [iterate_map_zero σ i]

noncomputable def j : (Z t d)ˣ →* GL (Fin 2) L :=
  Units.map ((Z t d).val.toRingHom : Z t d →* Matrix (Fin 2) (Fin 2) L)

@[scoped simp] theorem coe_j (z : (Z t d)ˣ) :
    ((j t d z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = ((z : Z t d) : Matrix (Fin 2) (Fin 2) L) := rfl

theorem j_injective : Function.Injective (j t d) := by
  intro z z' h
  apply Units.ext; apply Subtype.ext
  exact congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h

theorem coe_j_mem (z : (Z t d)ˣ) : ((j t d z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ∈ Z t d :=
  (z : Z t d).2

noncomputable def liftUnit (δ : GL (Fin 2) L) (h : (δ : Matrix (Fin 2) (Fin 2) L) ∈ Z t d) : (Z t d)ˣ where
  val := ⟨δ, h⟩
  inv := ⟨((δ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L), by
    rw [Matrix.coe_units_inv]; exact inv_mem_Z t d h (Matrix.isUnits_det_units δ)⟩
  val_inv := Subtype.ext (by
    show (δ : Matrix (Fin 2) (Fin 2) L) * ((δ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  inv_val := Subtype.ext (by
    show ((δ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (δ : Matrix (Fin 2) (Fin 2) L) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

@[scoped simp] theorem j_liftUnit (δ : GL (Fin 2) L) (h : (δ : Matrix (Fin 2) (Fin 2) L) ∈ Z t d) :
    j t d (liftUnit t d δ h) = δ :=
  Units.ext rfl

noncomputable def SZ : (Z t d)ˣ →* (Z t d)ˣ := Units.map (ZMap t d σ ht hd).toMonoidHom

theorem j_SZ (z : (Z t d)ˣ) :
    j t d (SZ t d σ ht hd z) = Matrix.GeneralLinearGroup.map σ (j t d z) := by
  apply Units.ext; ext a b; rfl

theorem coe_SZ_iterate (i : ℕ) (z : (Z t d)ˣ) :
    (((SZ t d σ ht hd)^[i] z : (Z t d)ˣ) : Z t d) = (ZMap t d σ ht hd)^[i] (z : Z t d) := by
  induction i generalizing z with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem j_sigmaPartialNorm (z : (Z t d)ˣ) (r : ℕ) :
    j t d (sigmaPartialNorm (SZ t d σ ht hd) z r)
      = sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) (j t d z) r :=
  hom_sigmaPartialNorm _ _ (j t d) (fun x => j_SZ t d σ ht hd x) z r

theorem sigmaPartialNorm_mul_Z (x y : (Z t d)ˣ) (r : ℕ) :
    sigmaPartialNorm (SZ t d σ ht hd) (x * y) r
      = sigmaPartialNorm (SZ t d σ ht hd) x r * sigmaPartialNorm (SZ t d σ ht hd) y r := by
  rw [sigmaPartialNorm_eq_prod_range, sigmaPartialNorm_eq_prod_range, sigmaPartialNorm_eq_prod_range,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact iterate_map_mul _ i x y

theorem sigmaPartialNorm_inv_Z (x : (Z t d)ˣ) (r : ℕ) :
    sigmaPartialNorm (SZ t d σ ht hd) x⁻¹ r = (sigmaPartialNorm (SZ t d σ ht hd) x r)⁻¹ := by
  rw [sigmaPartialNorm_eq_prod_range, sigmaPartialNorm_eq_prod_range, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact iterate_map_inv _ i x

end Sigma

section Coordinates

variable {L : Type*} [Field L] (t d : L)

theorem entries_of_mem_Z {X : Matrix (Fin 2) (Fin 2) L} (hX : X ∈ Z t d) :
    X 0 1 = -(d * X 1 0) ∧ X 1 1 = X 0 0 + t * X 1 0 := by
  have h := (mem_Z_iff t d).mp hX
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion] at h00 h10
  exact ⟨h00.symm, h10.symm⟩

def piRoot (ρ : L) (hρ : ρ ^ 2 - t * ρ + d = 0) : Z t d →+* L where
  toFun X := (X : Matrix (Fin 2) (Fin 2) L) 0 0 + (X : Matrix (Fin 2) (Fin 2) L) 1 0 * ρ
  map_one' := by simp
  map_zero' := by simp
  map_add' X Y := by
    simp only [Subalgebra.coe_add, Matrix.add_apply]; ring
  map_mul' X Y := by
    obtain ⟨hX01, hX11⟩ := entries_of_mem_Z t d X.2
    obtain ⟨hY01, hY11⟩ := entries_of_mem_Z t d Y.2
    simp only [Subalgebra.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hX01, hX11]
    linear_combination (-((X : Matrix (Fin 2) (Fin 2) L) 1 0 * (Y : Matrix (Fin 2) (Fin 2) L) 1 0)) * hρ

theorem piRoot_apply (ρ : L) (hρ : ρ ^ 2 - t * ρ + d = 0) (X : Z t d) :
    piRoot t d ρ hρ X = (X : Matrix (Fin 2) (Fin 2) L) 0 0 + (X : Matrix (Fin 2) (Fin 2) L) 1 0 * ρ := rfl

theorem ext_of_piRoot_eq {ρ ρ' : L} (hρ : ρ ^ 2 - t * ρ + d = 0) (hρ' : ρ' ^ 2 - t * ρ' + d = 0)
    (hne : ρ ≠ ρ') {X Y : Z t d}
    (h1 : piRoot t d ρ hρ X = piRoot t d ρ hρ Y) (h2 : piRoot t d ρ' hρ' X = piRoot t d ρ' hρ' Y) :
    X = Y := by
  simp only [piRoot_apply] at h1 h2
  have h10 : (X : Matrix (Fin 2) (Fin 2) L) 1 0 = (Y : Matrix (Fin 2) (Fin 2) L) 1 0 := by
    have : ((X : Matrix (Fin 2) (Fin 2) L) 1 0 - (Y : Matrix (Fin 2) (Fin 2) L) 1 0) * (ρ - ρ') = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hne
  have h00 : (X : Matrix (Fin 2) (Fin 2) L) 0 0 = (Y : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    rw [h10] at h1; linear_combination h1
  apply Subtype.ext
  rw [eq_lin_of_mem_Z t d X.2, eq_lin_of_mem_Z t d Y.2, h00, h10]

theorem exists_piRoot_eq {ρ ρ' : L} (hρ : ρ ^ 2 - t * ρ + d = 0) (hρ' : ρ' ^ 2 - t * ρ' + d = 0)
    (hne : ρ ≠ ρ') (x y : L) :
    ∃ W : Z t d, piRoot t d ρ hρ W = x ∧ piRoot t d ρ' hρ' W = y := by
  have hsub : ρ - ρ' ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨⟨(x - (x - y) / (ρ - ρ') * ρ) • (1 : Matrix (Fin 2) (Fin 2) L)
      + ((x - y) / (ρ - ρ')) • traceDetCompanion t d, lin_mem_Z t d _ _⟩, ?_, ?_⟩
  · simp [piRoot_apply, traceDetCompanion]
  · simp [piRoot_apply, traceDetCompanion]
    field_simp
    ring

variable (σ : L →+* L) (ht : σ t = t) (hd : σ d = d)

theorem piRoot_ZMap {ρ ρ' : L} (hρ : ρ ^ 2 - t * ρ + d = 0) (hρ' : ρ' ^ 2 - t * ρ' + d = 0)
    (hσ : σ ρ' = ρ) (X : Z t d) :
    piRoot t d ρ hρ (ZMap t d σ ht hd X) = σ (piRoot t d ρ' hρ' X) := by
  simp [piRoot_apply, hσ]

end Coordinates

section Core

theorem prod_range_two_mul_iterate {M F : Type*} [CommMonoid M] [FunLike F M M] [MulHomClass F M M]
    (f : F) (x : M) (m : ℕ) :
    ∏ i ∈ Finset.range (2 * m), (⇑f)^[i] x = ∏ k ∈ Finset.range m, ((⇑f)^[2])^[k] (x * f x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ,
        mul_assoc]
      congr 1
      rw [← Function.iterate_mul, iterate_map_mul, ← Function.iterate_succ_apply (⇑f) (2 * m) x]

variable {L : Type*} [Field L] (t d : L) (σ : L →+* L) (ht : σ t = t) (hd : σ d = d)

theorem exists_unit_mul_SZ_eq (n : ℕ) (hn : 0 < n) (hσn : ∀ x : L, σ^[n] x = x)
    (hdist : ∀ i j : ℕ, i < n → j < n → (∀ x : L, σ^[i] x = σ^[j] x) → i = j)
    (hfix : ∀ a : L, a ^ 2 - t * a + d = 0 → σ a ≠ a)
    (u : (Z t d)ˣ) (hu : sigmaPartialNorm (SZ t d σ ht hd) u n = 1) :
    ∃ w : (Z t d)ˣ, u * SZ t d σ ht hd w = w := by
  classical

  have hprod : ∏ i ∈ Finset.range n, (ZMap t d σ ht hd)^[i] (u : Z t d) = 1 := by
    have h := congrArg (fun z : (Z t d)ˣ => (z : Z t d)) hu
    simp only [sigmaPartialNorm_eq_prod_range, Units.coe_prod, coe_SZ_iterate, Units.val_one] at h
    exact h
  have hZn : ∀ X : Z t d, (ZMap t d σ ht hd)^[n] X = X := fun X => by
    apply Subtype.ext; rw [coe_ZMap_iterate]; ext a b; exact hσn _
  by_cases hroot : ∃ lam : L, lam ^ 2 - t * lam + d = 0
  ·
    obtain ⟨lam, hlam⟩ := hroot
    set mu := t - lam with hmu_def
    have hmu : mu ^ 2 - t * mu + d = 0 := by rw [hmu_def]; linear_combination hlam
    have hroots : ∀ a : L, a ^ 2 - t * a + d = 0 → a = lam ∨ a = mu := by
      intro a ha
      have : (a - lam) * (a - mu) = 0 := by rw [hmu_def]; linear_combination ha - hlam
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    have hσlam : σ lam = mu := by
      have hr : (σ lam) ^ 2 - t * σ lam + d = 0 := by
        have := congrArg σ hlam
        rw [map_add, map_sub, map_pow, map_mul, ht, hd, map_zero] at this
        exact this
      rcases hroots _ hr with h | h
      · exact absurd h (hfix lam hlam)
      · exact h
    have hσmu : σ mu = lam := by
      rw [hmu_def, map_sub, ht, hσlam, hmu_def]; ring
    have hne : lam ≠ mu := by
      intro h; apply hfix lam hlam; rw [hσlam, ← h]

    have hiter : ∀ k : ℕ, σ^[2 * k] lam = lam ∧ σ^[2 * k + 1] lam = mu := by
      intro k
      induction k with
      | zero => simp [hσlam]
      | succ k ih =>
          have h1 : σ^[2 * (k + 1)] lam = lam := by
            rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, Function.iterate_succ_apply', ih.2, hσmu]
          refine ⟨h1, ?_⟩
          rw [Function.iterate_succ_apply', h1, hσlam]

    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m, by omega⟩
      · exfalso
        have := hσn lam
        rw [hm, (hiter m).2] at this
        exact hne this.symm
    have hm0 : 0 < m := by omega

    have hint₁ : ∀ X, piRoot t d lam hlam (ZMap t d σ ht hd X) = σ (piRoot t d mu hmu X) :=
      fun X => piRoot_ZMap t d σ ht hd hlam hmu hσmu X
    have hint₂ : ∀ X, piRoot t d mu hmu (ZMap t d σ ht hd X) = σ (piRoot t d lam hlam X) :=
      fun X => piRoot_ZMap t d σ ht hd hmu hlam hσlam X

    set τ : L →+* L := σ.comp σ with hτ_def
    have hτ_iter : ∀ (k : ℕ) (x : L), τ^[k] x = σ^[2 * k] x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
          intro x
          rw [Function.iterate_succ_apply, ih, show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          rfl
    have hZ2 : ∀ Y : Z t d, piRoot t d lam hlam ((ZMap t d σ ht hd)^[2] Y) = τ (piRoot t d lam hlam Y) := by
      intro Y
      show piRoot t d lam hlam (ZMap t d σ ht hd (ZMap t d σ ht hd Y)) = σ (σ (piRoot t d lam hlam Y))
      rw [hint₁, hint₂]
    have hπ_iter2 : ∀ (k : ℕ) (X : Z t d),
        piRoot t d lam hlam (((ZMap t d σ ht hd)^[2])^[k] X) = τ^[k] (piRoot t d lam hlam X) := by
      intro k
      induction k with
      | zero => intro X; rfl
      | succ k ih => intro X; rw [Function.iterate_succ_apply', hZ2, ih, Function.iterate_succ_apply']

    set a := piRoot t d lam hlam (u : Z t d) with ha_def
    set b := piRoot t d mu hmu (u : Z t d) with hb_def
    have hv1 : ∏ k ∈ Finset.range m, τ^[k] (a * σ b) = 1 := by
      have hprod' : ∏ i ∈ Finset.range (2 * m), (ZMap t d σ ht hd)^[i] (u : Z t d) = 1 := hm ▸ hprod
      rw [prod_range_two_mul_iterate] at hprod'
      have h := congrArg (piRoot t d lam hlam) hprod'
      rw [map_prod, map_one] at h
      rw [← h]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hπ_iter2, map_mul, hint₁]
    have hτm : ∀ x, τ^[m] x = x := fun x => by rw [hτ_iter, ← hm]; exact hσn x
    have hτdist : ∀ i j : ℕ, i < m → j < m → (∀ x, τ^[i] x = τ^[j] x) → i = j := by
      intro i j hi hj hij
      have := hdist (2 * i) (2 * j) (by omega) (by omega)
        (fun x => by rw [← hτ_iter, ← hτ_iter, hij])
      omega
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mul_map_eq τ m hm0 hτm hτdist (a * σ b) hv1

    have hb0 : b ≠ 0 := ((Units.isUnit u).map (piRoot t d mu hmu)).ne_zero
    have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx0
    have hy0 : b * σ x ≠ 0 := mul_ne_zero hb0 hσx0
    obtain ⟨W, hW1, hW2⟩ := exists_piRoot_eq t d hlam hmu hne x (b * σ x)
    obtain ⟨W', hW1', hW2'⟩ := exists_piRoot_eq t d hlam hmu hne x⁻¹ (b * σ x)⁻¹
    have hWW' : W * W' = 1 :=
      ext_of_piRoot_eq t d hlam hmu hne
        (by rw [map_mul, map_one, hW1, hW1', mul_inv_cancel₀ hx0])
        (by rw [map_mul, map_one, hW2, hW2', mul_inv_cancel₀ hy0])
    have hW'W : W' * W = 1 := by rw [mul_comm]; exact hWW'
    refine ⟨⟨W, W', hWW', hW'W⟩, Units.ext ?_⟩
    show (u : Z t d) * ZMap t d σ ht hd W = W
    apply ext_of_piRoot_eq t d hlam hmu hne
    · rw [map_mul, hint₁, hW2, hW1, ← ha_def, map_mul, ← mul_assoc]
      exact hx
    · rw [map_mul, hint₂, hW1, hW2]
  ·
    push Not at hroot
    haveI := isDomain_Z t d hroot
    have hdist' : ∀ i j : ℕ, i < n → j < n →
        (∀ X : Z t d, (ZMap t d σ ht hd)^[i] X = (ZMap t d σ ht hd)^[j] X) → i = j := by
      intro i j hi hj hij
      apply hdist i j hi hj
      intro p
      have h := congrArg (fun X : Z t d => (X : Matrix (Fin 2) (Fin 2) L) 0 0)
        (hij ⟨p • 1, smul_one_mem_Z t d p⟩)
      simp only [ZMap_iterate_smul_one] at h
      simpa using h
    obtain ⟨x, hx0, hx⟩ :=
      exists_ne_zero_mul_map_eq (ZMap t d σ ht hd) n hn hZn hdist' (u : Z t d) hprod
    obtain ⟨w, hw⟩ := isUnit_of_ne_zero_Z t d hroot hx0
    refine ⟨w, Units.ext ?_⟩
    show (u : Z t d) * ZMap t d σ ht hd (w : Z t d) = w
    rw [hw, hx]

end Core

section Assembly

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

theorem isNormRep_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
  rw [← hQ, map_mul, map_mul, map_inv, ← hP]
  group

omit [FiniteDimensional F L] [IsGalois F L] in

theorem isNormRep_conj {σ : L ≃ₐ[F] L} {δ : GL (Fin 2) L} {γ : GL (Fin 2) F} (h : IsNormRep σ γ δ)
    (Q : GL (Fin 2) F) : IsNormRep σ (Q⁻¹ * γ * Q) δ := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hP]
  group

theorem exists_mk_eq_and_sigmaNormPow_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : IsNormRep σ γ δ) :
    ∃ δ' : GL (Fin 2) L, SigmaConjClasses.mk σ δ' = SigmaConjClasses.mk σ δ ∧
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ'
        = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) P, ?_, ?_⟩
  · symm
    exact SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨P, rfl⟩
  · rw [sigmaNormPow_sigmaConj_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
      (fun a => iterate_finrank_apply_of_generator hgen a) P δ, hP]

theorem sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) F) (hγ : γ ∈ AutomorphicForm.ellipticCell F)
    (δ₁ δ₂ : GL (Fin 2) L)
    (h₁ : normClassMap hgen (SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : normClassMap hgen (SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    SigmaConjClasses.mk σ δ₁ = SigmaConjClasses.mk σ δ₂ := by
  classical

  set t₀ : F := (γ : Matrix (Fin 2) (Fin 2) F).trace with ht₀
  set d₀ : F := (γ : Matrix (Fin 2) (Fin 2) F).det with hd₀
  have hell : ∀ a : F, a ^ 2 - t₀ * a + d₀ ≠ 0 := by
    intro a ha
    apply hγ a
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination ha
  have hnonscalar : ∀ c : F, (γ : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro c hc
    apply hell c
    have htr : t₀ = c + c := by rw [ht₀, hc]; simp; ring
    have hdet : d₀ = c * c := by rw [hd₀, hc]; simp; ring
    rw [htr, hdet]; ring

  have hdC : (traceDetCompanion t₀ d₀).det ≠ 0 := by
    rw [det_traceDetCompanion, hd₀]
    exact (Matrix.isUnits_det_units γ).ne_zero
  set Cγ : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdC with hCγ
  obtain ⟨Q, hQ⟩ := exists_conj_eq_traceDetCompanion_units γ hnonscalar
  have hQ' : Q⁻¹ * γ * Q = Cγ := Units.ext hQ

  set n := Module.finrank F L with hn_def
  set σr : L →+* L := (σ : L →+* L) with hσr
  set t : L := algebraMap F L t₀ with ht_def
  set d : L := algebraMap F L d₀ with hd_def
  have ht : σr t = t := σ.commutes t₀
  have hd : σr d = d := σ.commutes d₀
  have hσn : ∀ x : L, σr^[n] x = x := fun x => iterate_finrank_apply_of_generator hgen x
  have horder : orderOf σ = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hn0 : 0 < n := Module.finrank_pos
  have hdist : ∀ i j : ℕ, i < n → j < n → (∀ x : L, σr^[i] x = σr^[j] x) → i = j := by
    intro i j hi hj hij
    have hpow : σ ^ i = σ ^ j := by
      apply AlgEquiv.ext
      intro x
      rw [AlgEquiv.coe_pow, AlgEquiv.coe_pow]
      exact hij x
    exact pow_injOn_Iio_orderOf (by rw [horder]; exact hi) (by rw [horder]; exact hj) hpow
  have hfix : ∀ a : L, a ^ 2 - t * a + d = 0 → σr a ≠ a := by
    intro a ha hσa
    obtain ⟨b, rfl⟩ := mem_range_algebraMap_of_generator_apply_eq hgen (a := a) hσa
    apply hell b
    apply (algebraMap F L).injective
    rw [map_zero, ← ha, ht_def, hd_def]
    simp only [map_add, map_sub, map_mul, map_pow]

  set g : GL (Fin 2) L := Matrix.GeneralLinearGroup.map (algebraMap F L) Cγ with hg_def
  have hg_coe : (g : Matrix (Fin 2) (Fin 2) L) = traceDetCompanion t d := by
    rw [hg_def, ht_def, hd_def, ← traceDetCompanion_map]
    ext i j; rfl
  have hSg : Matrix.GeneralLinearGroup.map σr g = g := by
    apply Units.ext; ext i j
    change σ (algebraMap F L ((Cγ : Matrix (Fin 2) (Fin 2) F) i j)) = algebraMap F L ((Cγ : Matrix (Fin 2) (Fin 2) F) i j)
    exact σ.commutes _

  obtain ⟨δ₁', hcls₁, hN₁⟩ := exists_mk_eq_and_sigmaNormPow_eq hgen
    (isNormRep_conj (isNormRep_of_normClassMap_mk_eq hgen h₁) Q)
  obtain ⟨δ₂', hcls₂, hN₂⟩ := exists_mk_eq_and_sigmaNormPow_eq hgen
    (isNormRep_conj (isNormRep_of_normClassMap_mk_eq hgen h₂) Q)
  rw [hQ'] at hN₁ hN₂
  rw [← hcls₁, ← hcls₂]

  have hmem : ∀ δ : GL (Fin 2) L,
      sigmaNormPow (Matrix.GeneralLinearGroup.map σr) n δ = g → (δ : Matrix (Fin 2) (Fin 2) L) ∈ Z t d := by
    intro δ hδ
    have hstab := map_sigmaNormPow_generalLinearGroup (n := Fin 2) (σ := σr) (ℓ := n) hσn δ
    rw [hδ, hSg] at hstab

    have hcomm : δ * g = g * δ := by
      calc δ * g = δ * (δ⁻¹ * g * δ) := by rw [← hstab]
        _ = g * δ := by group
    rw [mem_Z_iff, ← hg_coe]
    have := congrArg (fun x : GL (Fin 2) L => (x : Matrix (Fin 2) (Fin 2) L)) hcomm
    simpa only [Units.val_mul] using this.symm
  set z₁ := liftUnit t d δ₁' (hmem δ₁' hN₁) with hz₁
  set z₂ := liftUnit t d δ₂' (hmem δ₂' hN₂) with hz₂
  have hgZ : (g : Matrix (Fin 2) (Fin 2) L) ∈ Z t d := by rw [hg_coe]; exact companion_mem_Z t d
  set c := liftUnit t d g hgZ with hc

  have hNz : ∀ (z : (Z t d)ˣ), sigmaNormPow (Matrix.GeneralLinearGroup.map σr) n (j t d z) = g →
      sigmaPartialNorm (SZ t d σr ht hd) z n = c := by
    intro z hz
    apply j_injective t d
    rw [j_sigmaPartialNorm, ← sigmaNormPow_def, hz, hc, j_liftUnit]
  have hN₁' : sigmaPartialNorm (SZ t d σr ht hd) z₁ n = c := hNz z₁ (by rw [hz₁, j_liftUnit]; exact hN₁)
  have hN₂' : sigmaPartialNorm (SZ t d σr ht hd) z₂ n = c := hNz z₂ (by rw [hz₂, j_liftUnit]; exact hN₂)
  set u := z₂ * z₁⁻¹ with hu_def
  have hu : sigmaPartialNorm (SZ t d σr ht hd) u n = 1 := by
    rw [hu_def, sigmaPartialNorm_mul_Z, sigmaPartialNorm_inv_Z, hN₁', hN₂', mul_inv_cancel]

  obtain ⟨w, hw⟩ := exists_unit_mul_SZ_eq t d σr ht hd n hn0 hσn hdist hfix u hu
  have hz₂w : z₂ = w * z₁ * (SZ t d σr ht hd w)⁻¹ := by
    calc z₂ = (z₂ * z₁⁻¹ * SZ t d σr ht hd w) * (SZ t d σr ht hd w)⁻¹ * z₁ := by group
      _ = w * (SZ t d σr ht hd w)⁻¹ * z₁ := by rw [← hu_def, hw]
      _ = w * z₁ * (SZ t d σr ht hd w)⁻¹ := mul_right_comm _ _ _

  have hδ₂ : δ₂' = j t d w * δ₁' * (Matrix.GeneralLinearGroup.map σr (j t d w))⁻¹ := by
    have h := congrArg (j t d) hz₂w
    rw [map_mul, map_mul, map_inv, j_SZ, hz₁, hz₂, j_liftUnit, j_liftUnit] at h
    exact h
  exact SigmaConjClasses.mk_eq_mk_iff.mpr ⟨j t d w, hδ₂⟩

end Assembly

end R2NormInj
p2m_reactivate "P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell.R2NormInj"

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.ellipticCell F)
    (δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h₁ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    LT.TwistedNorm.SigmaConjClasses.mk σ δ₁ = LT.TwistedNorm.SigmaConjClasses.mk σ δ₂ :=
  R2NormInj.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell hgen γ hγ δ₁ δ₂ h₁ h₂

end S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
end P2MW
export P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell (solution)
