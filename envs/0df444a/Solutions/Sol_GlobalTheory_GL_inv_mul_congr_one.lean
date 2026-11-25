-- Prove2me | solution 1 for GlobalTheory.GL_inv_mul_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:36.465988+00:00
-- url     : https://prove2.me/submissions/7142a4f7-31ec-474c-8066-f574975cbae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GLInvMulCongrOneModUniformizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  intro K _ _ N π hπ0 hπ a a₁ ha ha₁
  set v : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v with hv
  let S : Subring K := v.integer
  have hpS : π ∈ S := (Valuation.mem_integer_iff _ _).2 hπ.le
  let p : S := ⟨π, hpS⟩
  let B : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha i j)⟩
  let B₁ : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha₁ i j)⟩
  let f : S →+* K := S.subtype
  let A' : Matrix (Fin N) (Fin N) S := 1 + p • B
  have hA : f.mapMatrix A' = (a : Matrix (Fin N) (Fin N) K) := by
    ext i j
    have h1 : (((1 : Matrix (Fin N) (Fin N) S) i j : S) : K) = (1 : Matrix (Fin N) (Fin N) K) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    change ((A' i j : S) : K) = _
    change (((1 + p • B) i j : S) : K) = _
    rw [Matrix.add_apply, Matrix.smul_apply, Subring.coe_add, smul_eq_mul, Subring.coe_mul, h1]
    change _ + π * (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) = _
    rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply]
    ring
  have hB : (a₁ : Matrix (Fin N) (Fin N) K) - a = π • f.mapMatrix (B₁ - B) := by
    ext i j
    rw [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, smul_eq_mul]
    change _ = π * (((B₁ i j - B i j : S)) : K)
    rw [AddSubgroupClass.coe_sub]
    change _ = π * (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j - π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j)
    rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply, Matrix.sub_apply]
    ring
  let I : Ideal S := Ideal.span {p}
  have hp : Ideal.Quotient.mk I p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hdet1 : A'.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det]
    have hm : (Ideal.Quotient.mk I).mapMatrix A' = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp only [A', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hp, zero_mul,
        add_zero, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, det_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdet1
  have hvd : v (f A'.det) = 1 := by
    have hlt : v (f (A'.det - 1)) < 1 := by
      rw [← hc, map_mul, map_mul]
      have hc' : v (f c) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
      calc v (f c) * v (f p) ≤ 1 * v (f p) := mul_le_mul_of_nonneg_right hc' zero_le'
        _ = v π := one_mul _
        _ < 1 := hπ
    have he : f A'.det = 1 + f (A'.det - 1) := by rw [map_sub, map_one]; ring
    rw [he, Valuation.map_add_eq_of_lt_left v (by rwa [v.map_one]), v.map_one]
  have hu : IsUnit A'.det := (Valuation.integer.integers v).isUnit_of_one' hvd
  have hinv : (a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹ = 1 := by
    rw [← hA, ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  have hainv : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = f.mapMatrix A'⁻¹ := by
    calc ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have key : ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1 = π • f.mapMatrix (A'⁻¹ * (B₁ - B)) := by
    calc ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a₁ - ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a := by
          rw [Units.val_mul, Units.inv_mul]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a₁ : Matrix (Fin N) (Fin N) K) - a) := by rw [Matrix.mul_sub]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * (π • f.mapMatrix (B₁ - B)) := by rw [hB]
      _ = π • (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * f.mapMatrix (B₁ - B)) := by rw [Matrix.mul_smul]
      _ = _ := by rw [map_mul, hainv]
  intro i j
  rw [key, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ0, one_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (Valuation.mem_integer_iff _ _).1 ((A'⁻¹ * (B₁ - B)) i j).2
end GlobalTheory
