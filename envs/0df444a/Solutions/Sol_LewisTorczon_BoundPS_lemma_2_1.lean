-- Prove2me | solution 1 for LewisTorczon.BoundPS.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:54:07.032862+00:00
-- url     : https://prove2.me/submissions/acb00975-efd1-4386-8b5e-adeaed95e2c6

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- A nonsingular real matrix is uniformly bounded below on nonzero integer vectors. -/
theorem aux_l21_lower_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ c : Fin n → ℤ, c ≠ 0 →
      ζ ≤ ‖(WithLp.toLp 2 (B.mulVec (fun r => (c r : ℝ))) : EuclideanSpace ℝ (Fin n))‖ := by
  set f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin B
    with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h1 : B.mulVec (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      exact this
    have h2 : WithLp.ofLp v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hB h1
    have : v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
    rw [this, h2]
    rfl
  obtain ⟨K, hKpos, hK⟩ := f.exists_antilipschitzWith hker
  refine ⟨1 / (K : ℝ), by positivity, ?_⟩
  intro c hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun r => (c r : ℝ)) with hx
  have hx1 : 1 ≤ ‖x‖ := by
    have h1 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    have h2 : (1 : ℝ) ≤ ‖x i‖ := by
      have : x i = (c i : ℝ) := rfl
      rw [this, Real.norm_eq_abs]
      have : (1 : ℤ) ≤ |c i| := Int.one_le_abs hi
      exact_mod_cast this
    linarith
  have hbound : ‖x‖ ≤ K * ‖f x‖ := ZeroHomClass.bound_of_antilipschitz f hK x
  have hfx : f x = WithLp.toLp 2 (B.mulVec (fun r => (c r : ℝ))) := rfl
  rw [← hfx]
  have hKpos' : (0 : ℝ) < K := by exact_mod_cast hKpos
  rw [div_le_iff₀ hKpos']
  nlinarith

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ k, ∀ c ∈ cols R k,
      stepOf P (R.Δ k) c ≠ 0 → ζ * R.Δ k ≤ ‖stepOf P (R.Δ k) c‖ := by
  obtain ⟨ζ, hζ, hbd⟩ := aux_l21_lower_bound P.B P.B_det_ne_zero
  refine ⟨ζ, hζ, ?_⟩
  intro k c _ hne
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    unfold stepOf
    simp only [Int.cast_zero, Pi.zero_apply]
    have : (P.B.mulVec fun _ => (0 : ℝ)) = 0 := Matrix.mulVec_zero _
    rw [this, smul_zero]
    rfl
  have hstep : stepOf P (R.Δ k) c =
      R.Δ k • (WithLp.toLp 2 (P.B.mulVec (fun r => (c r : ℝ))) :
        EuclideanSpace ℝ (Fin n)) := rfl
  rw [hstep, norm_smul, Real.norm_eq_abs]
  have h1 := hbd c hc
  have h2 : R.Δ k ≤ |R.Δ k| := le_abs_self _
  have h3 : 0 ≤ |R.Δ k| := abs_nonneg _
  calc ζ * R.Δ k ≤ ζ * |R.Δ k| := mul_le_mul_of_nonneg_left h2 hζ.le
    _ ≤ ‖(WithLp.toLp 2 (P.B.mulVec (fun r => (c r : ℝ))) : EuclideanSpace ℝ (Fin n))‖ *
          |R.Δ k| := by nlinarith
    _ = |R.Δ k| *
          ‖(WithLp.toLp 2 (P.B.mulVec (fun r => (c r : ℝ))) : EuclideanSpace ℝ (Fin n))‖ :=
        mul_comm _ _
