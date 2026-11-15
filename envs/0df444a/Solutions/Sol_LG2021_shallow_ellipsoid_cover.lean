-- Prove2me | solution 1 for LG2021.shallow_ellipsoid_cover
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T15:20:26.556093+00:00
-- url     : https://prove2.me/submissions/a21b0d13-c1aa-4bcc-957a-ffeedc842b7c

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
set_option autoImplicit false

section

/-! Internal proof fragments reused from the accepted proof of the central-cut
ellipsoid cover. They are included explicitly so packaging does not depend on
unexposed helper declarations in an external theorem module. -/

noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod

private theorem rankOne_scaled_identity_det {n : ℕ} (hn : 1 ≤ n) (κ μ : ℝ) (hκ : κ ≠ 0) (p : Fin n → ℝ) (hp : p ⬝ᵥ p = 1) :
    det (κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p) = κ ^ (n - 1) * (κ + μ) := by
  have e : κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p =
      κ • (1 + vecMulVec ((μ / κ) • p) p) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
  rw [e, det_smul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin,
    dotProduct_smul, hp, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

private theorem native_ellipsoid_volume {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    MeasureTheory.volume (ellipsoid c B) =
      ENNReal.ofReal |B.det| * MeasureTheory.volume {u : Fin n → ℝ | u ⬝ᵥ u ≤ 1} := by
  have : ellipsoid c B = (fun x => c + x) '' (Matrix.toLin' B '' {u | u ⬝ᵥ u ≤ 1}) := by
    ext x
    simp only [ellipsoid, Set.mem_setOf_eq, Set.mem_image, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨B *ᵥ u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [this, Set.image_add_left, MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

private theorem normalized_cut_direction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    cutDirection B a ⬝ᵥ cutDirection B a = 1 ∧
      Bᵀ *ᵥ a = Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) • cutDirection B a ∧
      0 < Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) := by
  set w := Bᵀ *ᵥ a with hwdef
  have hBt : IsUnit Bᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hB
  have hw0 : w ≠ 0 := by
    intro h
    apply ha
    have : (Bᵀ)⁻¹ *ᵥ w = a := by rw [hwdef, mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : a ⬝ᵥ ((B * Bᵀ) *ᵥ a) = w ⬝ᵥ w := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hwdef, ← mulVec_transpose]
  have hqpos : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h => hw0 (dotProduct_self_eq_zero.mp h)))
  have hsq : 0 < Real.sqrt (w ⬝ᵥ w) := Real.sqrt_pos.2 hqpos
  refine ⟨?_, ?_, by rw [hq]; exact hsq⟩
  · unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  · unfold cutDirection
    rw [hq, ← hwdef, smul_smul, mul_one_div_cancel hsq.ne', one_smul]

end LG2021.Algorithm

end
end

section

/-!
Explicit shallow-cut cover for the offset used in Lattimore and György (2021).
The determinant, direction-normalization and volume identities are reused from
the accepted central-cut proof. The offset cover and its bound are proved here;
a central-cut theorem alone does not cover this geometry.
-/

noncomputable section
namespace LG2021.Algorithm

open Matrix MeasureTheory ModernConvex.EllipsoidMethod

private def shallowPerpendicular (d : ℕ) : ℝ :=
  Real.sqrt (1 + 3 / (4 * ((d : ℝ)^2 - 1)))

private def shallowParallel (d : ℕ) : ℝ := (2 * (d : ℝ) + 1) / (2 * ((d : ℝ) + 1))

private def shallowShift (d : ℕ) : ℝ := 1 / (2 * ((d : ℝ) + 1))

private def shallowMatrix {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :=
  B * (shallowPerpendicular d • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (shallowParallel d - shallowPerpendicular d) • vecMulVec p p)

private def shallowCenter {d : ℕ} (c : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :=
  c - shallowShift d • (B *ᵥ p)

private def shallowSlice {d : ℕ} (c : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ u, u ⬝ᵥ u ≤ 1 ∧ p ⬝ᵥ u ≤ 1 / (2 * (d : ℝ)) ∧ x = c + B *ᵥ u}

private theorem shallow_parameters_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < shallowPerpendicular d ∧ 0 < shallowParallel d ∧ 0 < shallowShift d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 0 < (d : ℝ)^2 - 1 := by nlinarith
  dsimp [shallowPerpendicular, shallowParallel, shallowShift]
  exact ⟨Real.sqrt_pos.mpr (by positivity), by positivity, by positivity⟩

private theorem shallow_scalar_bound {d : ℕ} (hd : 2 ≤ d) {s : ℝ}
    (hslo : -1 ≤ s) (hshi : s ≤ 1 / (2 * (d : ℝ))) :
    (shallowPerpendicular d)⁻¹ ^ 2 * (1 - s^2) +
      (shallowParallel d)⁻¹ ^ 2 * (s + shallowShift d)^2 ≤ 1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hm : (d : ℝ)^2 - 1 ≠ 0 := by nlinarith
  have h2m : 0 < 2 * (d : ℝ) - 1 := by linarith
  have h4m : 0 < 4 * (d : ℝ)^2 - 1 := by nlinarith
  have hp : 0 < 1 + 3 / (4 * ((d : ℝ)^2 - 1)) := by
    have : 0 < (d : ℝ)^2 - 1 := by nlinarith
    positivity
  have hperp : (shallowPerpendicular d)⁻¹ ^ 2 =
      4 * ((d : ℝ)^2 - 1) / (4 * (d : ℝ)^2 - 1) := by
    have he : 1 + 3 / (4 * ((d : ℝ)^2 - 1)) =
        (4 * (d : ℝ)^2 - 1) / (4 * ((d : ℝ)^2 - 1)) := by
      field_simp
      ring
    rw [shallowPerpendicular, inv_pow, Real.sq_sqrt hp.le]
    rw [he, inv_div]
  have hlin : 0 < (2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1)^2 := by positivity
  have hcoef : 0 ≤ 8 * (d : ℝ) * ((d : ℝ) + 1) /
      ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1)^2) := by positivity
  have hprod : (s + 1) * (s - 1 / (2 * (d : ℝ))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hshi)
  have hnegative := mul_nonpos_of_nonneg_of_nonpos hcoef hprod
  rw [hperp]
  have he : 4 * ((d : ℝ)^2 - 1) / (4 * (d : ℝ)^2 - 1) * (1 - s^2) +
      (shallowParallel d)⁻¹ ^ 2 * (s + shallowShift d)^2 - 1 =
      (8 * (d : ℝ) * ((d : ℝ) + 1) /
        ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1)^2)) *
          ((s + 1) * (s - 1 / (2 * (d : ℝ)))) := by
    dsimp [shallowParallel, shallowShift]
    field_simp [h2m.ne', h4m.ne']
    field_simp [show (-1 + (d : ℝ) * 2) ≠ 0 by linarith]
    ring
  linarith

private theorem shallow_cover {d : ℕ} (hd : 2 ≤ d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    shallowSlice c B p ⊆ ellipsoid (shallowCenter c B p) (shallowMatrix B p) := by
  obtain ⟨hκ, hl, _⟩ := shallow_parameters_pos hd
  rintro x ⟨u, hu, hcut, rfl⟩
  set s := p ⬝ᵥ u with hsdef
  have hperp : (u - s • p) ⬝ᵥ (u - s • p) = u ⬝ᵥ u - s^2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hp]
    rw [dotProduct_comm u p]
    ring
  have hp_perp : p ⬝ᵥ (u - s • p) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hp, smul_eq_mul]
    ring
  have hnn : 0 ≤ (u - s • p) ⬝ᵥ (u - s • p) := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsge : -1 ≤ s := by nlinarith
  let v := (shallowPerpendicular d)⁻¹ • (u - s • p) +
    (shallowParallel d)⁻¹ • ((s + shallowShift d) • p)
  refine ⟨v, ?_, ?_⟩
  · have he : v ⬝ᵥ v = (shallowPerpendicular d)⁻¹ ^ 2 * (u ⬝ᵥ u - s^2) +
        (shallowParallel d)⁻¹ ^ 2 * (s + shallowShift d)^2 := by
      dsimp [v]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, hperp, hp]
      rw [dotProduct_comm (u - s • p) p, hp_perp]
      ring
    rw [he]
    calc
      _ ≤ (shallowPerpendicular d)⁻¹ ^ 2 * (1 - s^2) +
          (shallowParallel d)⁻¹ ^ 2 * (s + shallowShift d)^2 := by gcongr
      _ ≤ 1 := shallow_scalar_bound hd hsge hcut
  · have hvm : ∀ v w z : Fin d → ℝ, vecMulVec v w *ᵥ z = (w ⬝ᵥ z) • v := by
      intro v w z
      ext i
      simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    have hdot : p ⬝ᵥ v = (shallowParallel d)⁻¹ * (s + shallowShift d) := by
      dsimp [v]
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hp_perp, dotProduct_smul, hp]
      simp
    dsimp [shallowCenter, shallowMatrix]
    rw [← mulVec_mulVec, add_mulVec, smul_mulVec, one_mulVec, smul_mulVec, hvm, hdot]
    dsimp [v]
    simp only [mulVec_add, mulVec_smul, mulVec_sub, smul_add, smul_smul]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

private theorem shallow_det {d : ℕ} (hd : 2 ≤ d) (B : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    (shallowMatrix B p).det = B.det *
      ((shallowPerpendicular d)^(d - 1) * shallowParallel d) := by
  rw [shallowMatrix, det_mul, rankOne_scaled_identity_det (by omega) _ _ (shallow_parameters_pos hd).1.ne' _ hp]
  congr 2
  ring

private theorem shallow_volume_ratio {d : ℕ} (hd : 2 ≤ d) :
    (shallowPerpendicular d)^(d - 1) * shallowParallel d ≤
      Real.exp (-1 / (8 * ((d : ℝ) + 1))) := by
  obtain ⟨hκ, hl, _⟩ := shallow_parameters_pos hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 0 < (d : ℝ)^2 - 1 := by nlinarith
  have harg : 0 < 1 + 3 / (4 * ((d : ℝ)^2 - 1)) := by positivity
  have hκlog : Real.log (shallowPerpendicular d) ≤ 3 / (8 * ((d : ℝ)^2 - 1)) := by
    rw [shallowPerpendicular, Real.log_sqrt harg.le]
    have h := Real.log_le_sub_one_of_pos harg
    have he : 3 / (8 * ((d : ℝ)^2 - 1)) = (3 / (4 * ((d : ℝ)^2 - 1))) / 2 := by
      field_simp
      ring
    rw [he]
    linarith
  have hllog : Real.log (shallowParallel d) ≤ -1 / (2 * ((d : ℝ) + 1)) := by
    have h := Real.log_le_sub_one_of_pos hl
    have he : shallowParallel d - 1 = -1 / (2 * ((d : ℝ) + 1)) := by
      dsimp [shallowParallel]
      field_simp
      ring
    rwa [he] at h
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hlog : Real.log ((shallowPerpendicular d)^(d - 1) * shallowParallel d) ≤
      -1 / (8 * ((d : ℝ) + 1)) := by
    rw [Real.log_mul (pow_pos hκ _).ne' hl.ne', Real.log_pow, hcast]
    calc
      _ ≤ ((d : ℝ) - 1) * (3 / (8 * ((d : ℝ)^2 - 1))) +
          (-1 / (2 * ((d : ℝ) + 1))) := by gcongr <;> linarith
      _ = _ := by field_simp; ring
  exact (Real.log_le_iff_le_exp (mul_pos (pow_pos hκ _) hl)).mp hlog

private theorem shallow_volume {d : ℕ} (hd : 2 ≤ d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    volume (ellipsoid (shallowCenter c B p) (shallowMatrix B p)) ≤
      ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1)))) * volume (ellipsoid c B) := by
  obtain ⟨hκ, hl, _⟩ := shallow_parameters_pos hd
  rw [native_ellipsoid_volume, native_ellipsoid_volume, shallow_det hd B p hp, abs_mul,
    abs_of_pos (mul_pos (pow_pos hκ _) hl), ENNReal.ofReal_mul (abs_nonneg _)]
  calc
    _ ≤ (ENNReal.ofReal |B.det| * ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1))))) *
        volume {u : Fin d → ℝ | u ⬝ᵥ u ≤ 1} := by
      gcongr
      exact shallow_volume_ratio hd
    _ = _ := by ac_rfl

private theorem shallow_cover_one (c : Fin 1 → ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (p : Fin 1 → ℝ) (hp : p ⬝ᵥ p = 1) :
    shallowSlice c B p ⊆ ellipsoid (shallowCenter c B p) (shallowMatrix B p) := by
  have hp0 : p 0 * p 0 = 1 := by simpa [dotProduct] using hp
  rintro x ⟨u, hu, hcut, rfl⟩
  have hu0 : u 0 * u 0 ≤ 1 := by simpa [dotProduct] using hu
  set s := p ⬝ᵥ u with hsdef
  have hs0 : s = p 0 * u 0 := by simp [hsdef, dotProduct]
  have hs2 : s^2 ≤ 1 := by
    rw [hs0, mul_pow]
    have hp2 : p 0 ^ 2 = 1 := by nlinarith
    rw [hp2, one_mul]
    nlinarith
  have hslo : -1 ≤ s := by nlinarith
  have hshi : s ≤ 1 / 2 := by simpa using hcut
  have huvec : u = s • p := by
    ext i
    fin_cases i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hs0]
    change u 0 = (p 0 * u 0) * p 0
    nlinarith [congrArg (fun t : ℝ => t * u 0) hp0]
  let v := ((4 / 3 : ℝ) * (s + 1 / 4)) • p
  refine ⟨v, ?_, ?_⟩
  · simp only [v, smul_dotProduct, dotProduct_smul, hp, smul_eq_mul]
    nlinarith [mul_nonneg (show 0 ≤ s + 1 by linarith) (show 0 ≤ 1 / 2 - s by linarith)]
  · have hvm : ∀ v w z : Fin 1 → ℝ, vecMulVec v w *ᵥ z = (w ⬝ᵥ z) • v := by
      intro v w z
      ext i
      simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    dsimp [shallowCenter, shallowMatrix]
    rw [← mulVec_mulVec, add_mulVec, smul_mulVec, one_mulVec, smul_mulVec, hvm]
    simp only [v, dotProduct_smul, hp, smul_eq_mul, mul_one]
    rw [huvec]
    norm_num [shallowPerpendicular, shallowParallel, shallowShift]
    simp only [smul_smul, mulVec_add, mulVec_smul, mulVec_neg]
    module

private theorem shallow_parameters_pos_of_pos {d : ℕ} (hd : 0 < d) :
    0 < shallowPerpendicular d ∧ 0 < shallowParallel d ∧ 0 < shallowShift d := by
  by_cases h : d = 1
  · subst d
    norm_num [shallowPerpendicular, shallowParallel, shallowShift]
  · exact shallow_parameters_pos (by omega)

private theorem shallow_cover_of_pos {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    shallowSlice c B p ⊆ ellipsoid (shallowCenter c B p) (shallowMatrix B p) := by
  by_cases h : d = 1
  · subst d
    exact shallow_cover_one c B p hp
  · exact shallow_cover (by omega) c B p hp

private theorem shallow_det_of_pos {d : ℕ} (hd : 0 < d) (B : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    (shallowMatrix B p).det = B.det *
      ((shallowPerpendicular d)^(d - 1) * shallowParallel d) := by
  rw [shallowMatrix, det_mul,
    rankOne_scaled_identity_det (by omega) _ _ (shallow_parameters_pos_of_pos hd).1.ne' _ hp]
  congr 2
  ring

private theorem shallow_volume_ratio_of_pos {d : ℕ} (hd : 0 < d) :
    (shallowPerpendicular d)^(d - 1) * shallowParallel d ≤
      Real.exp (-1 / (8 * ((d : ℝ) + 1))) := by
  by_cases h : d = 1
  · subst d
    have h := Real.add_one_le_exp (-1 / 16 : ℝ)
    norm_num [shallowPerpendicular, shallowParallel] at ⊢
    linarith
  · exact shallow_volume_ratio (by omega)

private theorem shallow_volume_of_pos {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    volume (ellipsoid (shallowCenter c B p) (shallowMatrix B p)) ≤
      ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1)))) * volume (ellipsoid c B) := by
  obtain ⟨hκ, hl, _⟩ := shallow_parameters_pos_of_pos hd
  rw [native_ellipsoid_volume, native_ellipsoid_volume, shallow_det_of_pos hd B p hp, abs_mul,
    abs_of_pos (mul_pos (pow_pos hκ _) hl), ENNReal.ofReal_mul (abs_nonneg _)]
  calc
    _ ≤ (ENNReal.ofReal |B.det| * ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1))))) *
        volume {u : Fin d → ℝ | u ⬝ᵥ u ≤ 1} := by
      gcongr
      exact shallow_volume_ratio_of_pos hd
    _ = _ := by ac_rfl

end LG2021.Algorithm

end
end

namespace LG2021
open Matrix MeasureTheory Algorithm

/-- An explicit shallow ellipsoid cover at normalized offset `1/(2*d)`.
This is the shallow-cut construction of Groetschel, Lovasz and Schrijver,
Geometric Algorithms and Combinatorial Optimization, Springer, 1988, Section 3.1,
specialized to the offset used by Lattimore and Gyorgy (COLT 2021), Lemma 3.
The displayed exponential factor is a convenient, slightly weaker bound. -/
theorem shallow_ellipsoid_cover {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    ∃ (B' : Matrix (Fin d) (Fin d) ℝ) (c' : Fin d → ℝ), B'.det ≠ 0 ∧
      {x | ∃ u, u ⬝ᵥ u ≤ 1 ∧ p ⬝ᵥ u ≤ 1 / (2 * (d : ℝ)) ∧ x = c + B *ᵥ u} ⊆
        ModernConvex.Ellipsoids.ellipsoid B' c' ∧
      |B'.det| ≤ Real.exp (-1 / (8 * ((d : ℝ) + 1))) * |B.det| ∧
      volume (ModernConvex.Ellipsoids.ellipsoid B' c') ≤
        ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1)))) *
          volume (ModernConvex.Ellipsoids.ellipsoid B c) := by
  have he (A : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) :
      ModernConvex.EllipsoidMethod.ellipsoid a A =
        ModernConvex.Ellipsoids.ellipsoid A a := by
    ext x
    simp only [ModernConvex.EllipsoidMethod.ellipsoid, ModernConvex.Ellipsoids.ellipsoid,
      Set.mem_setOf_eq, add_comm]
  obtain ⟨hκ, hl, _⟩ := shallow_parameters_pos_of_pos hd
  have hpositive := mul_pos (pow_pos hκ (d - 1)) hl
  refine ⟨shallowMatrix B p, shallowCenter c B p, ?_, ?_, ?_, ?_⟩
  · rw [shallow_det_of_pos hd B p hp]
    exact mul_ne_zero hB hpositive.ne'
  · rw [← he]
    exact shallow_cover_of_pos hd c B p hp
  · rw [shallow_det_of_pos hd B p hp, abs_mul, abs_of_pos hpositive]
    calc
      _ ≤ |B.det| * Real.exp (-1 / (8 * ((d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (shallow_volume_ratio_of_pos hd) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · simpa only [he] using shallow_volume_of_pos hd c B p hp

end LG2021

open Matrix MeasureTheory
theorem solution {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) :
    ∃ (B' : Matrix (Fin d) (Fin d) ℝ) (c' : Fin d → ℝ), B'.det ≠ 0 ∧
      {x | ∃ u, u ⬝ᵥ u ≤ 1 ∧ p ⬝ᵥ u ≤ 1 / (2 * (d : ℝ)) ∧ x = c + B *ᵥ u} ⊆
        ModernConvex.Ellipsoids.ellipsoid B' c' ∧
      |B'.det| ≤ Real.exp (-1 / (8 * ((d : ℝ) + 1))) * |B.det| ∧
      volume (ModernConvex.Ellipsoids.ellipsoid B' c') ≤
        ENNReal.ofReal (Real.exp (-1 / (8 * ((d : ℝ) + 1)))) *
          volume (ModernConvex.Ellipsoids.ellipsoid B c) := by
  exact LG2021.shallow_ellipsoid_cover hd c B hB p hp
