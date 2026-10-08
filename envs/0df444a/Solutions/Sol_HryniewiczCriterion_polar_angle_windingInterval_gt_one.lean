-- Prove2me | solution 1 for HryniewiczCriterion.polar_angle_windingInterval_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T16:05:33.16109+00:00
-- url     : https://prove2.me/submissions/ff037411-3ebd-4447-9fe1-41adddefd354

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

open HryniewiczCriterion
open scoped ContDiff

/-!
# Eigenvalues of the graph unitary of a `2 × 2` symplectic matrix

For `g ∈ SL(2, ℝ)` the unitary `W(Γ_g) W(Δ)⁻¹` equals `D̄⁻¹ • adj(Aᴴ) Aᵀ σ`, where
`A = graphBasis2 g`, `D = det A = (g₀₁ - g₁₀) + i (g₀₀ + g₁₁)` and `σ` swaps the coordinates.
In the polar form `g = R(x) P` its eigenvalues are `e^{i(x ± γ)}` with `cos γ = 2 / tr P`.
-/

namespace HryniewiczCriterion

open Matrix Complex Polynomial

noncomputable section

/-- For a `2 × 2` complex matrix with trace `μ₁ + μ₂` and determinant `μ₁ μ₂`, the roots of the
characteristic polynomial are `μ₁, μ₂`. -/
lemma charpoly_roots_fin_two {V : Matrix (Fin 2) (Fin 2) ℂ} {μ₁ μ₂ : ℂ}
    (htr : V.trace = μ₁ + μ₂) (hdet : V.det = μ₁ * μ₂) :
    V.charpoly.roots = {μ₁, μ₂} := by
  have h : V.charpoly = (X - C μ₁) * (X - C μ₂) := by
    rw [charpoly_fin_two, htr, hdet]; simp only [C_add, C_mul]; ring
  rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- `W(L) = (Aᴴ)⁻¹ Aᵀ` for an invertible basis matrix `A`. -/
lemma lagUnitary_eq {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.det ≠ 0) : lagUnitary A = (Aᴴ)⁻¹ * Aᵀ := by
  unfold lagUnitary
  rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]

/-- `D(g) = (g₀₁ - g₁₀) + i (g₀₀ + g₁₁)`, the determinant of `graphBasis2 g`. -/
def graphDet2 (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((g 0 1 - g 1 0 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * I

/-- The coordinate swap `σ = W(Δ)`. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma graphBasis2_eq (g : Matrix (Fin 2) (Fin 2) ℝ) :
    graphBasis2 g = !![1, -I; (g 0 0 : ℂ) + I * g 1 0, (g 0 1 : ℂ) + I * g 1 1] := by
  ext r k; fin_cases r <;> fin_cases k <;> simp [graphBasis2]

lemma det_graphBasis2 (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (graphBasis2 g).det = graphDet2 g := by
  rw [graphBasis2_eq, det_fin_two_of, graphDet2]
  push_cast
  linear_combination (g 1 0 : ℂ) * I_sq

lemma graphDet2_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) : graphDet2 g ≠ 0 := by
  intro h
  have hre : g 0 1 - g 1 0 = 0 := by simpa [graphDet2] using congrArg Complex.re h
  have him : g 0 0 + g 1 1 = 0 := by simpa [graphDet2] using congrArg Complex.im h
  have e1 : g 1 0 = g 0 1 := by linarith
  have e2 : g 1 1 = -g 0 0 := by linarith
  rw [det_fin_two, e1, e2] at hg
  nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 0 1)]

lemma swap2_inv : swap2⁻¹ = swap2 :=
  inv_eq_left_inv (by ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply])

lemma lagUnitary_graphBasis2_one : lagUnitary (graphBasis2 1) = swap2 := by
  have hd : (graphBasis2 1).det ≠ 0 := by
    rw [det_graphBasis2]; exact graphDet2_ne_zero (by simp)
  rw [lagUnitary_eq hd]
  have hT : (graphBasis2 1)ᵀ = (graphBasis2 1)ᴴ * swap2 := by
    rw [graphBasis2_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply]
  have hu : IsUnit ((graphBasis2 1)ᴴ).det := by
    rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (by simpa using hd)
  rw [hT, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- `W(Γ_g) W(Δ)⁻¹ = D̄⁻¹ • adj(Aᴴ) Aᵀ σ`. -/
lemma graphUnitary2_eq {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    graphUnitary2 g = (star (graphDet2 g))⁻¹ •
      (adjugate (graphBasis2 g)ᴴ * (graphBasis2 g)ᵀ * swap2) := by
  have hd : (graphBasis2 g).det ≠ 0 := by rw [det_graphBasis2]; exact graphDet2_ne_zero hg
  unfold graphUnitary2
  rw [lagUnitary_graphBasis2_one, swap2_inv, lagUnitary_eq hd, Matrix.inv_def,
    det_conjTranspose, det_graphBasis2]
  simp [Matrix.smul_mul]

lemma trace_graphUnitary2 {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    (graphUnitary2 g).trace = (star (graphDet2 g))⁻¹ * (-4 * I) := by
  rw [graphUnitary2_eq hg, trace_smul, smul_eq_mul]
  congr 1
  rw [det_fin_two] at hg
  rw [graphBasis2_eq]
  simp [trace_fin_two, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, swap2,
    Matrix.vecMul, dotProduct]
  apply Complex.ext
  · simp; ring
  · simp; linarith

lemma det_graphUnitary2 {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    (graphUnitary2 g).det = (star (graphDet2 g))⁻¹ * (-graphDet2 g) := by
  have hD := graphDet2_ne_zero hg
  have hsD : star (graphDet2 g) ≠ 0 := by simpa using hD
  rw [graphUnitary2_eq hg, det_smul, det_mul, det_mul, det_adjugate, det_transpose,
    det_conjTranspose, det_graphBasis2]
  have hs : swap2.det = -1 := by simp [swap2]
  rw [hs]
  simp only [Fintype.card_fin]
  field_simp
  ring

/-- The polar form of `D`: for `g = R(x) P` with `P` symmetric, `D = (tr P) i e^{ix}`. -/
lemma graphDet2_polar (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hPs : P 1 0 = P 0 1) :
    graphDet2 (rotationMatrix x * P) =
      ((P 0 0 + P 1 1 : ℝ) : ℂ) * I * exp (x * I) := by
  rw [exp_mul_I, graphDet2]
  simp only [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, hPs]
  apply Complex.ext <;> simp <;> ring

/-- Eigenvalues of the graph unitary in polar coordinates: for `g = R(x) P` with `P` symmetric
positive definite of determinant one, they are `e^{i(x ± γ)}`, `γ = arccos (2 / tr P)`. -/
theorem graphUnitary2_polar_roots (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef)
    (hdet : P.det = 1) :
    (graphUnitary2 (rotationMatrix x * P)).charpoly.roots =
      {exp ((x + Real.arccos (2 / (P 0 0 + P 1 1))) * I),
        exp ((x - Real.arccos (2 / (P 0 0 + P 1 1))) * I)} := by
  have hPs : P 1 0 = P 0 1 := by simpa using hP.1.apply 0 1
  have h00 : 0 < P 0 0 := by simpa using hP.diag_pos (i := 0)
  have h11 : 0 < P 1 1 := by simpa using hP.diag_pos (i := 1)
  rw [det_fin_two, hPs] at hdet
  set s := P 0 0 + P 1 1 with hs
  have hs0 : 0 < s := by linarith
  have hs2 : 2 ≤ s := by nlinarith [sq_nonneg (P 0 0 - P 1 1), sq_nonneg (P 0 1)]
  have hrot : (rotationMatrix x).det = 1 := by
    simp [rotationMatrix, det_fin_two]; nlinarith [Real.sin_sq_add_cos_sq x]
  have hg : (rotationMatrix x * P).det = 1 := by
    rw [det_mul, hrot, one_mul, det_fin_two, hPs, hdet]
  set γ := Real.arccos (2 / s)
  have hcos : Real.cos γ = 2 / s :=
    Real.cos_arccos (by have : 0 < 2 / s := by positivity
                        linarith) ((div_le_one hs0).mpr hs2)
  have hD := graphDet2_polar x hPs
  rw [← hs] at hD
  have hstar : star (graphDet2 (rotationMatrix x * P)) =
      (s : ℂ) * (-I) * exp (-(x * I)) := by
    rw [hD]
    simp [star_mul', ← exp_conj, map_neg]
  have hinv : (star (graphDet2 (rotationMatrix x * P)))⁻¹ = I * exp (x * I) / s := by
    rw [hstar]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    field_simp
    rw [mul_assoc, ← exp_add]
    simp
  apply charpoly_roots_fin_two
  · rw [trace_graphUnitary2 hg, hinv]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hc : exp (γ * I) + exp (-(γ * I)) = 2 * (2 / s : ℝ) := by
      rw [← hcos, Complex.ofReal_cos, Complex.cos]
      ring_nf
    rw [show exp ((x + γ) * I) + exp ((x - γ) * I) =
        exp (x * I) * (exp (γ * I) + exp (-(γ * I))) by
      rw [mul_add, ← exp_add, ← exp_add]; ring_nf, hc]
    push_cast
    linear_combination (-4 * exp (x * I) / s) * I_mul_I
  · rw [det_graphUnitary2 hg, hinv, hD, ← exp_add]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [show ((x : ℂ) + γ) * I + (x - γ) * I = x * I + x * I by ring, exp_add]
    field_simp
    simp [I_sq]

end

end HryniewiczCriterion

/-!
# Polar angle versus winding in `SL(2, ℝ)`

If `φ(t) = R(α(t)) P(t)` with `P(t)` positive definite and `θ` lifts the angle of `φ(t) e^{is}`,
then `θ - α - s` stays in `(-π/2, π/2)` (its cosine is `⟨P v, v⟩ / r > 0`), and at `t = 1`
it is at least `-γ`, where `cos γ = 2 / tr P(1)`. Together with the eigenvalues
`e^{i(α(1) ± γ)}` of the graph unitary this gives the HWZ (3.45)–(3.46) criterion.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

/-- `angPos (e^{iy}) = y - 2πk` for an integer `k`, and `angPos ∈ (0, 2π]`. -/
lemma angPos_exp_mul_I (y : ℝ) :
    ∃ k : ℤ, angPos (exp (y * I)) = y - 2 * Real.pi * k ∧ 0 < angPos (exp (y * I)) ∧
      angPos (exp (y * I)) ≤ 2 * Real.pi := by
  have harg := arg_exp_mul_I y
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) y
  have hk := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) y
  rw [← harg] at hmem hk
  rw [zsmul_eq_mul] at hk
  have hpi := Real.pi_pos
  unfold angPos
  split_ifs with hpos
  · exact ⟨toIocDiv Real.two_pi_pos (-Real.pi) y, by linarith, hpos, by linarith [hmem.2]⟩
  · refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) y - 1, by push_cast; linarith,
      by linarith [hmem.1], by linarith [hmem.2]⟩

/-- The eigen-angle sum of the graph unitary of `R(x) P`. -/
theorem eigenAngleSum_graphUnitary2_polar (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : P.PosDef) (hdet : P.det = 1) :
    eigenAngleSum (graphUnitary2 (rotationMatrix x * P)) =
      angPos (exp (((x + Real.arccos (2 / (P 0 0 + P 1 1)) : ℝ) : ℂ) * I)) +
        angPos (exp (((x - Real.arccos (2 / (P 0 0 + P 1 1)) : ℝ) : ℂ) * I)) := by
  unfold eigenAngleSum
  rw [graphUnitary2_polar_roots x hP hdet]
  simp

/-- The arithmetic core of (3.45)–(3.46): if `4π + angPos(e^{i(x+γ)}) + angPos(e^{i(x-γ)}) ≤ 2x`
with `0 ≤ γ < π/2`, then `x - γ > 2π`. -/
lemma two_pi_lt_of_angPos_sum {x γ a₁ a₂ : ℝ} {k₁ k₂ : ℤ} (hγ0 : 0 ≤ γ)
    (hγ : γ < Real.pi / 2) (h₁ : a₁ = (x + γ) - 2 * Real.pi * k₁) (h₁0 : 0 < a₁)
    (h₂ : a₂ = (x - γ) - 2 * Real.pi * k₂) (h₂0 : 0 < a₂)
    (h : 4 * Real.pi + (a₁ + a₂) ≤ 2 * x) : 2 * Real.pi < x - γ := by
  have hpi := Real.pi_pos
  have hk : (2 : ℝ) ≤ k₁ + k₂ := by
    have : 2 * Real.pi * 2 ≤ 2 * Real.pi * (k₁ + k₂) := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  by_contra hc
  push_neg at hc
  have hk2 : (k₂ : ℝ) < 1 := by
    have : 2 * Real.pi * k₂ < 2 * Real.pi * 1 := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hk2' : (k₂ : ℝ) ≤ 0 := by
    have : k₂ < 1 := by exact_mod_cast hk2
    exact_mod_cast (show k₂ ≤ 0 by omega)
  have hk1 : (2 : ℝ) ≤ k₁ := by linarith
  nlinarith

/-- Coordinates of `P v` against `v = e^{is}` and `v^⊥`, when `R(x) P v = r e^{iθ}`. -/
lemma polar_mulVec_coords {x θ s r : ℝ} {P : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (rotationMatrix x * P).mulVec (rotationVector s) = r • rotationVector θ) :
    (P.mulVec (rotationVector s)) 0 * Real.cos s + (P.mulVec (rotationVector s)) 1 * Real.sin s =
        r * Real.cos (θ - x - s) ∧
      -(P.mulVec (rotationVector s)) 0 * Real.sin s + (P.mulVec (rotationVector s)) 1 * Real.cos s =
        r * Real.sin (θ - x - s) := by
  rw [← Matrix.mulVec_mulVec] at h
  set w := P.mulVec (rotationVector s)
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp [rotationMatrix, rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hx := Real.sin_sq_add_cos_sq x
  rw [show θ - x - s = θ - (x + s) by ring, Real.cos_sub, Real.sin_sub, Real.cos_add,
    Real.sin_add]
  constructor
  · linear_combination (Real.cos x * Real.cos s - Real.sin x * Real.sin s) * e0 +
      (Real.sin x * Real.cos s + Real.cos x * Real.sin s) * e1 -
      (w 0 * Real.cos s + w 1 * Real.sin s) * hx
  · linear_combination (-(Real.sin x * Real.cos s + Real.cos x * Real.sin s)) * e0 +
      (Real.cos x * Real.cos s - Real.sin x * Real.sin s) * e1 -
      (-w 0 * Real.sin s + w 1 * Real.cos s) * hx

lemma rotationVector_ne_zero (s : ℝ) : rotationVector s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have := Real.sin_sq_add_cos_sq s
  rw [h0, h1] at this
  norm_num at this

/-- `⟨P v, v⟩ > 0` for `v = e^{is}` and `P` positive definite. -/
lemma posDef_rotationVector {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef) (s : ℝ) :
    0 < (P.mulVec (rotationVector s)) 0 * Real.cos s +
      (P.mulVec (rotationVector s)) 1 * Real.sin s := by
  have := hP.dotProduct_mulVec_pos (rotationVector_ne_zero s)
  simpa [dotProduct, Fin.sum_univ_two, rotationVector, mul_comm] using this

/-- The relative angle `θ - α - s` of an angle lift against the polar lift stays in
`(-π/2, π/2)` on `[0, 1]`. -/
theorem angleLift_sub_polar_mem {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {α θ : ℝ → ℝ} {s : ℝ}
    (hα : IsPolarAngleLift φ α) (hθ : IsAngleLift φ s θ) :
    -(Real.pi / 2) < θ 1 - α 1 - s ∧ θ 1 - α 1 - s < Real.pi / 2 := by
  set χ : ℝ → ℝ := fun t => θ t - α t - s with hχ
  have hcont : ContinuousOn χ (Set.Icc 0 1) :=
    (hθ.1.sub hα.1).sub continuousOn_const
  have hχ0 : χ 0 = 0 := by simp [hχ, hθ.2.1, hα.2.1]
  have hcos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < Real.cos (χ t) := by
    intro t ht
    obtain ⟨P, hP, hφt⟩ := hα.2.2 t ht
    obtain ⟨r, hr, hrt⟩ := hθ.2.2 t ht
    rw [hφt] at hrt
    have h1 := (polar_mulVec_coords hrt).1
    have h2 := posDef_rotationVector hP s
    rw [h1] at h2
    exact pos_of_mul_pos_right h2 hr.le
  have hpi := Real.pi_pos
  constructor
  · by_contra hc
    push_neg at hc
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc' zero_le_one hcont
      ⟨hc, by rw [hχ0]; linarith⟩
    have := hcos t ht
    rw [hteq, Real.cos_neg, Real.cos_pi_div_two] at this
    exact lt_irrefl _ this
  · by_contra hc
    push_neg at hc
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hcont
      ⟨by rw [hχ0]; linarith, hc⟩
    have := hcos t ht
    rw [hteq, Real.cos_pi_div_two] at this
    exact lt_irrefl _ this

/-- The algebraic inequality behind the lower bound `χ ≥ -γ`:
`⟨P v, v^⊥⟩ cos γ + ⟨P v, v⟩ sin γ ≥ 0`, with `cos γ = 2 / tr P`. -/
lemma posDef_det_one_angle_ineq {P : Matrix (Fin 2) (Fin 2) ℝ} (hPs : P 1 0 = P 0 1)
    (hdet : P 0 0 * P 1 1 - P 0 1 * P 0 1 = 1) (htr : 0 < P 0 0 + P 1 1) (s : ℝ) :
    0 ≤ (-(P.mulVec (rotationVector s)) 0 * Real.sin s +
          (P.mulVec (rotationVector s)) 1 * Real.cos s) * (2 / (P 0 0 + P 1 1)) +
      ((P.mulVec (rotationVector s)) 0 * Real.cos s +
          (P.mulVec (rotationVector s)) 1 * Real.sin s) *
        Real.sqrt (1 - (2 / (P 0 0 + P 1 1)) ^ 2) := by
  set σ := Real.sqrt (1 - (2 / (P 0 0 + P 1 1)) ^ 2) with hσ
  set S := P 0 0 + P 1 1 with hS
  have hS2 : 4 ≤ S ^ 2 := by nlinarith [sq_nonneg (P 0 0 - P 1 1)]
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσsq : σ ^ 2 = 1 - (2 / S) ^ 2 := by
    rw [hσ, Real.sq_sqrt]
    rw [div_pow, sub_nonneg, div_le_one (by positivity)]; linarith
  set M := σ * S / 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMsq : M ^ 2 = ((P 0 0 - P 1 1) / 2) ^ 2 + P 0 1 ^ 2 := by
    have hS0 : S ≠ 0 := by positivity
    have e1 : M ^ 2 = σ ^ 2 * S ^ 2 / 4 := by rw [hM]; ring
    have e2 : (1 - (2 / S) ^ 2) * S ^ 2 / 4 = S ^ 2 / 4 - 1 := by field_simp; ring
    rw [e1, hσsq, e2, hS]
    linear_combination hdet
  set p := S / 2 with hp
  have hp0 : 0 < p := by positivity
  have hpM : p ^ 2 = 1 + M ^ 2 := by rw [hMsq, hp, hS]; nlinarith
  set cs := Real.cos s
  set sn := Real.sin s
  have hu : sn ^ 2 + cs ^ 2 = 1 := Real.sin_sq_add_cos_sq s
  set X := (P 0 0 - P 1 1) / 2 * (cs ^ 2 - sn ^ 2) + 2 * P 0 1 * cs * sn with hX
  set Y := -2 * ((P 0 0 - P 1 1) / 2) * cs * sn + P 0 1 * (cs ^ 2 - sn ^ 2) with hY
  have hw : P.mulVec (rotationVector s) =
      ![P 0 0 * cs + P 0 1 * sn, P 0 1 * cs + P 1 1 * sn] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rotationVector,
      hPs, cs, sn]
  rw [hw]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hXc : (P 0 0 * cs + P 0 1 * sn) * cs + (P 0 1 * cs + P 1 1 * sn) * sn = p + X := by
    rw [hX, hp, hS]; linear_combination (P 0 0 + P 1 1) / 2 * hu
  have hYc : -(P 0 0 * cs + P 0 1 * sn) * sn + (P 0 1 * cs + P 1 1 * sn) * cs = Y := by
    rw [hY]; ring
  rw [hXc, hYc]
  have hXY : X ^ 2 + Y ^ 2 = M ^ 2 := by
    rw [hMsq, hX, hY]
    have : (cs ^ 2 + sn ^ 2) ^ 2 = 1 := by rw [add_comm, hu]; norm_num
    linear_combination (((P 0 0 - P 1 1) / 2) ^ 2 + P 0 1 ^ 2) * this
  have hc : 2 / S = 1 / p := by rw [hp]; field_simp
  have hσp : σ = M / p := by rw [hM, hp]; field_simp
  rw [hc, hσp]
  have key : 0 ≤ Y + M * X + M * p := by
    by_contra hneg
    push_neg at hneg
    have h1 : (Y + M * X) ^ 2 + (X - M * Y) ^ 2 = p ^ 2 * M ^ 2 := by
      rw [hpM]; linear_combination (1 + M ^ 2) * hXY
    nlinarith [sq_nonneg (X - M * Y), mul_nonneg hM0 hp0.le]
  have : Y * (1 / p) + (p + X) * (M / p) = (Y + M * X + M * p) / p := by
    field_simp; ring
  rw [this]
  positivity

/-- At `t = 1` the relative angle is at least `-γ`, `γ = arccos (2 / tr P(1))`. -/
theorem angleLift_sub_polar_ge {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {α θ : ℝ → ℝ} {s : ℝ}
    (hα : IsPolarAngleLift φ α) (hθ : IsAngleLift φ s θ) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : P.PosDef) (hdet : P.det = 1) (hφ1 : φ 1 = rotationMatrix (α 1) * P) :
    -Real.arccos (2 / (P 0 0 + P 1 1)) ≤ θ 1 - α 1 - s := by
  have hPs : P 1 0 = P 0 1 := by simpa using hP.1.apply 0 1
  have h00 : 0 < P 0 0 := by simpa using hP.diag_pos (i := 0)
  have h11 : 0 < P 1 1 := by simpa using hP.diag_pos (i := 1)
  rw [det_fin_two, hPs] at hdet
  have hS : 0 < P 0 0 + P 1 1 := by linarith
  have hS2 : 2 ≤ P 0 0 + P 1 1 := by nlinarith [sq_nonneg (P 0 0 - P 1 1), sq_nonneg (P 0 1)]
  obtain ⟨hlo, hhi⟩ := angleLift_sub_polar_mem hα hθ
  obtain ⟨r, hr, hrt⟩ := hθ.2.2 1 ⟨zero_le_one, le_rfl⟩
  rw [hφ1] at hrt
  obtain ⟨hc, hs⟩ := polar_mulVec_coords hrt
  have hineq := posDef_det_one_angle_ineq hPs hdet hS s
  rw [hc, hs] at hineq
  set γ := Real.arccos (2 / (P 0 0 + P 1 1))
  have hcosγ : Real.cos γ = 2 / (P 0 0 + P 1 1) :=
    Real.cos_arccos (by have : 0 < 2 / (P 0 0 + P 1 1) := by positivity
                        linarith) ((div_le_one hS).mpr hS2)
  have hsinγ : Real.sin γ = Real.sqrt (1 - (2 / (P 0 0 + P 1 1)) ^ 2) := Real.sin_arccos _
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg _
  have hγ1 : γ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by positivity)
  set χ := θ 1 - α 1 - s
  have hsin : 0 ≤ Real.sin (χ + γ) := by
    rw [Real.sin_add, hcosγ, hsinγ]
    have : r * (Real.sin χ * (2 / (P 0 0 + P 1 1)) +
        Real.cos χ * Real.sqrt (1 - (2 / (P 0 0 + P 1 1)) ^ 2)) ≥ 0 := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  by_contra hneg
  push_neg at hneg
  have : Real.sin (χ + γ) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  linarith

/-- **HWZ (3.45)–(3.46).** -/
theorem polar_angle_windingInterval_gt_one' (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α)
    (h : 4 * Real.pi + eigenAngleSum (graphUnitary2 (φ 1)) ≤ 2 * α 1) :
    ∀ d ∈ windingInterval φ, 1 < d := by
  rintro d ⟨s, -, θ, hθ, rfl⟩
  obtain ⟨P, hP, hφ1⟩ := hα.2.2 1 ⟨zero_le_one, le_rfl⟩
  have hrot : (rotationMatrix (α 1)).det = 1 := by
    simp [rotationMatrix, det_fin_two]; nlinarith [Real.sin_sq_add_cos_sq (α 1)]
  have hdet : P.det = 1 := by
    have := hsymp 1 ⟨zero_le_one, le_rfl⟩
    rwa [hφ1, det_mul, hrot, one_mul] at this
  have hlow := angleLift_sub_polar_ge hα hθ hP hdet hφ1
  rw [hφ1, eigenAngleSum_graphUnitary2_polar _ hP hdet] at h
  set γ := Real.arccos (2 / (P 0 0 + P 1 1))
  obtain ⟨k₁, e₁, p₁, -⟩ := angPos_exp_mul_I (α 1 + γ)
  obtain ⟨k₂, e₂, p₂, -⟩ := angPos_exp_mul_I (α 1 - γ)
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg _
  have h00 : 0 < P 0 0 := by simpa using hP.diag_pos (i := 0)
  have h11 : 0 < P 1 1 := by simpa using hP.diag_pos (i := 1)
  have hγ1 : γ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by positivity)
  have key := two_pi_lt_of_angPos_sum hγ0 hγ1 e₁ p₁ e₂ p₂ h
  have hpi := Real.pi_pos
  rw [lt_div_iff₀ (by positivity)]
  linarith

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (h0 : φ 0 = 1)
    (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α)
    (h : 4 * Real.pi + eigenAngleSum (graphUnitary2 (φ 1)) ≤ 2 * α 1) :
    ∀ d ∈ windingInterval φ, 1 < d :=
  polar_angle_windingInterval_gt_one' φ hsymp α hα h
