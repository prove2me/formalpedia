-- Prove2me | solution 1 for HorodeckiBoundKey.polar_twist
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:22:45.708009+00:00
-- url     : https://prove2.me/submissions/636078e5-a2f8-460b-9c5e-3e458adb0bb1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock twist twistingMatrix)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

namespace PolarTwistAux

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {R : Type*} [Fintype R] [DecidableEq R]

lemma fin (X : Matrix R R ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma sqrt_herm (X : Matrix R R ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix R R ℂ} (hX : X.PosSemidef) :
    cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary.  (Adapted from the accepted public
solution of `QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_3`, lemma `X5UH.polar`.) -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := sqrt_herm G
  have hAA : A * A = G := sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (fin _ _) (fin _ _),
      ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S :=
      ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩

/-- The trace of a positive semidefinite matrix is real. -/
lemma psd_trace_eq {X : Matrix R R ℂ} (h : X.PosSemidef) :
    X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

/-- The blocks of a twisted state: `σ''_{ab} = U_a σ_{ab} U_b†`. -/
lemma twistingMatrix_mul_apply {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key 2 → Matrix.unitaryGroup H ℂ) (ρ : Op (Key 2 × H)) (a b : Key 2) (s t : H) :
    (twistingMatrix U * ρ) (a, s) (b, t) = ∑ u, (U a : Matrix H H ℂ) s u * ρ (a, u) (b, t) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [twistingMatrix]
  · intro c _ hc
    simp [twistingMatrix, Ne.symm hc]
  · simp

lemma mul_twistingMatrix_conj_apply {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key 2 → Matrix.unitaryGroup H ℂ) (M : Op (Key 2 × H)) (a b : Key 2) (s t : H) :
    (M * (twistingMatrix U)ᴴ) (a, s) (b, t) =
      ∑ u, M (a, s) (b, u) * star ((U b : Matrix H H ℂ) t u) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [twistingMatrix, Matrix.conjTranspose_apply]
  · intro c _ hc
    simp [twistingMatrix, Matrix.conjTranspose_apply, Ne.symm hc]
  · simp

lemma keyBlock_twist {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key 2 → Matrix.unitaryGroup H ℂ) (ρ : Op (Key 2 × H)) (a b : Key 2) :
    keyBlock (twist U ρ) a b =
      (U a : Matrix H H ℂ) * keyBlock ρ a b * (U b : Matrix H H ℂ)ᴴ := by
  ext s t
  show (twistingMatrix U * ρ * (twistingMatrix U)ᴴ) (a, s) (b, t) = _
  rw [mul_twistingMatrix_conj_apply]
  simp only [twistingMatrix_mul_apply]
  simp only [keyBlock, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Overlap with the Bell projector of a two-qubit operator. -/
lemma bell_trace (M : Matrix (Key 2) (Key 2) ℂ) :
    (bellProjector 2 * M).trace =
      (1 / 2 : ℂ) * (M (0,0) (0,0) + M (1,1) (0,0) + M (0,0) (1,1) + M (1,1) (1,1)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bellProjector, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp
  ring

lemma traceRight_apply_eq_trace {H : Type*} [Fintype H] (ρ : Op (Key 2 × H)) (a b : Key 2) :
    QAlgorithms.traceRight ρ a b = (keyBlock ρ a b).trace := by
  simp [QAlgorithms.traceRight, keyBlock, Matrix.trace]

/-- For a positive semidefinite operator on `Key 2 × H`:
`Re Tr σ_{00,11} + Re Tr σ_{11,00} ≤ Re Tr σ_{00,00} + Re Tr σ_{11,11}`. -/
lemma block_ineq {H : Type*} [Fintype H] [DecidableEq H] (ρ : Op (Key 2 × H))
    (hρ : ρ.PosSemidef) :
    (keyBlock ρ (0,0) (1,1)).trace.re + (keyBlock ρ (1,1) (0,0)).trace.re ≤
      (keyBlock ρ (0,0) (0,0)).trace.re + (keyBlock ρ (1,1) (1,1)).trace.re := by
  have key : ∀ s : H, 0 ≤ (ρ ((0,0),s) ((0,0),s) + ρ ((1,1),s) ((1,1),s)
      - ρ ((0,0),s) ((1,1),s) - ρ ((1,1),s) ((0,0),s)).re := by
    intro s
    have h := hρ.dotProduct_mulVec_nonneg
      (Pi.single ((0,0),s) 1 - Pi.single ((1,1),s) 1)
    have hne : (((0,0),s) : Key 2 × H) ≠ ((1,1),s) := by
      intro h; simp [Prod.ext_iff] at h
    have e : star (Pi.single ((0,0),s) (1:ℂ) - Pi.single ((1,1),s) 1) ⬝ᵥ
        (ρ *ᵥ (Pi.single ((0,0),s) 1 - Pi.single ((1,1),s) 1)) =
        ρ ((0,0),s) ((0,0),s) + ρ ((1,1),s) ((1,1),s)
          - ρ ((0,0),s) ((1,1),s) - ρ ((1,1),s) ((0,0),s) := by
      simp [Matrix.mulVec_sub, Matrix.mulVec_single_one, sub_dotProduct, dotProduct_sub,
        Pi.single_apply, hne, hne.symm]
      ring
    rw [e] at h
    exact (Complex.nonneg_iff.mp h).1
  have hsum := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) => key s)
  simp only [Matrix.trace, Matrix.diag, keyBlock]
  simp only [Complex.sub_re, Complex.add_re, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    at hsum
  simp only [Complex.re_sum]
  linarith

/-- `|X| = √(X†X)` is positive semidefinite. -/
lemma sqrt_psd (X : Matrix R R ℂ) : (cfc Real.sqrt (Xᴴ * X)).PosSemidef :=
  (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt (Xᴴ * X)).posSemidef

end PolarTwistAux

open PolarTwistAux in
theorem solution {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (σ : Op (Key 2 × (S × T))) (hσ : IsDensityMatrix σ) :
    ∃ U : Key 2 → Matrix.unitaryGroup (S × T) ℂ,
      (keyBlock (twist U σ) (0,0) (1,1)).trace = (traceNorm (keyBlock σ (0,0) (1,1)) : ℂ) ∧
      2 * traceNorm (keyBlock σ (0,0) (1,1)) ≤
        (bellProjector 2 * traceRight (twist U σ)).trace.re := by
  set X := keyBlock σ (0,0) (1,1) with hX
  obtain ⟨W, hW⟩ := polar X
  let U : Key 2 → Matrix.unitaryGroup (S × T) ℂ := fun k => if k = (0,0) then star W else 1
  have hU00 : (U (0,0) : Matrix (S × T) (S × T) ℂ) = (W : Matrix (S × T) (S × T) ℂ)ᴴ := by
    simp [U, Matrix.star_eq_conjTranspose]
  have hU11 : (U (1,1) : Matrix (S × T) (S × T) ℂ) = 1 := by
    simp [U, Prod.ext_iff]
  have hWW : (W : Matrix (S × T) (S × T) ℂ)ᴴ * W = 1 := by
    have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have hpsd : (cfc Real.sqrt (Xᴴ * X)).PosSemidef := sqrt_psd X
  -- the twisted corner block is `|X|`
  have hcorner : keyBlock (twist U σ) (0,0) (1,1) = cfc Real.sqrt (Xᴴ * X) := by
    rw [keyBlock_twist, hU00, hU11, ← hX, Matrix.conjTranspose_one, Matrix.mul_one]
    conv_lhs => rw [← hW]
    rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have htr : (keyBlock (twist U σ) (0,0) (1,1)).trace = (traceNorm X : ℂ) := by
    rw [hcorner, psd_trace_eq hpsd]
    rfl
  refine ⟨U, htr, ?_⟩
  -- the singlet overlap
  have hpsd'' : (twist U σ).PosSemidef := by
    unfold twist
    exact hσ.1.mul_mul_conjTranspose_same _
  have hherm : (keyBlock (twist U σ) (1,1) (0,0)).trace =
      star (keyBlock (twist U σ) (0,0) (1,1)).trace := by
    rw [← Matrix.trace_conjTranspose]
    congr 1
    ext s t
    simp only [keyBlock, Matrix.conjTranspose_apply]
    have := congrFun (congrFun hpsd''.1 ((1,1),s)) ((0,0),t)
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]
  have hineq := block_ineq (twist U σ) hpsd''
  rw [bell_trace]
  simp only [traceRight_apply_eq_trace]
  rw [hherm, htr] at *
  simp only [Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    Complex.ofReal_re] at hineq ⊢
  norm_num
  linarith
