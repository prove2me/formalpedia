-- Prove2me | solution 1 for MosonyiPetz.alpha_dual
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T19:02:59.597489+00:00
-- url     : https://prove2.me/submissions/f366316b-253e-4b76-9d37-7ee1cea52dee

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_alpha
import Definitions.Def_MosonyiPetz_weightedInner

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Kronecker
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetzAux

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-! ### Square roots of positive definite matrices -/

theorem sqrt_mul_sqrt {D : Matrix H H ℂ} (hD : D.PosSemidef) :
    cfc Real.sqrt D * cfc Real.sqrt D = D := by
  have h0 : 0 ≤ D := hD.nonneg
  have hsa : IsSelfAdjoint D := hD.isHermitian
  rw [← cfc_mul Real.sqrt Real.sqrt D (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _)]
  rw [cfc_congr (g := fun x : ℝ => x) fun x hx => by
    show Real.sqrt x * Real.sqrt x = x
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)]
  exact cfc_id' ℝ D

theorem sqrt_mul_invSqrt {D : Matrix H H ℂ} (hD : D.PosDef) :
    cfc Real.sqrt D * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D = 1 := by
  have hsa : IsSelfAdjoint D := hD.isHermitian
  rw [← cfc_mul Real.sqrt _ D (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _)]
  rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) fun x hx => by
    have : 0 < x := hD.isStrictlyPositive.spectrum_pos hx
    show Real.sqrt x * (Real.sqrt x)⁻¹ = 1
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr this).ne']
  exact cfc_const_one ℝ D

theorem invSqrt_mul_sqrt {D : Matrix H H ℂ} (hD : D.PosDef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D * cfc Real.sqrt D = 1 := by
  have hsa : IsSelfAdjoint D := hD.isHermitian
  rw [← cfc_mul _ Real.sqrt D (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _)]
  rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) fun x hx => by
    have : 0 < x := hD.isStrictlyPositive.spectrum_pos hx
    show (Real.sqrt x)⁻¹ * Real.sqrt x = 1
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr this).ne']
  exact cfc_const_one ℝ D

theorem invSqrt_mul_self_mul_invSqrt {D : Matrix H H ℂ} (hD : D.PosDef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D * D * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D = 1 := by
  have h := sqrt_mul_sqrt hD.posSemidef
  set R := cfc Real.sqrt D
  set S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D
  calc S * D * S = S * (R * R) * S := by rw [h]
    _ = (S * R) * (R * S) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [invSqrt_mul_sqrt hD, sqrt_mul_invSqrt hD, Matrix.one_mul]

/-! ### Positive maps preserve adjoints -/

theorem exists_posSemidef_sub {A : Matrix H H ℂ} (hA : A.IsHermitian) :
    ∃ P N : Matrix H H ℂ, P.PosSemidef ∧ N.PosSemidef ∧ A = P - N := by
  refine ⟨cfc (fun x : ℝ => max x 0) A, cfc (fun x : ℝ => max (-x) 0) A,
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _),
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _), ?_⟩
  rw [← cfc_sub _ _ A (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _),
    cfc_congr (f := fun x : ℝ => max x 0 - max (-x) 0) (g := fun x : ℝ => x) fun x _ => by
      show max x 0 - max (-x) 0 = x
      rcases le_total 0 x with hx | hx
      · rw [max_eq_left hx, max_eq_right (by linarith), sub_zero]
      · rw [max_eq_right hx, max_eq_left (by linarith), zero_sub, neg_neg]]
  exact (cfc_id' ℝ A hA).symm

theorem conjTranspose_map_of_posSemidef {Φ : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (hΦ : ∀ M : Matrix H H ℂ, M.PosSemidef → (Φ M).PosSemidef) (X : Matrix H H ℂ) :
    Φ Xᴴ = (Φ X)ᴴ := by
  have hherm : ∀ A : Matrix H H ℂ, A.IsHermitian → (Φ A).IsHermitian := by
    intro A hA
    obtain ⟨P, N, hP, hN, rfl⟩ := exists_posSemidef_sub hA
    rw [map_sub]
    exact (hΦ P hP).isHermitian.sub (hΦ N hN).isHermitian
  obtain ⟨A, B, hA, hB, hX, hXh⟩ : ∃ A B : Matrix H H ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      (2 : ℂ) • X = A - Complex.I • B ∧ (2 : ℂ) • Xᴴ = A + Complex.I • B := by
    refine ⟨X + Xᴴ, Complex.I • (X - Xᴴ), ?_, ?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
        add_comm]
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub]
    · rw [smul_smul, Complex.I_mul_I]
      module
    · rw [smul_smul, Complex.I_mul_I]
      module
  have hstar2 : star (2 : ℂ) = 2 := by norm_num
  have e1 : (2 : ℂ) • Φ Xᴴ = Φ A + Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hXh, map_add, LinearMap.map_smul]
  have e2 : (2 : ℂ) • (Φ X)ᴴ = ((2 : ℂ) • Φ X)ᴴ := by
    rw [Matrix.conjTranspose_smul, hstar2]
  have e3 : (2 : ℂ) • Φ X = Φ A - Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hX, map_sub, LinearMap.map_smul]
  have key : (2 : ℂ) • Φ Xᴴ = (2 : ℂ) • (Φ X)ᴴ := by
    rw [e1, e2, e3, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_I, hherm A hA, hherm B hB, neg_smul, sub_neg_eq_add]
  exact smul_right_injective _ two_ne_zero key

theorem posSemidef_map_of_isTwoPositive {T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (hT : IsTwoPositive T) (X : Matrix H H ℂ) (hX : X.PosSemidef) : (T X).PosSemidef :=
  (hT _ (hX.submatrix (Prod.snd : Fin 2 × H → H))).submatrix fun i : K => ((0 : Fin 2), i)

/-! ### The Hilbert–Schmidt adjoint -/

theorem sum4_rev {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ x, ∑ a, ∑ b, f i x a b = ∑ b, ∑ a, ∑ x, ∑ i, f i x a b := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := α)]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := β)]
  rw [Finset.sum_comm]

theorem map_eq_sum_single (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (B : Matrix H H ℂ) :
    T B = ∑ i, ∑ j, B i j • T (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single B]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- `Tr ((T* X)ᴴ B) = Tr (Xᴴ T(B))`. -/
theorem trace_channelAdjoint_conjTranspose_mul (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ)
    (X : Matrix K K ℂ) (B : Matrix H H ℂ) :
    ((channelAdjoint T X)ᴴ * B).trace = (Xᴴ * T B).trace := by
  rw [map_eq_sum_single T B]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    channelAdjoint, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, star_sum, star_mul',
    Complex.star_def, Complex.conj_conj, Finset.mul_sum]
  simp only [Finset.sum_mul]
  rw [sum4_rev]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem conjTranspose_channelAdjoint {T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (hstar : ∀ M, T Mᴴ = (T M)ᴴ) (Y : Matrix K K ℂ) :
    (channelAdjoint T Y)ᴴ = channelAdjoint T Yᴴ := by
  ext i j
  have hs : ∀ k l, T (Matrix.single i j 1) l k = star (T (Matrix.single j i 1) k l) := by
    intro k l
    rw [← Matrix.conjTranspose_apply, ← hstar, Matrix.conjTranspose_single, star_one]
  simp only [Matrix.conjTranspose_apply, channelAdjoint, star_sum, star_mul',
    Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs, Complex.star_def, Complex.conj_conj, mul_comm]

/-- `Tr (T*(Y) B) = Tr (Y T(B))` for a `*`-preserving `T`. -/
theorem trace_channelAdjoint_mul {T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (hstar : ∀ M, T Mᴴ = (T M)ᴴ) (Y : Matrix K K ℂ) (B : Matrix H H ℂ) :
    (channelAdjoint T Y * B).trace = (Y * T B).trace := by
  have h := trace_channelAdjoint_conjTranspose_mul T Yᴴ B
  rwa [← conjTranspose_channelAdjoint hstar, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

theorem channelAdjoint_one {T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (htr : ∀ A, (T A).trace = A.trace) : channelAdjoint T (1 : Matrix K K ℂ) = 1 := by
  ext i j
  have h := htr (Matrix.single i j 1)
  simp only [channelAdjoint, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← map_sum]
  change (starRingEnd ℂ) (T (Matrix.single i j 1)).trace = _
  rw [h]
  by_cases hij : i = j
  · subst hij; simp [Matrix.trace, Matrix.single_apply]
  · simp [Matrix.trace, Matrix.single_apply, hij]


/-! ### Blocks and Hermitian square roots -/

theorem cfc_conjTranspose (f : ℝ → ℝ) (D : Matrix H H ℂ) : (cfc f D)ᴴ = cfc f D := by
  rw [← Matrix.star_eq_conjTranspose]
  exact (cfc_predicate f D).star_eq

theorem eq_of_forall_trace {M N : Matrix K K ℂ}
    (h : ∀ X : Matrix K K ℂ, (Xᴴ * M).trace = (Xᴴ * N).trace) : M = N := by
  ext i j
  have := h (Matrix.single i j 1)
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq'] using this

def blockOf {ι ιE : Type*} (M : Matrix (ιE × ι) (ιE × ι) ℂ) (e e' : ιE) : Matrix ι ι ℂ :=
  Matrix.of fun i i' => M (e, i) (e', i')

theorem blockOf_conj {ι κ : Type*} [Fintype ι] (M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ)
    (A B : Matrix ι κ ℂ) (a b : Fin 2) :
    blockOf ((Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A)ᴴ * M *
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) B) a b = Aᴴ * blockOf M a b * B := by
  ext k l
  fin_cases a <;>
  simp [blockOf, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]

end MosonyiPetzAux

open MosonyiPetzAux MosonyiPetz in
theorem solution
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef) :
    (∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
      weightedInner (T (D 0)) X (alpha T (D 0) A) =
        weightedInner (D 0) (channelAdjoint T X) A) ∧
    (∀ φ : Matrix H H ℂ → Matrix K K ℂ,
      (∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
        weightedInner (T (D 0)) X (φ A) = weightedInner (D 0) (channelAdjoint T X) A) →
      φ = alpha T (D 0)) ∧
    alpha T (D 0) 1 = 1 ∧ IsTwoPositive (alpha T (D 0)) := by
  set R := cfc Real.sqrt (D 0)
  set R' := cfc Real.sqrt (T (D 0))
  set S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T (D 0))
  have hR'S : R' * S = 1 := sqrt_mul_invSqrt (hTD 0)
  have hSR' : S * R' = 1 := invSqrt_mul_sqrt (hTD 0)
  have halpha : ∀ A, alpha T (D 0) A = S * T (R * A * R) * S := fun A => rfl
  -- `⟨X, Y⟩_{T(D₁)}` with `Y = S Z S` collapses to `Tr (Xᴴ Z)`.
  have hcollapse : ∀ X Z : Matrix K K ℂ,
      weightedInner (T (D 0)) X (S * Z * S) = (Xᴴ * Z).trace := by
    intro X Z
    change (Xᴴ * R' * (S * Z * S) * R').trace = _
    calc (Xᴴ * R' * (S * Z * S) * R').trace = (Xᴴ * (R' * S) * Z * (S * R')).trace := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR'S, hSR', Matrix.mul_one, Matrix.mul_one]
  have hrhs : ∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
      weightedInner (D 0) (channelAdjoint T X) A = (Xᴴ * T (R * A * R)).trace := by
    intro A X
    change ((channelAdjoint T X)ᴴ * R * A * R).trace = _
    rw [← trace_channelAdjoint_conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h4 : ∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
      weightedInner (T (D 0)) X (alpha T (D 0) A) =
        weightedInner (D 0) (channelAdjoint T X) A := by
    intro A X
    rw [halpha, hcollapse, hrhs]
  refine ⟨h4, fun φ hφ => ?_, ?_, ?_⟩
  · funext A
    have hRφR : R' * φ A * R' = R' * alpha T (D 0) A * R' := by
      apply eq_of_forall_trace
      intro X
      have e1 := hφ A X
      rw [← h4] at e1
      change (Xᴴ * R' * φ A * R').trace = (Xᴴ * R' * alpha T (D 0) A * R').trace at e1
      simpa only [Matrix.mul_assoc] using e1
    calc φ A = S * (R' * φ A * R') * S := by
          simp only [← Matrix.mul_assoc, hSR', Matrix.one_mul]
          rw [Matrix.mul_assoc, hR'S, Matrix.mul_one]
      _ = S * (R' * alpha T (D 0) A * R') * S := by rw [hRφR]
      _ = alpha T (D 0) A := by
          simp only [← Matrix.mul_assoc, hSR', Matrix.one_mul]
          rw [Matrix.mul_assoc, hR'S, Matrix.mul_one]
  · rw [halpha, Matrix.mul_one, sqrt_mul_sqrt (hD 0).1.posSemidef]
    exact invSqrt_mul_self_mul_invSqrt (hTD 0)
  · intro X hX
    have hQ := hX.conjTranspose_mul_mul_same (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) R)
    have hTQ := hT _ hQ
    have hP := hTQ.conjTranspose_mul_mul_same (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) S)
    convert hP using 1
    ext ⟨a, k⟩ ⟨b, l⟩
    have e := congrFun (congrFun (blockOf_conj
      (QAlgorithms.idTensorSuperop (R := Fin 2) (⇑T) ((Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) R)ᴴ * X * (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) R))) S S a b) k) l
    simp only [blockOf, Matrix.of_apply] at e
    rw [e]
    change alpha T (D 0) (blockOf X a b) k l = _
    rw [halpha, cfc_conjTranspose]
    congr 3
    have e2 := blockOf_conj X R R a b
    rw [cfc_conjTranspose] at e2
    rw [← e2]
    rfl
