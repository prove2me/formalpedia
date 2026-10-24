-- Prove2me | solution 1 for ManPG.Conv.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T12:28:14.861053+00:00
-- url     : https://prove2.me/submissions/14a556d2-031b-4335-913f-a0d9b2cee3f7

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

set_option autoImplicit false

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPGProof
open ManPG.Conv

variable {n r : ℕ}

/-! ### Euclidean bridge -/

noncomputable def eL (n r : ℕ) : Mat n r ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin r) :=
  (LinearEquiv.curry (R := ℝ) (M := ℝ) (V := Fin n) (V₂ := Fin r)).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin n × Fin r → ℝ)).symm

lemma eL_apply (A : Mat n r) (p : Fin n × Fin r) : eL n r A p = A p.1 p.2 := rfl

lemma fI_eq (A B : Mat n r) : frobInner A B = inner ℝ (eL n r A) (eL n r B) := by
  rw [PiLp.inner_apply]
  simp only [eL_apply, frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma fN_eq (A : Mat n r) : frobNorm A = ‖eL n r A‖ := by
  rw [frobNorm, fI_eq, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma fN_nonneg (A : Mat n r) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

lemma fN_sq (A : Mat n r) : frobNorm A ^ 2 = frobInner A A := by
  rw [fN_eq, fI_eq, real_inner_self_eq_norm_sq]

lemma fN_smul (c : ℝ) (A : Mat n r) : frobNorm (c • A) = |c| * frobNorm A := by
  rw [fN_eq, fN_eq, map_smul, norm_smul, Real.norm_eq_abs]

lemma fN_sub_le (A B : Mat n r) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [fN_eq, fN_eq, fN_eq, map_sub]; exact norm_sub_le _ _

lemma fN_eq_zero {A : Mat n r} (h : frobNorm A = 0) : A = 0 := by
  rw [fN_eq, norm_eq_zero] at h
  exact (eL n r).map_eq_zero_iff.1 h

lemma fI_cs (A B : Mat n r) : frobInner A B ≤ frobNorm A * frobNorm B := by
  rw [fI_eq, fN_eq, fN_eq]; exact real_inner_le_norm _ _

lemma fI_smul_right (c : ℝ) (A B : Mat n r) : frobInner A (c • B) = c * frobInner A B := by
  rw [fI_eq, fI_eq, map_smul, real_inner_smul_right]

lemma fI_add_right (A B C : Mat n r) : frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [fI_eq, fI_eq, fI_eq, map_add, inner_add_right]

lemma fI_sub_right (A B C : Mat n r) : frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [fI_eq, fI_eq, fI_eq, map_sub, inner_sub_right]

lemma fI_add_left (A B C : Mat n r) : frobInner (A + B) C = frobInner A C + frobInner B C := by
  rw [fI_eq, fI_eq, fI_eq, map_add, inner_add_left]

lemma fI_sub_left (A B C : Mat n r) : frobInner (A - B) C = frobInner A C - frobInner B C := by
  rw [fI_eq, fI_eq, fI_eq, map_sub, inner_sub_left]

lemma fI_zero_right (A : Mat n r) : frobInner A 0 = 0 := by
  rw [fI_eq, map_zero, inner_zero_right]

/-- squared norm of the midpoint -/
lemma fN_mid (V W : Mat n r) :
    frobNorm ((1 / 2 : ℝ) • (V + W)) ^ 2
      = frobNorm V ^ 2 / 2 + frobNorm W ^ 2 / 2 - frobNorm (V - W) ^ 2 / 4 := by
  rw [fN_eq, fN_eq, fN_eq, fN_eq, map_smul, map_add, map_sub, norm_smul, mul_pow,
    norm_add_sq_real, norm_sub_sq_real]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  ring

/-! ### Topology -/

noncomputable def eC (n r : ℕ) : Mat n r ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin r) :=
  (eL n r).toContinuousLinearEquiv

lemma eC_apply (A : Mat n r) : eC n r A = eL n r A := rfl

lemma tendsto_iff_frob {ι : Type*} {l : Filter ι} (A : ι → Mat n r) (B : Mat n r) :
    Tendsto A l (𝓝 B) ↔ Tendsto (fun k => frobNorm (A k - B)) l (𝓝 0) := by
  rw [(eC n r).toHomeomorph.isEmbedding.tendsto_nhds_iff, tendsto_iff_norm_sub_tendsto_zero]
  simp only [Function.comp_def, fN_eq, map_sub]
  rfl

lemma continuous_fN : Continuous (fun A : Mat n r => frobNorm A) := by
  have : (fun A : Mat n r => frobNorm A) = fun A => ‖eC n r A‖ := by
    funext A; rw [fN_eq]; rfl
  rw [this]; exact continuous_norm.comp (eC n r).continuous

lemma continuous_fI : Continuous (fun p : Mat n r × Mat n r => frobInner p.1 p.2) := by
  have : (fun p : Mat n r × Mat n r => frobInner p.1 p.2)
      = fun p => inner ℝ (eC n r p.1) (eC n r p.2) := by
    funext p; rw [fI_eq]; rfl
  rw [this]
  exact continuous_inner.comp (((eC n r).continuous.comp continuous_fst).prodMk
    ((eC n r).continuous.comp continuous_snd))

lemma continuous_of_lip (g : Mat n r → Mat n r) (K : ℝ)
    (hg : ∀ X Y, frobNorm (g X - g Y) ≤ K * frobNorm (X - Y)) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun B => ?_
  have h0 := (tendsto_iff_frob (fun Y : Mat n r => Y) B (l := 𝓝 B)).1 tendsto_id
  refine (tendsto_iff_frob (fun Y => g Y) (g B)).2 ?_
  have h1 := h0.const_mul K
  rw [mul_zero] at h1
  exact squeeze_zero (fun _ => fN_nonneg _) (fun Y => hg Y B) h1

lemma continuous_of_lip_real (g : Mat n r → ℝ) (K : ℝ)
    (hg : ∀ X Y, |g X - g Y| ≤ K * frobNorm (X - Y)) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun B => ?_
  have h0 := (tendsto_iff_frob (fun Y : Mat n r => Y) B (l := 𝓝 B)).1 tendsto_id
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h1 := h0.const_mul K
  rw [mul_zero] at h1
  exact squeeze_zero (fun _ => norm_nonneg _) (fun Y => by
    rw [Real.norm_eq_abs]; exact hg Y B) h1

lemma isClosed_stiefel : IsClosed (stiefel n r) := by
  have : stiefel n r = {X : Mat n r | Xᵀ * X = 1} := rfl
  rw [this]
  exact isClosed_eq (Continuous.matrix_mul (Continuous.matrix_transpose continuous_id)
    continuous_id) continuous_const

lemma continuous_projT (W : Mat n r) : Continuous (fun X : Mat n r => projT X W) := by
  unfold projT
  fun_prop

/-! ### Tangent space algebra -/

lemma tangent_smul {X V : Mat n r} (hV : V ∈ tangent X) (c : ℝ) : c • V ∈ tangent X := by
  simp only [tangent, Set.mem_ofPred_eq] at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hV, smul_zero]

lemma tangent_add {X V W : Mat n r} (hV : V ∈ tangent X) (hW : W ∈ tangent X) :
    V + W ∈ tangent X := by
  simp only [tangent, Set.mem_ofPred_eq] at *
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hV, hW, add_zero]

lemma tangent_zero (X : Mat n r) : (0 : Mat n r) ∈ tangent X := by
  simp [tangent]

def tangentSub (X : Mat n r) : Submodule ℝ (Mat n r) where
  carrier := tangent X
  add_mem' := tangent_add
  zero_mem' := tangent_zero X
  smul_mem' c _ h := tangent_smul h c

lemma projT_mem {X : Mat n r} (hX : X ∈ stiefel n r) (W : Mat n r) : projT X W ∈ tangent X := by
  have hX' : Xᵀ * X = 1 := hX
  set P := projT X W with hP
  have hXP : Xᵀ * P = (1 / 2 : ℝ) • (Xᵀ * W - (Xᵀ * W)ᵀ) := by
    rw [hP, projT, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX',
      Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hX', Matrix.one_mul,
      sub_self, Matrix.zero_mul, zero_add, Matrix.transpose_mul, Matrix.transpose_transpose]
  show Pᵀ * X + Xᵀ * P = 0
  have hPX : Pᵀ * X = (Xᵀ * P)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hPX, hXP, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose,
    ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]

lemma projT_self {X W : Mat n r} (hW : W ∈ tangent X) : projT X W = W := by
  have h2 : Wᵀ * X = -(Xᵀ * W) := eq_neg_of_add_eq_zero_left hW
  rw [projT, h2, sub_neg_eq_add, Matrix.mul_add, ← two_smul ℝ (X * (Xᵀ * W)), smul_smul,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  norm_num

lemma projT_eq_zero {X Y : Mat n r} (hX : X ∈ stiefel n r)
    (hY : ∀ W ∈ tangent X, frobInner Y W = 0) : projT X Y = 0 := by
  have hX' : Xᵀ * X = 1 := hX
  set P := projT X Y with hP
  have hPT : P ∈ tangent X := projT_mem hX Y
  set S : Matrix (Fin r) (Fin r) ℝ := (1 / 2 : ℝ) • (Xᵀ * Y + Yᵀ * X) with hS
  have hYP : Y - P = X * S := by
    rw [hP, projT, hS, Matrix.mul_smul, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_assoc]
    module
  have hSt : Sᵀ = S := by
    rw [hS, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, add_comm]
  have hK : (Xᵀ * P)ᵀ = -(Xᵀ * P) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact eq_neg_of_add_eq_zero_left hPT
  have h0 : frobInner (Y - P) P = 0 := by
    rw [hYP, frobInner, Matrix.transpose_mul, hSt, Matrix.mul_assoc]
    set K := Xᵀ * P
    have : Matrix.trace (S * K) = -Matrix.trace (S * K) := by
      conv_lhs => rw [← Matrix.trace_transpose, Matrix.transpose_mul, hK, hSt,
        Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
    linarith
  have h1 : frobInner Y P = 0 := hY P hPT
  have h2 : frobInner P P = 0 := by
    have := fI_sub_left Y P P; linarith
  rw [← fN_sq] at h2
  exact fN_eq_zero (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)

/-! ### Analysis lemmas -/

lemma fI_abs (A B : Mat n r) : |frobInner A B| ≤ frobNorm A * frobNorm B := by
  rw [fI_eq, fN_eq, fN_eq]; exact abs_real_inner_le_norm _ _

lemma small_le {D Q : ℝ} (hQ : 0 ≤ Q) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → D ≤ s * Q) : D ≤ 0 := by
  by_contra hD
  push_neg at hD
  have hpos : 0 < D / (2 * (Q + 1)) := by positivity
  set s := min 1 (D / (2 * (Q + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos hpos
  have h1 := h s hs0 (min_le_left _ _)
  have h2 : s * Q ≤ D / (2 * (Q + 1)) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ
  have h3 : D / (2 * (Q + 1)) * Q < D := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

lemma cvx_seg {h : Mat n r → ℝ} (hc : ConvexOn ℝ Set.univ h) (X W : Mat n r) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : h (X + s • W) ≤ (1 - s) * h X + s * h (X + W) := by
  have := hc.2 (Set.mem_univ X) (Set.mem_univ (X + W)) (by linarith : (0:ℝ) ≤ 1 - s) hs0
    (by ring)
  rw [show (1 - s) • X + s • (X + W) = X + s • W by module] at this
  simpa [smul_eq_mul] using this

lemma descent_aux {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} {L Lh : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (X D : Mat n r) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    σ * (f (X + D) - f X - frobInner (gradf X) D - σ * (L / 2) * frobNorm D ^ 2) ≤ 0 := by
  have hφ : ∀ s : ℝ, HasDerivAt (fun u : ℝ => f (X + u • D)) (frobInner (gradf (X + s • D)) D) s := by
    intro s
    have h1 := hA.hasDerivAt_line (X + s • D) D
    have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
    have e : (fun u : ℝ => f (X + s • D + (u - s) • D)) = fun u => f (X + u • D) := by
      funext u; congr 1; rw [sub_smul]; abel
    rw [e] at h2; exact h2
  set c := frobInner (gradf X) D
  set q := frobNorm D ^ 2 with hq
  set χ : ℝ → ℝ := fun u => f (X + u • D) - u * c - σ * (L / 2) * u ^ 2 * q with hχ
  set χ' : ℝ → ℝ := fun u => frobInner (gradf (X + u • D)) D - c - σ * L * u * q with hχ'
  have hd : ∀ u, HasDerivAt χ (χ' u) u := by
    intro u
    simp only [hχ, hχ']
    exact (((hφ u).sub ((hasDerivAt_id' u).mul_const c)).sub
      (((hasDerivAt_pow 2 u).const_mul (σ * (L / 2))).mul_const q)).congr_deriv
      (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
  obtain ⟨u, hu, heq⟩ := exists_hasDerivAt_eq_slope χ χ' zero_lt_one
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hbd : σ * (frobInner (gradf (X + u • D)) D - c) ≤ L * u * q := by
    have e1 : frobInner (gradf (X + u • D)) D - c
        = frobInner (gradf (X + u • D) - gradf X) D := by rw [fI_sub_left]
    rw [e1]
    have hσx : ∀ x : ℝ, σ * x ≤ |x| := by
      intro x; rcases hσ with h | h <;> rw [h]
      · simpa using le_abs_self x
      · simpa using neg_le_abs x
    refine (hσx _).trans ((fI_abs _ _).trans ?_)
    have hl := hA.grad_lipschitz (X + u • D) X
    rw [add_sub_cancel_left, fN_smul, abs_of_pos hu.1] at hl
    have : q = frobNorm D * frobNorm D := by rw [hq, sq]
    rw [this]
    have := mul_le_mul_of_nonneg_right hl (fN_nonneg D)
    linarith
  have hneg : σ * χ' u ≤ 0 := by
    simp only [hχ']
    have : σ * (frobInner (gradf (X + u • D)) D - c - σ * L * u * q)
        = σ * (frobInner (gradf (X + u • D)) D - c) - (σ * σ) * L * u * q := by ring
    rw [this, hσ2]; linarith
  rw [heq] at hneg
  simp only [hχ, one_smul, zero_smul, add_zero, sub_zero, div_one, one_pow, mul_one,
    zero_mul] at hneg
  convert hneg using 2
  ring

lemma descent_le {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} {L Lh : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (X D : Mat n r) :
    f (X + D) ≤ f X + frobInner (gradf X) D + L / 2 * frobNorm D ^ 2 := by
  have := descent_aux hA X D 1 (Or.inl rfl)
  linarith

lemma descent_ge {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} {L Lh : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (X D : Mat n r) :
    f X + frobInner (gradf X) D - L / 2 * frobNorm D ^ 2 ≤ f (X + D) := by
  have := descent_aux hA X D (-1) (Or.inr rfl)
  linarith

lemma continuous_f {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} {L Lh : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun B => ?_
  have h0 := (tendsto_iff_frob (fun Y : Mat n r => Y) B (l := 𝓝 B)).1 tendsto_id
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h1 : Tendsto (fun Y : Mat n r => frobNorm (gradf B) * frobNorm (Y - B)
      + L / 2 * frobNorm (Y - B) ^ 2) (𝓝 B) (𝓝 0) := by
    have := (h0.const_mul (frobNorm (gradf B))).add ((h0.pow 2).const_mul (L / 2))
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun Y => ?_) h1
  have e1 := descent_le hA B (Y - B)
  have e2 := descent_ge hA B (Y - B)
  rw [add_sub_cancel] at e1 e2
  have e3 := abs_le.1 (fI_abs (gradf B) (Y - B))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [e3.1, e3.2]

/-- Lemma 5.1-type inequality from optimality of `V` along the segment `[0, V]`. -/
lemma star {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} (hc : ConvexOn ℝ Set.univ h)
    {X V : Mat n r} {t : ℝ} (ht : 0 < t) (hV : IsSubSol gradf h X t V) :
    frobInner (gradf X) V + h (X + V) ≤ h X - frobNorm V ^ 2 / t := by
  have hQ : 0 ≤ frobNorm V ^ 2 / (2 * t) := by positivity
  have key := small_le hQ (D := frobInner (gradf X) V + h (X + V) - h X + frobNorm V ^ 2 / t)
    (fun s hs0 hs1 => by
      have hmin := hV.2 ((1 - s) • V) (tangent_smul hV.1 _)
      simp only [subObj] at hmin
      rw [fI_smul_right, fN_smul, abs_of_nonneg (by linarith), mul_pow] at hmin
      have cvx := cvx_seg hc X V (s := 1 - s) (by linarith) (by linarith)
      have hprod : s * (frobInner (gradf X) V + h (X + V) - h X + frobNorm V ^ 2 / t
          - s * (frobNorm V ^ 2 / (2 * t))) ≤ 0 := by
        have e : s * (frobInner (gradf X) V + h (X + V) - h X + frobNorm V ^ 2 / t
            - s * (frobNorm V ^ 2 / (2 * t)))
            = (frobInner (gradf X) V + frobNorm V ^ 2 / (2 * t) + h (X + V))
              - ((1 - s) * frobInner (gradf X) V + (1 - s) ^ 2 * frobNorm V ^ 2 / (2 * t)
                + h (X + (1 - s) • V))
              + (h (X + (1 - s) • V) - ((1 - (1 - s)) * h X + (1 - s) * h (X + V))) := by
          field_simp <;> ring
        rw [e]; linarith
      by_contra hc'
      push_neg at hc'
      have := mul_pos hs0 (sub_pos.2 hc')
      linarith)
  linarith

/-- Lemma 5.2: sufficient decrease for small steps. -/
lemma decrease {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {L Lh M1 M2 G t : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (ht : 0 < t) {X V : Mat n r} (hX : X ∈ stiefel n r) (hV : IsSubSol gradf h X t V)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hαb : α ≤ abar L Lh M1 M2 G t) :
    f (R X (α • V)) + h (R X (α • V)) ≤ f X + h X - α * frobNorm V ^ 2 / (2 * t) := by
  have hξ : α • V ∈ tangent X := tangent_smul hV.1 α
  have nξ : frobNorm (α • V) = α * frobNorm V := by rw [fN_smul, abs_of_pos hα0]
  have nV0 := fN_nonneg V
  have b1 := hR.bound_3_1 X hX _ hξ
  have b2 := hR.bound_3_2 X hX _ hξ
  rw [nξ] at b1 b2
  have desc := descent_le hA X (R X (α • V) - X)
  rw [add_sub_cancel] at desc
  have hsplit : R X (α • V) - X = α • V + (R X (α • V) - (X + α • V)) := by abel
  rw [hsplit, fI_add_right, fI_smul_right] at desc
  rw [← hsplit] at desc
  have hΔ : frobInner (gradf X) (R X (α • V) - (X + α • V)) ≤ G * (M2 * (α * frobNorm V) ^ 2) :=
    (fI_cs _ _).trans (mul_le_mul (hG.bound X hX) b2 (fN_nonneg _) hG.G_pos.le)
  have hsq : frobNorm (R X (α • V) - X) ^ 2 ≤ (M1 * (α * frobNorm V)) ^ 2 :=
    pow_le_pow_left₀ (fN_nonneg _) b1 2
  have hh : h (R X (α • V)) ≤ h (X + α • V) + Lh * (M2 * (α * frobNorm V) ^ 2) := by
    have := hA.h_lipschitz (R X (α • V)) (X + α • V)
    have := (le_abs_self _).trans this
    have := mul_le_mul_of_nonneg_left b2 hA.Lh_nonneg
    linarith
  have cvx := cvx_seg hA.h_convex X V hα0.le hα1
  have st := star hA.h_convex ht hV
  have hK : 0 < c0 L M1 M2 G + Lh * M2 := by
    unfold c0
    have := hG.G_pos; have := hR.M2_pos; have := hA.L_pos; have := hA.Lh_nonneg
    positivity
  have hab : (c0 L M1 M2 G + Lh * M2) * α ≤ 1 / (2 * t) := by
    rw [abar, le_div_iff₀ (by positivity)] at hαb
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have e1 := mul_le_mul_of_nonneg_left st hα0.le
  have e2 := mul_le_mul_of_nonneg_right hab (by positivity : (0:ℝ) ≤ α * frobNorm V ^ 2)
  unfold c0 at e2
  have hL := hA.L_pos
  have e3 : L / 2 * frobNorm (R X (α • V) - X) ^ 2 ≤ L / 2 * (M1 * (α * frobNorm V)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e4 : 1 / (2 * t) * (α * frobNorm V ^ 2) = α * frobNorm V ^ 2 / (2 * t) := by ring
  have e5 : α * (h X - frobNorm V ^ 2 / t) = α * h X - 2 * (α * frobNorm V ^ 2 / (2 * t)) := by
    field_simp <;> ring
  rw [e4] at e2
  rw [e5] at e1
  nlinarith

/-- Uniqueness of the solution of the strongly convex subproblem. -/
lemma subsol_unique {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ} (hc : ConvexOn ℝ Set.univ h)
    {X V V' : Mat n r} {t : ℝ} (ht : 0 < t) (hV : IsSubSol gradf h X t V)
    (hV' : IsSubSol gradf h X t V') : V = V' := by
  have hM : (1 / 2 : ℝ) • (V + V') ∈ tangent X := tangent_smul (tangent_add hV.1 hV'.1) _
  have h1 := hV.2 _ hM
  have h2 := hV'.2 _ hM
  simp only [subObj] at h1 h2
  rw [fI_smul_right, fI_add_right, fN_mid] at h1 h2
  have cv := hc.2 (Set.mem_univ (X + V)) (Set.mem_univ (X + V')) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • (X + V) + (1 / 2 : ℝ) • (X + V') = X + (1 / 2 : ℝ) • (V + V') by module]
    at cv
  simp only [smul_eq_mul] at cv
  have eA : (frobNorm V ^ 2 / 2 + frobNorm V' ^ 2 / 2 - frobNorm (V - V') ^ 2 / 4) / (2 * t)
      = (frobNorm V ^ 2 / (2 * t) + frobNorm V' ^ 2 / (2 * t)) / 2
        - frobNorm (V - V') ^ 2 / (8 * t) := by
    field_simp <;> ring
  rw [eA] at h1 h2
  have h3 : frobNorm (V - V') ^ 2 / (8 * t) ≤ 0 := by linarith
  have h4 : frobNorm (V - V') ^ 2 ≤ 0 := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 8 * t)).1 h3; linarith
  have h5 : frobNorm (V - V') = 0 := by nlinarith [fN_nonneg (V - V')]
  exact sub_eq_zero.1 (fN_eq_zero h5)

lemma one_le_M1 {R : Mat n r → Mat n r → Mat n r} {M1 M2 : ℝ} (hR : RetrBounds R M1 M2)
    {X V : Mat n r} (hX : X ∈ stiefel n r) (hV : V ∈ tangent X) (hV0 : 0 < frobNorm V) :
    1 ≤ M1 := by
  have hQ : 0 ≤ M2 * frobNorm V := by have := hR.M2_pos; positivity
  have := small_le hQ (D := 1 - M1) (fun s hs0 _ => by
    have hξ : s • V ∈ tangent X := tangent_smul hV s
    have b1 := hR.bound_3_1 X hX _ hξ
    have b2 := hR.bound_3_2 X hX _ hξ
    have nξ : frobNorm (s • V) = s * frobNorm V := by rw [fN_smul, abs_of_pos hs0]
    have tri := fN_sub_le (R X (s • V) - X) (R X (s • V) - (X + s • V))
    rw [show R X (s • V) - X - (R X (s • V) - (X + s • V)) = s • V by abel] at tri
    rw [nξ] at b1 b2 tri
    have key : s * frobNorm V * (1 - M1 - s * (M2 * frobNorm V)) ≤ 0 := by nlinarith
    by_contra hc
    push_neg at hc
    have := mul_pos (mul_pos hs0 hV0) (sub_pos.2 hc)
    linarith)
  linarith

/-! ### Optimality conditions -/

lemma drop_quad {h : Mat n r → ℝ} (hc : ConvexOn ℝ Set.univ h) {X a : Mat n r} {t : ℝ}
    (ht : 0 < t) (T : Submodule ℝ (Mat n r))
    (hmin : ∀ W ∈ T, h X ≤ frobInner a W + frobNorm W ^ 2 / (2 * t) + h (X + W)) :
    ∀ W ∈ T, h X ≤ frobInner a W + h (X + W) := by
  intro W hW
  have hQ : 0 ≤ frobNorm W ^ 2 / (2 * t) := by positivity
  have := small_le hQ (D := h X - frobInner a W - h (X + W)) (fun s hs0 hs1 => by
    have h1 := hmin (s • W) (T.smul_mem s hW)
    rw [fI_smul_right, fN_smul, abs_of_pos hs0, mul_pow] at h1
    have cvx := cvx_seg hc X W hs0.le hs1
    have hp : s * ((h X - frobInner a W - h (X + W)) - s * (frobNorm W ^ 2 / (2 * t))) ≤ 0 := by
      have e : s * ((h X - frobInner a W - h (X + W)) - s * (frobNorm W ^ 2 / (2 * t)))
          = (h X - (s * frobInner a W + s ^ 2 * frobNorm W ^ 2 / (2 * t) + h (X + s • W)))
            + (h (X + s • W) - ((1 - s) * h X + s * h (X + W))) := by ring
      rw [e]; linarith
    by_contra hc'
    push_neg at hc'
    have := mul_pos hs0 (sub_pos.2 hc')
    linarith)
  linarith

/-- KKT via Hahn–Banach: a minimizer over a subspace yields a subgradient orthogonality relation. -/
lemma kkt {h : Mat n r → ℝ} (hc : ConvexOn ℝ Set.univ h) {Lh : ℝ}
    (hlip : ∀ X Y, |h X - h Y| ≤ Lh * frobNorm (X - Y)) (X a : Mat n r)
    (T : Submodule ℝ (Mat n r)) (hmin : ∀ W ∈ T, h X ≤ frobInner a W + h (X + W)) :
    ∃ G : Mat n r, IsSubgrad h X G ∧ ∀ W ∈ T, frobInner (a + G) W = 0 := by
  haveI : Nonempty (Set.Ioi (0:ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩
  let q : ℝ → Mat n r → ℝ := fun s W => (h (X + s • W) - h X) / s
  have hbdd : ∀ W, ∀ s : ℝ, 0 < s → -(Lh * frobNorm W) ≤ q s W := by
    intro W s hs
    have h1 := hlip (X + s • W) X
    rw [add_sub_cancel_left, fN_smul, abs_of_pos hs] at h1
    have h2 := neg_abs_le (h (X + s • W) - h X)
    show -(Lh * frobNorm W) ≤ (h (X + s • W) - h X) / s
    rw [le_div_iff₀ hs]
    nlinarith
  let N : Mat n r → ℝ := fun W => ⨅ s : Set.Ioi (0:ℝ), q s W
  have hN_le : ∀ W, ∀ s : ℝ, 0 < s → N W ≤ q s W := by
    intro W s hs
    refine ciInf_le ⟨-(Lh * frobNorm W), ?_⟩ (⟨s, hs⟩ : Set.Ioi (0:ℝ))
    rintro _ ⟨⟨s', hs'⟩, rfl⟩
    exact hbdd W s' hs'
  have hle_N : ∀ W c, (∀ s : ℝ, 0 < s → c ≤ q s W) → c ≤ N W := by
    intro W c hcs
    exact le_ciInf (fun s => hcs s.1 s.2)
  have hq_smul : ∀ W (c s : ℝ), 0 < c → 0 < s → q s (c • W) = c * q (c * s) W := by
    intro W c s hc0 hs
    simp only [q]
    rw [smul_smul, mul_comm s c]
    field_simp
  have hom : ∀ c : ℝ, 0 < c → ∀ W, N (c • W) = c * N W := by
    intro c hc0 W
    apply le_antisymm
    · have : N (c • W) / c ≤ N W := hle_N W _ (fun s hs => by
        rw [div_le_iff₀ hc0]
        have h1 := hN_le (c • W) (s / c) (div_pos hs hc0)
        rw [hq_smul W c (s / c) hc0 (div_pos hs hc0), mul_div_cancel₀ s hc0.ne'] at h1
        linarith [mul_comm c (q s W)])
      rwa [div_le_iff₀ hc0, mul_comm] at this
    · refine hle_N (c • W) _ (fun s hs => ?_)
      rw [hq_smul W c s hc0 hs]
      exact mul_le_mul_of_nonneg_left (hN_le W (c * s) (mul_pos hc0 hs)) hc0.le
  have hadd : ∀ W1 W2, N (W1 + W2) ≤ N W1 + N W2 := by
    intro W1 W2
    have key : ∀ s1 : ℝ, 0 < s1 → ∀ s2 : ℝ, 0 < s2 →
        q (s1 * s2 / (s1 + s2)) (W1 + W2) ≤ q s1 W1 + q s2 W2 := by
      intro s1 hs1 s2 hs2
      have hcv := hc.2 (Set.mem_univ (X + s1 • W1)) (Set.mem_univ (X + s2 • W2))
        (by positivity : (0:ℝ) ≤ s2 / (s1 + s2)) (by positivity : (0:ℝ) ≤ s1 / (s1 + s2))
        (by field_simp <;> ring : s2 / (s1 + s2) + s1 / (s1 + s2) = 1)
      have heq : (s2 / (s1 + s2)) • (X + s1 • W1) + (s1 / (s1 + s2)) • (X + s2 • W2)
          = X + (s1 * s2 / (s1 + s2)) • (W1 + W2) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        field_simp
        ring
      rw [heq] at hcv
      simp only [smul_eq_mul] at hcv
      simp only [q]
      rw [div_le_iff₀ (by positivity)]
      have e : ((h (X + s1 • W1) - h X) / s1 + (h (X + s2 • W2) - h X) / s2)
          * (s1 * s2 / (s1 + s2))
          = s2 / (s1 + s2) * h (X + s1 • W1) + s1 / (s1 + s2) * h (X + s2 • W2) - h X := by
        field_simp
        ring
      rw [e]; linarith
    have h1 : ∀ s1 : ℝ, 0 < s1 → N (W1 + W2) - N W2 ≤ q s1 W1 := by
      intro s1 hs1
      have : N (W1 + W2) - q s1 W1 ≤ N W2 := hle_N W2 _ (fun s2 hs2 => by
        have := hN_le (W1 + W2) _ (by positivity : (0:ℝ) < s1 * s2 / (s1 + s2))
        have := key s1 hs1 s2 hs2
        linarith)
      linarith
    have := hle_N W1 _ h1
    linarith
  let ℓ : Mat n r →ₗ[ℝ] ℝ :=
    { toFun := fun W => -frobInner a W
      map_add' := by intro x y; rw [fI_add_right]; ring
      map_smul' := by intro c x; simp only [RingHom.id_apply, smul_eq_mul]; rw [fI_smul_right]; ring }
  let f0 : Mat n r →ₗ.[ℝ] ℝ := ⟨T, ℓ.domRestrict T⟩
  have hf0 : ∀ x : f0.domain, f0 x ≤ N x := by
    rintro ⟨W, hW⟩
    show -frobInner a W ≤ N W
    refine hle_N W _ (fun s hs => ?_)
    have h1 := hmin (s • W) (T.smul_mem s hW)
    rw [fI_smul_right] at h1
    show -frobInner a W ≤ (h (X + s • W) - h X) / s
    rw [le_div_iff₀ hs]
    linarith
  obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f0 N hom hadd hf0
  let gE : EuclideanSpace ℝ (Fin n × Fin r) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (g ∘ₗ (eL n r).symm.toLinearMap)
  let G' := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n × Fin r))).symm gE
  let G := (eL n r).symm G'
  have hG : ∀ W, frobInner G W = g W := by
    intro W
    rw [fI_eq]
    simp only [G, LinearEquiv.apply_symm_apply]
    rw [InnerProductSpace.toDual_symm_apply]
    simp [gE]
  refine ⟨G, ?_, ?_⟩
  · intro Y
    rw [hG]
    have h1 := hg_le (Y - X)
    have h2 := hN_le (Y - X) 1 one_pos
    simp only [q, one_smul, div_one, add_sub_cancel] at h2
    linarith
  · intro W hW
    have e := hg_ext ⟨W, hW⟩
    change g W = -frobInner a W at e
    rw [fI_add_left, hG, e]
    ring

/-! ### The run -/

lemma fN_zero : frobNorm (0 : Mat n r) = 0 := by
  rw [fN_eq, map_zero, norm_zero]

lemma abar_pos {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {L Lh M1 M2 G t : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (ht : 0 < t) : 0 < abar L Lh M1 M2 G t := by
  unfold abar c0
  have := hG.G_pos; have := hR.M2_pos; have := hA.L_pos; have := hA.Lh_nonneg
  positivity

lemma run_mem {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {M1 M2 γ t : ℝ} {X V : ℕ → Mat n r} {α : ℕ → ℝ}
    (hR : RetrBounds R M1 M2) (hrun : IsManPGRun f gradf h R γ t X V α) :
    ∀ k, X k ∈ stiefel n r := by
  intro k
  induction k with
  | zero => exact hrun.1
  | succ k ih =>
    rw [(hrun.2 k).2.2]
    exact hR.mem _ ih _ (tangent_smul (hrun.2 k).1.1 _)

lemma run_step {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {γ t : ℝ} {X V : ℕ → Mat n r} {α : ℕ → ℝ}
    (hrun : IsManPGRun f gradf h R γ t X V α) (k : ℕ) :
    f (X (k + 1)) + h (X (k + 1)) ≤ f (X k) + h (X k) - α k * frobNorm (V k) ^ 2 / (2 * t) := by
  obtain ⟨j, hj, hdec, -⟩ := (hrun.2 k).2.1
  rw [(hrun.2 k).2.2, hj]
  exact hdec

lemma run_alpha {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {L Lh M1 M2 G γ t : ℝ} {X V : ℕ → Mat n r} {α : ℕ → ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (ht : 0 < t) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hrun : IsManPGRun f gradf h R γ t X V α) (k : ℕ) :
    min 1 (γ * abar L Lh M1 M2 G t) ≤ α k := by
  obtain ⟨j, hj, -, hfirst⟩ := (hrun.2 k).2.1
  rw [hj]
  by_contra hlt
  push_neg at hlt
  cases j with
  | zero =>
    rw [pow_zero] at hlt
    exact absurd hlt (not_lt.2 (min_le_left _ _))
  | succ i =>
    have h1 : γ ^ (i + 1) < γ * abar L Lh M1 M2 G t := lt_of_lt_of_le hlt (min_le_right _ _)
    rw [pow_succ, mul_comm] at h1
    have hi : γ ^ i < abar L Lh M1 M2 G t := lt_of_mul_lt_mul_left h1 hγ.1.le
    have hd := decrease hA hR hG ht (run_mem hR hrun k) (hrun.2 k).1 (pow_pos hγ.1 i)
      (pow_le_one₀ hγ.1.le hγ.2.le) hi.le
    exact absurd hd (not_le.2 (hfirst i (Nat.lt_succ_self i)))

set_option maxHeartbeats 1000000 in
lemma claim1 {n r : ℕ} {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {L Lh M1 M2 G : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    {γ t : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    {X V : ℕ → Mat n r} {α : ℕ → ℝ} (hrun : IsManPGRun f gradf h R γ t X V α) :
    ∀ Xbar : Mat n r, MapClusterPt Xbar atTop X → IsStationary gradf h Xbar := by
  set m := min 1 (γ * abar L Lh M1 M2 G t) with hm
  have hab0 := abar_pos hA hR hG ht
  have hm0 : 0 < m := lt_min one_pos (mul_pos hγ.1 hab0)
  have hmem := run_mem hR hrun
  have hstep : ∀ k, f (X (k + 1)) + h (X (k + 1))
      ≤ f (X k) + h (X k) - m / (2 * t) * frobNorm (V k) ^ 2 := by
    intro k
    have h1 := run_step hrun k
    have h2 := run_alpha hA hR hG ht hγ hrun k
    have h3 : m / (2 * t) * frobNorm (V k) ^ 2 ≤ α k * frobNorm (V k) ^ 2 / (2 * t) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
        (by positivity)
    linarith
  have htel : ∀ N, ∑ k ∈ Finset.range N, m / (2 * t) * frobNorm (V k) ^ 2
      ≤ f (X 0) + h (X 0) - (f (X N) + h (X N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ]; linarith [hstep N]
  have hanti : Antitone (fun k => f (X k) + h (X k)) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have := hstep k
    have : 0 ≤ m / (2 * t) * frobNorm (V k) ^ 2 := by positivity
    linarith
  intro Xbar hcl
  haveI : FirstCountableTopology (Mat n r) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin r → ℝ))
  obtain ⟨ψ, hψm, hψ⟩ := hcl.tendsto_subseq
  have hXbar : Xbar ∈ stiefel n r :=
    isClosed_stiefel.mem_of_tendsto hψ (Eventually.of_forall fun i => hmem (ψ i))
  have hcont_g : Continuous gradf := continuous_of_lip gradf L hA.grad_lipschitz
  have hcont_h : Continuous h := continuous_of_lip_real h Lh hA.h_lipschitz
  have hFc : Continuous (fun Y => f Y + h Y) := (continuous_f hA).add hcont_h
  have hlow : ∀ N, f Xbar + h Xbar ≤ f (X N) + h (X N) := by
    intro N
    have ht1 : Tendsto (fun i => f (X (ψ i)) + h (X (ψ i))) atTop (𝓝 (f Xbar + h Xbar)) :=
      (hFc.tendsto Xbar).comp hψ
    refine le_of_tendsto ht1 ?_
    filter_upwards [eventually_ge_atTop N] with i hi
    exact hanti (hi.trans (hψm.id_le i))
  have hsum : Summable (fun k => frobNorm (V k) ^ 2) := by
    refine summable_of_sum_range_le (fun k => sq_nonneg _)
      (c := (f (X 0) + h (X 0) - (f Xbar + h Xbar)) / (m / (2 * t))) (fun N => ?_)
    have h1 := htel N
    have h2 := hlow N
    rw [← Finset.mul_sum] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hV0 : Tendsto (fun k => frobNorm (V k)) atTop (𝓝 0) := by
    have h1 := hsum.tendsto_atTop_zero
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr (fun k => ?_)
    exact Real.sqrt_sq (fN_nonneg _)
  have hVt : Tendsto V atTop (𝓝 0) := (tendsto_iff_frob V 0).2 (by simpa using hV0)
  have hVψ := hVt.comp hψm.tendsto_atTop
  have hΦ : Continuous (fun p : Mat n r × Mat n r =>
      frobInner (gradf p.1) p.2 + frobNorm p.2 ^ 2 / (2 * t) + h (p.1 + p.2)) := by
    have c1 : Continuous (fun p : Mat n r × Mat n r => frobInner (gradf p.1) p.2) :=
      continuous_fI.comp ((hcont_g.comp continuous_fst).prodMk continuous_snd)
    have c2 : Continuous (fun p : Mat n r × Mat n r => frobNorm p.2) :=
      continuous_fN.comp continuous_snd
    exact (c1.add ((c2.pow 2).div_const _)).add (hcont_h.comp (continuous_fst.add continuous_snd))
  have hminbar : ∀ W ∈ tangentSub Xbar, h Xbar
      ≤ frobInner (gradf Xbar) W + frobNorm W ^ 2 / (2 * t) + h (Xbar + W) := by
    intro W hW
    have hW' : W ∈ tangent Xbar := hW
    have hL : Tendsto (fun i => frobInner (gradf (X (ψ i))) (V (ψ i))
        + frobNorm (V (ψ i)) ^ 2 / (2 * t) + h (X (ψ i) + V (ψ i))) atTop (𝓝 (h Xbar)) := by
      have := (hΦ.tendsto (Xbar, 0)).comp (hψ.prodMk_nhds hVψ)
      simpa [fI_zero_right, fN_zero, Function.comp_def] using this
    have hWψ : Tendsto (fun i => projT (X (ψ i)) W) atTop (𝓝 W) := by
      have := ((continuous_projT W).tendsto Xbar).comp hψ
      rwa [projT_self hW'] at this
    have hR' : Tendsto (fun i => frobInner (gradf (X (ψ i))) (projT (X (ψ i)) W)
        + frobNorm (projT (X (ψ i)) W) ^ 2 / (2 * t) + h (X (ψ i) + projT (X (ψ i)) W)) atTop
        (𝓝 (frobInner (gradf Xbar) W + frobNorm W ^ 2 / (2 * t) + h (Xbar + W))) := by
      have := (hΦ.tendsto (Xbar, W)).comp (hψ.prodMk_nhds hWψ)
      simpa only [Function.comp_def] using this
    refine le_of_tendsto_of_tendsto' hL hR' (fun i => ?_)
    exact (hrun.2 (ψ i)).1.2 _ (projT_mem (hmem (ψ i)) W)
  have hlin := drop_quad hA.h_convex ht (tangentSub Xbar) hminbar
  obtain ⟨Gs, hGs, horth⟩ :=
    kkt hA.h_convex hA.h_lipschitz Xbar (gradf Xbar) (tangentSub Xbar) hlin
  exact ⟨hXbar, Gs, hGs, projT_eq_zero hXbar (fun W hW => horth W hW)⟩

set_option maxHeartbeats 1000000 in
lemma claim2 {n r : ℕ} {f : Mat n r → ℝ} {gradf : Mat n r → Mat n r} {h : Mat n r → ℝ}
    {R : Mat n r → Mat n r → Mat n r} {L Lh M1 M2 G : ℝ}
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    {γ t : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    {X V : ℕ → Mat n r} {α : ℕ → ℝ} (hrun : IsManPGRun f gradf h R γ t X V α) :
    t = 1 / L → ∀ ε : ℝ, 0 < ε → ∀ Fstar : ℝ, IsOptimalValue f h Fstar →
      ∃ k : ℕ, k ≤ ⌈2 * L * (f (X 0) + h (X 0) - Fstar) / (γ * abar L Lh M1 M2 G t * ε ^ 2)⌉₊ ∧
        frobNorm (V k) ≤ ε / L ∧ IsEpsStationary gradf h L ε (X k) := by
  set m := min 1 (γ * abar L Lh M1 M2 G t) with hm
  have hab0 := abar_pos hA hR hG ht
  have hm0 : 0 < m := lt_min one_pos (mul_pos hγ.1 hab0)
  have hmem := run_mem hR hrun
  have hstep : ∀ k, f (X (k + 1)) + h (X (k + 1))
      ≤ f (X k) + h (X k) - m / (2 * t) * frobNorm (V k) ^ 2 := by
    intro k
    have h1 := run_step hrun k
    have h2 := run_alpha hA hR hG ht hγ hrun k
    have h3 : m / (2 * t) * frobNorm (V k) ^ 2 ≤ α k * frobNorm (V k) ^ 2 / (2 * t) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
        (by positivity)
    linarith
  have htel : ∀ N, ∑ k ∈ Finset.range N, m / (2 * t) * frobNorm (V k) ^ 2
      ≤ f (X 0) + h (X 0) - (f (X N) + h (X N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ]; linarith [hstep N]
  have hanti : Antitone (fun k => f (X k) + h (X k)) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have := hstep k
    have : 0 ≤ m / (2 * t) * frobNorm (V k) ^ 2 := by positivity
    linarith
  intro htL ε hε Fstar hF
  have hL0 := hA.L_pos
  obtain ⟨hFlow, -⟩ := hF
  set N := ⌈2 * L * (f (X 0) + h (X 0) - Fstar) / (γ * abar L Lh M1 M2 G t * ε ^ 2)⌉₊ with hN
  have hex : ∃ k, k ≤ N ∧ frobNorm (V k) ≤ ε / L := by
    by_contra hno
    push_neg at hno
    have hV0pos : 0 < frobNorm (V 0) := lt_of_le_of_lt (by positivity) (hno 0 (Nat.zero_le _))
    have hM1 := one_le_M1 hR (hmem 0) (hrun.2 0).1.1 hV0pos
    have hab1 : abar L Lh M1 M2 G t ≤ 1 := by
      have hK : 1 ≤ 2 * (c0 L M1 M2 G + Lh * M2) * t := by
        rw [htL]
        unfold c0
        have := hG.G_pos; have := hR.M2_pos; have := hA.Lh_nonneg
        have e : 2 * (M2 * G + L * M1 ^ 2 / 2 + Lh * M2) * (1 / L)
            = M1 ^ 2 + 2 * (M2 * G + Lh * M2) / L := by field_simp; ring
        rw [e]
        have : 0 ≤ 2 * (M2 * G + Lh * M2) / L := by positivity
        nlinarith
      unfold abar
      rw [div_le_one (by linarith)]
      exact hK
    have hmeq : m = γ * abar L Lh M1 M2 G t := by
      apply min_eq_right
      nlinarith [hγ.1, hγ.2]
    have h1 := htel (N + 1)
    have h2 := hFlow _ (hmem (N + 1))
    have h3 : ∑ k ∈ Finset.range (N + 1), m / (2 * t) * (ε / L) ^ 2
        < ∑ k ∈ Finset.range (N + 1), m / (2 * t) * frobNorm (V k) ^ 2 := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ (fun k hk => ?_)
      have hkN : k ≤ N := by
        rw [Finset.mem_range] at hk; omega
      exact mul_lt_mul_of_pos_left
        (pow_lt_pow_left₀ (hno k hkN) (by positivity) two_ne_zero) (by positivity)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    push_cast at h3
    have hK : m / (2 * t) * (ε / L) ^ 2 = γ * abar L Lh M1 M2 G t * ε ^ 2 / (2 * L) := by
      rw [hmeq, htL]; field_simp
    rw [hK] at h3
    have hceil := Nat.le_ceil (2 * L * (f (X 0) + h (X 0) - Fstar)
      / (γ * abar L Lh M1 M2 G t * ε ^ 2))
    rw [← hN] at hceil
    have hpos : 0 < γ * abar L Lh M1 M2 G t * ε ^ 2 := by
      have := hγ.1; positivity
    rw [div_le_iff₀ hpos] at hceil
    have e : ((N : ℝ) + 1) * (γ * abar L Lh M1 M2 G t * ε ^ 2 / (2 * L))
        = ((N : ℝ) + 1) * (γ * abar L Lh M1 M2 G t * ε ^ 2) / (2 * L) := by ring
    rw [e, div_lt_iff₀ (by positivity)] at h3
    nlinarith
  obtain ⟨k, hkN, hk⟩ := hex
  refine ⟨k, hkN, hk, hmem k, fun V' hV' => ?_⟩
  have hVk : IsSubSol gradf h (X k) (1 / L) (V k) := by rw [← htL]; exact (hrun.2 k).1
  rw [← subsol_unique hA.h_convex (by positivity) hVk hV']
  exact hk

end ManPGProof

open ManPG.Conv Filter Topology ProjLikeRetr.Stiefel in
theorem solution {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 G : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2) (hG : GradBound gradf G)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    (X V : ℕ → Mat n r) (α : ℕ → ℝ) (hrun : IsManPGRun f gradf h R γ t X V α) :
    (∀ Xbar : Mat n r, MapClusterPt Xbar atTop X → IsStationary gradf h Xbar) ∧
    (t = 1 / L → ∀ ε : ℝ, 0 < ε → ∀ Fstar : ℝ, IsOptimalValue f h Fstar →
      ∃ k : ℕ, k ≤ ⌈2 * L * (f (X 0) + h (X 0) - Fstar) / (γ * abar L Lh M1 M2 G t * ε ^ 2)⌉₊ ∧
        frobNorm (V k) ≤ ε / L ∧ IsEpsStationary gradf h L ε (X k)) := by
  exact ⟨ManPGProof.claim1 hA hR hG hγ ht hrun, ManPGProof.claim2 hA hR hG hγ ht hrun⟩
