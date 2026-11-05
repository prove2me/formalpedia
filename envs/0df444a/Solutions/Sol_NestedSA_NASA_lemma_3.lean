-- Prove2me | solution 1 for NestedSA.NASA.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:16:36.984696+00:00
-- url     : https://prove2.me/submissions/9740f714-5016-4169-8346-d2584a2c96f4

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

open NestedSA.NASA
open scoped RealInnerProductSpace

/-- Variational inequality of the projection onto a convex set. -/
private lemma l3_vi {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) :
    ∀ w, ∀ y ∈ X, ⟪w - P w, y - P w⟫ ≤ 0 := by
  intro w
  have hmem := (hP w).1
  have hne : Nonempty X := ⟨⟨P w, hmem⟩⟩
  have hbdd : BddBelow (Set.range fun y : X => ‖w - (y : EuclideanSpace ℝ (Fin n))‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _
  have heq : ‖w - P w‖ = ⨅ y : X, ‖w - (y : EuclideanSpace ℝ (Fin n))‖ := by
    apply le_antisymm
    · exact le_ciInf (fun y => (hP w).2 y y.2)
    · exact ciInf_le hbdd (⟨P w, hmem⟩ : X)
  exact (norm_eq_iInf_iff_real_inner_le_zero hX_cvx hmem).1 heq

/-- Firm nonexpansiveness of the residual `w ↦ w - P w`. -/
private lemma l3_firm {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (w w' : EuclideanSpace ℝ (Fin n)) :
    ‖(w - P w) - (w' - P w')‖ ^ 2 ≤ ⟪(w - P w) - (w' - P w'), w - w'⟫ := by
  have h1 := l3_vi X hX_cvx P hP w (P w') (hP w').1
  have h2 := l3_vi X hX_cvx P hP w' (P w) (hP w).1
  have e : ⟪(w - P w) - (w' - P w'), w - w'⟫ - ‖(w - P w) - (w' - P w')‖ ^ 2 =
      -⟪w - P w, P w' - P w⟫ - ⟪w' - P w', P w - P w'⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  linarith

private lemma l3_res_lip {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (w w' : EuclideanSpace ℝ (Fin n)) :
    ‖(w - P w) - (w' - P w')‖ ≤ ‖w - w'‖ := by
  have h := l3_firm X hX_cvx P hP w w'
  have h4 := real_inner_le_norm ((w - P w) - (w' - P w')) (w - w')
  rcases eq_or_lt_of_le (norm_nonneg ((w - P w) - (w' - P w'))) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- Two-sided quadratic bound for `φ(w) = ‖w - P w‖²`. -/
private lemma l3_phi_rem {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (w k : EuclideanSpace ℝ (Fin n)) :
    |‖(w + k) - P (w + k)‖ ^ 2 - ‖w - P w‖ ^ 2 - 2 * ⟪w - P w, k⟫| ≤ 3 * ‖k‖ ^ 2 := by
  have hup : ‖(w + k) - P (w + k)‖ ^ 2 ≤ ‖(w - P w) + k‖ ^ 2 := by
    have := (hP (w + k)).2 (P w) (hP w).1
    have e : w + k - P w = (w - P w) + k := by abel
    rw [e] at this
    gcongr
  have hlo : ‖w - P w‖ ^ 2 ≤ ‖((w + k) - P (w + k)) - k‖ ^ 2 := by
    have := (hP w).2 (P (w + k)) (hP (w + k)).1
    have e : w - P (w + k) = ((w + k) - P (w + k)) - k := by abel
    rw [e] at this
    gcongr
  rw [norm_add_sq_real] at hup
  rw [norm_sub_sq_real (w + k - P (w + k)) k] at hlo
  have hl := l3_res_lip X hX_cvx P hP (w + k) w
  have e2 : w + k - w = k := by abel
  rw [e2] at hl
  have hc : |⟪((w + k) - P (w + k)) - (w - P w), k⟫| ≤ ‖k‖ * ‖k‖ := by
    calc _ ≤ ‖((w + k) - P (w + k)) - (w - P w)‖ * ‖k‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖k‖ * ‖k‖ := by gcongr
  rw [inner_sub_left] at hc
  rw [abs_le] at hc ⊢
  constructor <;> nlinarith [norm_nonneg k]

/-- The scalar inequality behind the Lipschitz constant `L_∇η`. -/
private lemma l3_alg (β t A B D i1 i2 : ℝ) (hβ : 0 < β) (hβt : β * t = 1) (ht : 0 < t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hfirm : D ^ 2 ≤ i1 - t * i2) (hCS : i1 ≤ D * A)
    (hDle : D ≤ A + t * B) :
    β ^ 2 * D ^ 2 + (D ^ 2 + 2 * t * i2 + t ^ 2 * B ^ 2) ≤
      4 * ((1 + β) ^ 2 + (1 + t / 2) ^ 2) * (A ^ 2 + B ^ 2) := by
  have hb1 : β * D ≤ β * A + B := by
    calc β * D ≤ β * (A + t * B) := by gcongr
      _ = β * A + (β * t) * B := by ring
      _ = β * A + B := by rw [hβt, one_mul]
  have hβD : 0 ≤ β * D := by positivity
  have hsq : (β * D) ^ 2 ≤ (β * A + B) ^ 2 := by gcongr
  have h2 : (β * A + B) ^ 2 ≤ 2 * β ^ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (β * A - B)]
  have h3 : 2 * D * A - D ^ 2 ≤ A ^ 2 := by nlinarith [sq_nonneg (D - A)]
  have hkey : β ^ 2 * D ^ 2 + (D ^ 2 + 2 * t * i2 + t ^ 2 * B ^ 2) ≤
      2 * β ^ 2 * A ^ 2 + 2 * B ^ 2 + A ^ 2 + t ^ 2 * B ^ 2 := by
    have e : (β * D) ^ 2 = β ^ 2 * D ^ 2 := by ring
    nlinarith
  have hdiff : 4 * ((1 + β) ^ 2 + (1 + t / 2) ^ 2) * (A ^ 2 + B ^ 2) -
      (2 * β ^ 2 * A ^ 2 + 2 * B ^ 2 + A ^ 2 + t ^ 2 * B ^ 2) =
      A ^ 2 * (7 + 8 * β + 2 * β ^ 2 + 4 * t + t ^ 2) + B ^ 2 * (4 * (1 + β) ^ 2 + 2 + 4 * t) := by
    ring
  have : 0 ≤ A ^ 2 * (7 + 8 * β + 2 * β ^ 2 + 4 * t + t ^ 2) +
      B ^ 2 * (4 * (1 + β) ^ 2 + 2 + 4 * t) := by positivity
  linarith

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (hX_ne : X.Nonempty) (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (β : ℝ) (hβ : 0 < β) :
    Differentiable ℝ (etaJoint P β) ∧
      ∀ p q : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        ‖gradient (etaJoint P β) p - gradient (etaJoint P β) q‖ ≤ Leta β * ‖p - q‖ := by
  -- notation
  set R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun w => w - P w with hR
  set wf : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) := fun p => p.fst - β⁻¹ • p.snd with hwf
  set Gr : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun p => WithLp.toLp 2 (β • R (wf p), -R (wf p) - β⁻¹ • p.snd) with hGr
  have hβ0 : β ≠ 0 := hβ.ne'
  -- η in terms of the squared distance
  have heta : ∀ p : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      etaJoint P β p = β / 2 * ‖R (wf p)‖ ^ 2 - ‖p.snd‖ ^ 2 / (2 * β) := by
    intro p
    simp only [etaJoint, eta, ybar, hR, hwf]
    set y := P (p.fst - β⁻¹ • p.snd)
    have e : p.fst - β⁻¹ • p.snd - y = -(y - p.fst) - β⁻¹ • p.snd := by abel
    rw [e, norm_sub_sq_real (-(y - p.fst)) (β⁻¹ • p.snd), norm_neg, inner_neg_left, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hβ, real_inner_comm]
    field_simp
    ring
  -- gradient
  have hgrad : ∀ p, HasGradientAt (etaJoint P β) (Gr p) p := by
    intro p
    rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero,
      Asymptotics.isLittleO_iff]
    intro ε hε
    set C : ℝ := 3 * β / 2 * (1 + β⁻¹) ^ 2 + 1 / (2 * β) with hC
    have hCpos : 0 < C := by positivity
    have hball : Metric.ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (ε / C) ∈ nhds 0 :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    rw [InnerProductSpace.toDual_apply_apply, heta, heta]
    set k : EuclideanSpace ℝ (Fin n) := h.fst - β⁻¹ • h.snd with hk
    have hwk : wf (p + h) = wf p + k := by
      simp only [hwf, hk, WithLp.add_fst, WithLp.add_snd, smul_add]
      abel
    rw [hwk]
    have hrem := l3_phi_rem X hX_cvx P hP (wf p) k
    have hinner : ⟪Gr p, h⟫ = β * ⟪R (wf p), k⟫ - β⁻¹ * ⟪p.snd, h.snd⟫ := by
      simp only [hGr, WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_fst,
        WithLp.ofLp_snd, hk, inner_sub_right, inner_sub_left, inner_smul_left, inner_smul_right,
        inner_neg_left, RCLike.conj_to_real]
      linear_combination (⟪R (wf p), h.snd⟫) * (mul_inv_cancel₀ hβ0)
    rw [hinner, WithLp.add_snd, norm_add_sq_real]
    have hkn : ‖k‖ ≤ (1 + β⁻¹) * ‖h‖ := by
      have h1 : ‖h.fst‖ ≤ ‖h‖ := by
        have := WithLp.prod_norm_sq_eq_of_L2 h
        nlinarith [norm_nonneg h.fst, norm_nonneg h.snd, norm_nonneg h]
      have h2 : ‖h.snd‖ ≤ ‖h‖ := by
        have := WithLp.prod_norm_sq_eq_of_L2 h
        nlinarith [norm_nonneg h.fst, norm_nonneg h.snd, norm_nonneg h]
      calc ‖k‖ ≤ ‖h.fst‖ + ‖β⁻¹ • h.snd‖ := norm_sub_le _ _
        _ = ‖h.fst‖ + β⁻¹ * ‖h.snd‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
        _ ≤ ‖h‖ + β⁻¹ * ‖h‖ := by gcongr
        _ = (1 + β⁻¹) * ‖h‖ := by ring
    have hsn : ‖h.snd‖ ≤ ‖h‖ := by
      have := WithLp.prod_norm_sq_eq_of_L2 h
      nlinarith [norm_nonneg h.fst, norm_nonneg h.snd, norm_nonneg h]
    -- the remainder
    have hexpr : β / 2 * ‖R (wf p + k)‖ ^ 2 -
          (‖p.snd‖ ^ 2 + 2 * ⟪p.snd, h.snd⟫ + ‖h.snd‖ ^ 2) / (2 * β) -
        (β / 2 * ‖R (wf p)‖ ^ 2 - ‖p.snd‖ ^ 2 / (2 * β)) -
        (β * ⟪R (wf p), k⟫ - β⁻¹ * ⟪p.snd, h.snd⟫) =
      β / 2 * (‖R (wf p + k)‖ ^ 2 - ‖R (wf p)‖ ^ 2 - 2 * ⟪R (wf p), k⟫) - ‖h.snd‖ ^ 2 / (2 * β) := by
      field_simp
      ring
    rw [hexpr, Real.norm_eq_abs]
    have hrem' : |‖R (wf p + k)‖ ^ 2 - ‖R (wf p)‖ ^ 2 - 2 * ⟪R (wf p), k⟫| ≤ 3 * ‖k‖ ^ 2 := hrem
    have hk2 : ‖k‖ ^ 2 ≤ (1 + β⁻¹) ^ 2 * ‖h‖ ^ 2 := by
      rw [← mul_pow]; gcongr
    have hs2 : ‖h.snd‖ ^ 2 ≤ ‖h‖ ^ 2 := by gcongr
    have hb1 : |β / 2 * (‖R (wf p + k)‖ ^ 2 - ‖R (wf p)‖ ^ 2 - 2 * ⟪R (wf p), k⟫) -
        ‖h.snd‖ ^ 2 / (2 * β)| ≤ C * ‖h‖ ^ 2 := by
      calc _ ≤ |β / 2 * (‖R (wf p + k)‖ ^ 2 - ‖R (wf p)‖ ^ 2 - 2 * ⟪R (wf p), k⟫)| +
            |‖h.snd‖ ^ 2 / (2 * β)| := abs_sub _ _
        _ = β / 2 * |‖R (wf p + k)‖ ^ 2 - ‖R (wf p)‖ ^ 2 - 2 * ⟪R (wf p), k⟫| +
            ‖h.snd‖ ^ 2 / (2 * β) := by
          rw [abs_mul, abs_of_pos (show (0:ℝ) < β / 2 by positivity),
            abs_of_nonneg (show (0:ℝ) ≤ ‖h.snd‖ ^ 2 / (2 * β) by positivity)]
        _ ≤ β / 2 * (3 * ((1 + β⁻¹) ^ 2 * ‖h‖ ^ 2)) + ‖h‖ ^ 2 / (2 * β) := by
          gcongr
          linarith
        _ = C * ‖h‖ ^ 2 := by rw [hC]; ring
    have hhC : C * ‖h‖ ≤ ε := by
      rw [lt_div_iff₀ hCpos] at hh; linarith
    calc _ ≤ C * ‖h‖ ^ 2 := hb1
      _ = (C * ‖h‖) * ‖h‖ := by ring
      _ ≤ ε * ‖h‖ := by gcongr
  refine ⟨fun p => (hgrad p).differentiableAt, ?_⟩
  intro p q
  rw [(hgrad p).gradient, (hgrad q).gradient]
  set dx := p.fst - q.fst with hdx
  set dz := p.snd - q.snd with hdz
  set δ := R (wf p) - R (wf q) with hδ
  have hv : wf p - wf q = dx - β⁻¹ • dz := by
    simp only [hwf, hdx, hdz, smul_sub]; abel
  have hfirm : ‖δ‖ ^ 2 ≤ ⟪δ, dx⟫ - β⁻¹ * ⟪δ, dz⟫ := by
    have := l3_firm X hX_cvx P hP (wf p) (wf q)
    rw [hv, inner_sub_right, inner_smul_right] at this
    exact this
  have hpq : ‖p - q‖ ^ 2 = ‖dx‖ ^ 2 + ‖dz‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd]
  have e1 : (Gr p - Gr q).fst = β • δ := by
    simp only [WithLp.sub_fst, hGr, WithLp.toLp_fst]
    rw [← smul_sub]
  have e2 : (Gr p - Gr q).snd = -δ - β⁻¹ • dz := by
    simp only [WithLp.sub_snd, hGr, WithLp.toLp_snd]
    rw [hδ, hdz, smul_sub]; abel
  have hG : ‖Gr p - Gr q‖ ^ 2 = ‖β • δ‖ ^ 2 + ‖-δ - β⁻¹ • dz‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, e1, e2]
  have hG1 : ‖β • δ‖ ^ 2 = β ^ 2 * ‖δ‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]; ring
  have hG2 : ‖-δ - β⁻¹ • dz‖ ^ 2 = ‖δ‖ ^ 2 + 2 * β⁻¹ * ⟪δ, dz⟫ + β⁻¹ ^ 2 * ‖dz‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_neg, inner_neg_left, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
    ring
  have hCS : ⟪δ, dx⟫ ≤ ‖δ‖ * ‖dx‖ := real_inner_le_norm _ _
  have hDle : ‖δ‖ ≤ ‖dx‖ + β⁻¹ * ‖dz‖ := by
    calc ‖δ‖ ≤ ‖wf p - wf q‖ := l3_res_lip X hX_cvx P hP (wf p) (wf q)
      _ = ‖dx - β⁻¹ • dz‖ := by rw [hv]
      _ ≤ ‖dx‖ + ‖β⁻¹ • dz‖ := norm_sub_le _ _
      _ = ‖dx‖ + β⁻¹ * ‖dz‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
  have hLeta : Leta β ^ 2 = 4 * ((1 + β) ^ 2 + (1 + β⁻¹ / 2) ^ 2) := by
    unfold Leta; rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : 1 / (2 * β) = β⁻¹ / 2 := by field_simp
    rw [this]; norm_num
  have htot : ‖Gr p - Gr q‖ ^ 2 ≤ (Leta β * ‖p - q‖) ^ 2 := by
    rw [mul_pow, hG, hG1, hG2, hpq, hLeta]
    exact l3_alg β β⁻¹ ‖dx‖ ‖dz‖ ‖δ‖ ⟪δ, dx⟫ ⟪δ, dz⟫ hβ (mul_inv_cancel₀ hβ0)
      (inv_pos.mpr hβ) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hfirm hCS hDle
  have hR0 : 0 ≤ Leta β * ‖p - q‖ := by unfold Leta; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).1 htot
