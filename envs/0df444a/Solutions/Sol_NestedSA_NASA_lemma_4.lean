-- Prove2me | solution 1 for NestedSA.NASA.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:27:39.236122+00:00
-- url     : https://prove2.me/submissions/70e67d93-9cd4-4ec4-b09c-ef66404fa807

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model
import Theorems.Thm_Gradient_descent_lemma
import Theorems.Thm_NestedSA_NASA_lemma_2
import Theorems.Thm_NestedSA_NASA_eq_3_21

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

/-- The gradient of `η` (as a function of the joint variable). -/
private noncomputable def l3Gr {n : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (p : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  WithLp.toLp 2 (β • ((p.fst - β⁻¹ • p.snd) - P (p.fst - β⁻¹ • p.snd)),
    -((p.fst - β⁻¹ • p.snd) - P (p.fst - β⁻¹ • p.snd)) - β⁻¹ • p.snd)

/-- Lemma 3 with the explicit gradient. -/
private lemma l3_core {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (β : ℝ) (hβ : 0 < β) :
    (∀ p, HasGradientAt (etaJoint P β) (l3Gr P β p) p) ∧
      ∀ p q : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        ‖l3Gr P β p - l3Gr P β q‖ ≤ Leta β * ‖p - q‖ := by
  -- notation
  set R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun w => w - P w with hR
  set wf : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) := fun p => p.fst - β⁻¹ • p.snd with hwf
  set Gr : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun p => WithLp.toLp 2 (β • R (wf p), -R (wf p) - β⁻¹ • p.snd) with hGr
  have hβ0 : β ≠ 0 := hβ.ne'
  have hkey : ∀ p, l3Gr P β p = Gr p := fun p => rfl
  simp only [hkey]
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
  refine ⟨hgrad, ?_⟩
  intro p q
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

/-- Nonnegativity of the quadratic form behind (3.16). -/
private lemma l4_quad (Pq Qq K D E : ℝ) (hP : 0 ≤ Pq) (hQ : 0 ≤ Qq) (hK : K ^ 2 ≤ 4 * Pq * Qq) :
    0 ≤ Pq * D ^ 2 - K * D * E + Qq * E ^ 2 := by
  rcases eq_or_lt_of_le hP with h0 | h0
  · subst h0
    have hK0 : K = 0 := by nlinarith [sq_nonneg K]
    subst hK0
    nlinarith [sq_nonneg E]
  · have h1 : 0 ≤ 4 * Pq * (Pq * D ^ 2 - K * D * E + Qq * E ^ 2) := by
      nlinarith [sq_nonneg (2 * Pq * D - K * E), mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg E)]
    have h4 : 0 < 4 * Pq := by linarith
    by_contra hcon
    push_neg at hcon
    have := mul_neg_of_pos_of_neg h4 hcon
    linarith

/-- The scalar bookkeeping of the proof of Lemma 4 (one iteration). -/
private lemma l4_alg (a b β c γ t LF Le Lg Ldf Fx Fx1 Fs η0 η1 Dn E Q C2 Ig Δg2 IF IA Izd Idv ΔZ2 : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (ht : 0 < t) (hbt0 : 0 ≤ b * t) (hbt1 : 0 ≤ 1 - b * t)
    (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hLg : 0 ≤ Lg) (hLdf : 0 ≤ Ldf) (hDn : 0 ≤ Dn) (hE : 0 ≤ E) (hQ0 : 0 ≤ Q)
    (hA : -Fx ≤ -Fx1 + t * IF + LF / 2 * (t * Dn) ^ 2)
    (hB : -η1 ≤ -η0 + -(t * (-(β * Dn ^ 2) - Izd) + a * t * (Idv - Izd)) +
      Le / 2 * (t ^ 2 * Dn ^ 2 + ΔZ2))
    (h321 : Izd + β * Dn ^ 2 ≤ 0)
    (hC : C2 = (1 - b * t) ^ 2 * Q ^ 2 + 2 * (1 - b * t) * (b * t) * Ig + (b * t) ^ 2 * Δg2)
    (hQ : Q ≤ E + Lg * (t * Dn))
    (hD : IF - IA ≤ Ldf * (E + Lg * (t * Dn)) * (Lg * Dn)) :
    a * (Fx1 - Fs) - η1 + γ / 2 * C2 - (a * (Fx - Fs) - η0 + γ / 2 * E ^ 2) ≤
      -(c * (t * (Dn ^ 2 + E ^ 2))) +
        (t ^ 2 / 2 * ((a * LF + Le + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf) * Dn ^ 2 + γ * b ^ 2 * Δg2) +
          t * (γ * b * (1 - b * t) * Ig + a * (IA - Idv)) + Le / 2 * ΔZ2) := by
  have S1 : a * (Fx1 - Fx) ≤ a * (t * IF + LF / 2 * (t * Dn) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ ha.le; linarith
  have S3 : (1 + a) * t * (Izd + β * Dn ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h321
  have S4 : a * t * (IF - IA) ≤ a * t * (Ldf * (E + Lg * (t * Dn)) * (Lg * Dn)) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hQ2 : Q ^ 2 ≤ (E + Lg * (t * Dn)) ^ 2 := by gcongr
  have hX0 : 0 ≤ 2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2 := by positivity
  have S5a : (1 - b * t) ^ 2 * Q ^ 2 ≤ (1 - b * t) * (E + Lg * (t * Dn)) ^ 2 := by
    have h1 : (1 - b * t) ^ 2 ≤ (1 - b * t) := by
      have e : (1 - b * t) ^ 2 = (1 - b * t) - (b * t) * (1 - b * t) := by ring
      have := mul_nonneg hbt0 hbt1
      linarith
    calc (1 - b * t) ^ 2 * Q ^ 2 ≤ (1 - b * t) * Q ^ 2 := by gcongr
      _ ≤ (1 - b * t) * (E + Lg * (t * Dn)) ^ 2 := by gcongr
  have S5b : (1 - b * t) * (E + Lg * (t * Dn)) ^ 2 ≤
      (1 - b * t) * E ^ 2 + (2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2) := by
    have : (1 - b * t) * (2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2) ≤
        1 * (2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hX0; linarith
    have e : (E + Lg * (t * Dn)) ^ 2 = E ^ 2 + (2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2) := by
      ring
    rw [e]
    linarith
  have S5 : γ / 2 * ((1 - b * t) ^ 2 * Q ^ 2) ≤
      γ / 2 * ((1 - b * t) * E ^ 2 + (2 * E * (Lg * (t * Dn)) + (Lg * (t * Dn)) ^ 2)) :=
    mul_le_mul_of_nonneg_left (S5a.trans S5b) (by positivity)
  have S6 : 0 ≤ (a * β - c) * Dn ^ 2 - Lg * (a * Ldf + γ) * Dn * E + (γ * b / 2 - c) * E ^ 2 :=
    l4_quad _ _ _ _ _ (by linarith) (by linarith) (by
      calc (Lg * (a * Ldf + γ)) ^ 2 = Lg ^ 2 * (a * Ldf + γ) ^ 2 := by ring
        _ ≤ 2 * (a * β - c) * (γ * b - 2 * c) := h316
        _ = 4 * (a * β - c) * (γ * b / 2 - c) := by ring)
  have S6' : 0 ≤ t * ((a * β - c) * Dn ^ 2 - Lg * (a * Ldf + γ) * Dn * E +
      (γ * b / 2 - c) * E ^ 2) := mul_nonneg ht.le S6
  rw [hC]
  linear_combination S1 + hB + S3 + S4 + S5 + S6'

/-- One iteration of Lemma 4: the merit function decreases up to `r^{k+1}`. -/
private lemma l4_step {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X)
    (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → EuclideanSpace ℝ (Fin m))
    (J : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsRun X P a b β τ x0 z0 u0 x z u G s J)
    (c γ : ℝ) (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hτ_one : ∀ k, τ k ≤ 1) (hbτ : ∀ k, b * τ k ≤ 1) (k : ℕ) (hxk : x k ∈ X) :
    W P f g X a γ β (x (k + 1)) (z (k + 1)) (u (k + 1)) - W P f g X a γ β (x k) (z k) (u k) ≤
      -(c * (τ k * (‖ybar P (x k) (z k) β - x k‖ ^ 2 + ‖g (x k) - u k‖ ^ 2))) +
        rTerm P f g a b γ β Lf Lg Ldf Ldg τ x z u G s J k := by
  have ha := hrun.a_pos
  have hb := hrun.b_pos
  have hβ := hrun.β_pos
  have hτ := hrun.τ_pos k
  have hβ0 : β ≠ 0 := hβ.ne'
  have hτ1 := hτ_one k
  have hbτ1 := hbτ k
  have hx' := hrun.step_x k
  have hz' := hrun.step_z k
  have hu' := hrun.step_u k
  unfold rTerm W
  set t := τ k with ht
  set d := ybar P (x k) (z k) β - x k with hd
  set A := fderiv ℝ g (x (k + 1)) with hAdef
  set v := (ContinuousLinearMap.adjoint (J (k + 1))) (s (k + 1)) with hv
  set LF := LgradF Lf Lg Ldf Ldg with hLF
  -- (A) descent for `F`
  have hfd := hA2.contDiff_f.differentiable (by norm_num)
  have hgd := hA2.contDiff_g.differentiable (by norm_num)
  have hFd : Differentiable ℝ (fun y => f (g y)) := hfd.comp hgd
  have hFg : ∀ y, HasGradientAt (fun y => -f (g y)) (-gradF f g y) y := by
    intro y
    have h1 : HasGradientAt (fun y => f (g y)) (gradF f g y) y := (hFd y).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at h1 ⊢
    rw [map_neg]
    exact h1.neg
  have hFL : ∀ y y', ‖-gradF f g y - -gradF f g y'‖ ≤ LF * ‖y - y'‖ := by
    intro y y'
    rw [neg_sub_neg, norm_sub_rev]
    exact lemma_2 f g Lf Lg Ldf Ldg hA2 y y'
  have hA := Gradient.descent_lemma hFg hFL (x (k + 1)) (x k)
  have hxdiff : x k - x (k + 1) = -(t • d) := by rw [hx']; abel
  rw [hxdiff, inner_neg_left, inner_neg_right, neg_neg, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos hτ] at hA
  -- (B) descent for `η`
  obtain ⟨hηg, hηL⟩ := l3_core X hX_cvx P hP β hβ
  have hng : ∀ q, HasGradientAt (fun q => -etaJoint P β q) (-l3Gr P β q) q := by
    intro q
    have h1 := hηg q
    rw [hasGradientAt_iff_hasFDerivAt] at h1 ⊢
    rw [map_neg]
    exact h1.neg
  have hnL : ∀ q q' : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      ‖-l3Gr P β q - -l3Gr P β q'‖ ≤ Leta β * ‖q - q'‖ := by
    intro q q'
    rw [neg_sub_neg, norm_sub_rev]
    exact hηL q q'
  have hB := Gradient.descent_lemma hng hnL (WithLp.toLp 2 (x k, z k))
    (WithLp.toLp 2 (x (k + 1), z (k + 1)))
  have hηp : etaJoint P β (WithLp.toLp 2 (x k, z k)) = eta P β (x k) (z k) := rfl
  have hηp' : etaJoint P β (WithLp.toLp 2 (x (k + 1), z (k + 1))) =
      eta P β (x (k + 1)) (z (k + 1)) := rfl
  have hR1 : β • ((x k - β⁻¹ • z k) - P (x k - β⁻¹ • z k)) = -(β • d) - z k := by
    rw [hd]; unfold ybar
    rw [smul_sub, smul_sub, smul_smul, mul_inv_cancel₀ hβ0, one_smul, smul_sub]; abel
  have hR2 : -((x k - β⁻¹ • z k) - P (x k - β⁻¹ • z k)) - β⁻¹ • z k = d := by
    rw [hd]; unfold ybar; abel
  have hzdiff : z (k + 1) - z k = (a * t) • (v - z k) := by
    rw [hz']; module
  have hGin : ⟪l3Gr P β (WithLp.toLp 2 (x k, z k)),
      WithLp.toLp 2 (x (k + 1), z (k + 1)) - WithLp.toLp 2 (x k, z k)⟫ =
      t * (-(β * ‖d‖ ^ 2) - ⟪z k, d⟫) + a * t * (⟪d, v⟫ - ⟪z k, d⟫) := by
    rw [WithLp.prod_inner_apply]
    simp only [l3Gr, WithLp.ofLp_toLp, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub,
      WithLp.toLp_fst, WithLp.toLp_snd]
    have hxd2 : x (k + 1) - x k = t • d := by rw [hx']; abel
    rw [hR1, hR2, hzdiff, hxd2, inner_smul_right, inner_smul_right, inner_sub_left,
      inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq, inner_sub_right d v (z k),
      real_inner_comm d (z k)]
  have hpn : ‖WithLp.toLp 2 (x (k + 1), z (k + 1)) - WithLp.toLp 2 (x k, z k)‖ ^ 2 =
      t ^ 2 * ‖d‖ ^ 2 + ‖z (k + 1) - z k‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst,
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.toLp_snd, hx', add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hτ]
    ring
  rw [hηp, hηp', inner_neg_left, hGin, hpn] at hB
  -- (3.21)
  have h321 := eq_3_21 X hX_cl hX_cvx P hP (x k) hxk (z k) β hβ
  rw [← hd] at h321
  -- (C) the `u` recursion
  have hudiff : g (x (k + 1)) - u (k + 1) =
      (1 - b * t) • (g (x (k + 1)) - u k) + (b * t) • (g (x (k + 1)) - G (k + 1)) := by
    rw [hu']; module
  have hbt0 : 0 ≤ b * t := by positivity
  have hbt1 : 0 ≤ 1 - b * t := by linarith
  have hC : ‖g (x (k + 1)) - u (k + 1)‖ ^ 2 =
      (1 - b * t) ^ 2 * ‖g (x (k + 1)) - u k‖ ^ 2 +
        2 * (1 - b * t) * (b * t) * ⟪g (x (k + 1)) - u k, g (x (k + 1)) - G (k + 1)⟫ +
        (b * t) ^ 2 * ‖g (x (k + 1)) - G (k + 1)‖ ^ 2 := by
    rw [hudiff, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hbt1, abs_of_nonneg hbt0]
    simp only [RCLike.conj_to_real]
    ring
  have hQ : ‖g (x (k + 1)) - u k‖ ≤ ‖g (x k) - u k‖ + Lg * (t * ‖d‖) := by
    have e : g (x (k + 1)) - u k = (g (x (k + 1)) - g (x k)) + (g (x k) - u k) := by abel
    have hl := hA2.lip_g (x (k + 1)) (x k)
    rw [hx', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ] at hl
    rw [e]
    calc _ ≤ ‖g (x (k + 1)) - g (x k)‖ + ‖g (x k) - u k‖ := norm_add_le _ _
      _ ≤ _ := by rw [hx']; linarith
  -- (D) (3.24)
  have hgn : ‖A‖ ≤ Lg := by
    have hgl : LipschitzWith ⟨Lg, hA2.Lg_nonneg⟩ g :=
      lipschitzWith_iff_norm_sub_le.mpr hA2.lip_g
    exact norm_fderiv_le_of_lipschitz ℝ hgl
  have hIF : ⟪gradF f g (x (k + 1)), d⟫ = ⟪gradient f (g (x (k + 1))), A d⟫ := by
    unfold gradF gradient
    rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply,
      fderiv_fun_comp (x (k + 1)) (hfd (g (x (k + 1)))) (hgd (x (k + 1)))]
    rfl
  have hD : ⟪gradF f g (x (k + 1)), d⟫ -
      ⟪d, (ContinuousLinearMap.adjoint A) (gradient f (u k))⟫ ≤
      Ldf * (‖g (x k) - u k‖ + Lg * (t * ‖d‖)) * (Lg * ‖d‖) := by
    rw [hIF, ContinuousLinearMap.adjoint_inner_right, ← real_inner_comm (A d) (gradient f (u k)), ← inner_sub_left]
    calc _ ≤ ‖gradient f (g (x (k + 1))) - gradient f (u k)‖ * ‖A d‖ := real_inner_le_norm _ _
      _ ≤ (Ldf * ‖g (x (k + 1)) - u k‖) * (Lg * ‖d‖) := by
          apply mul_le_mul (hA2.lip_gradf _ _) _ (norm_nonneg _)
            (mul_nonneg hA2.Ldf_nonneg (norm_nonneg _))
          calc ‖A d‖ ≤ ‖A‖ * ‖d‖ := A.le_opNorm d
            _ ≤ Lg * ‖d‖ := by gcongr
      _ ≤ _ := by
          have := hA2.Ldf_nonneg
          have := hA2.Lg_nonneg
          gcongr
  rw [inner_sub_right d ((ContinuousLinearMap.adjoint A) (gradient f (u k))) v]
  have key := l4_alg a b β c γ t LF (Leta β) Lg Ldf (f (g (x k))) (f (g (x (k + 1))))
    (Fstar f g X) (eta P β (x k) (z k)) (eta P β (x (k + 1)) (z (k + 1))) ‖d‖ ‖g (x k) - u k‖
    ‖g (x (k + 1)) - u k‖ (‖g (x (k + 1)) - u (k + 1)‖ ^ 2)
    ⟪g (x (k + 1)) - u k, g (x (k + 1)) - G (k + 1)⟫ (‖g (x (k + 1)) - G (k + 1)‖ ^ 2)
    ⟪gradF f g (x (k + 1)), d⟫ ⟪d, (ContinuousLinearMap.adjoint A) (gradient f (u k))⟫
    ⟪z k, d⟫ ⟪d, v⟫ (‖z (k + 1) - z k‖ ^ 2) ha hβ hτ hbt0 hbt1 hγ
    hcβ hcγ h316 hA2.Lg_nonneg hA2.Ldf_nonneg (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hA hB h321 hC hQ hD
  exact key

theorem solution {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (hF_bdd : BddBelow ((fun x => f (g x)) '' X))
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → EuclideanSpace ℝ (Fin m))
    (J : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsRun X P a b β τ x0 z0 u0 x z u G s J)
    (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hτ_one : ∀ k, τ k ≤ 1) (hbτ : ∀ k, b * τ k ≤ 1) :
    ∀ N : ℕ, 1 ≤ N →
      c * ∑ k ∈ Finset.range N, τ k * (‖ybar P (x k) (z k) β - x k‖ ^ 2 + ‖g (x k) - u k‖ ^ 2) ≤
        W P f g X a γ β x0 z0 u0 +
          ∑ k ∈ Finset.range N, rTerm P f g a b γ β Lf Lg Ldf Ldg τ x z u G s J k := by

  intro N _
  have hτpos : ∀ k, 0 < τ k := hrun.τ_pos
  have hxX : ∀ k, x k ∈ X := by
    intro k
    induction k with
    | zero => rw [hrun.init_x]; exact hrun.x0_mem
    | succ k ih =>
      rw [hrun.step_x k]
      exact hX_cvx.add_smul_sub_mem ih (hP _).1 ⟨(hτpos k).le, hτ_one k⟩
  set Wk : ℕ → ℝ := fun k => W P f g X a γ β (x k) (z k) (u k) with hWk
  have hstep : ∀ k, Wk (k + 1) - Wk k ≤
      -(c * (τ k * (‖ybar P (x k) (z k) β - x k‖ ^ 2 + ‖g (x k) - u k‖ ^ 2))) +
        rTerm P f g a b γ β Lf Lg Ldf Ldg τ x z u G s J k := fun k =>
    l4_step X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 a b β τ x0 z0 u0 x z u G s J hrun c γ hγ
      hcβ hcγ h316 hτ_one hbτ k (hxX k)
  have htel : ∑ k ∈ Finset.range N, (Wk (k + 1) - Wk k) = Wk N - Wk 0 :=
    Finset.sum_range_sub Wk N
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => hstep k)
  rw [htel, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hW0 : Wk 0 = W P f g X a γ β x0 z0 u0 := by
    simp only [hWk, hrun.init_x, hrun.init_z, hrun.init_u]
  have hWN : 0 ≤ Wk N := by
    simp only [hWk, W]
    have hβ := hrun.β_pos
    have hF : Fstar f g X ≤ f (g (x N)) := csInf_le hF_bdd ⟨x N, hxX N, rfl⟩
    have h321 := eq_3_21 X hX_cl hX_cvx P hP (x N) (hxX N) (z N) β hβ
    have heta : eta P β (x N) (z N) ≤ 0 := by
      unfold eta
      have : 0 ≤ β / 2 * ‖ybar P (x N) (z N) β - x N‖ ^ 2 := by positivity
      nlinarith
    have h1 : 0 ≤ a * (f (g (x N)) - Fstar f g X) :=
      mul_nonneg hrun.a_pos.le (by linarith)
    have h2 : 0 ≤ γ / 2 * ‖g (x N) - u N‖ ^ 2 := by positivity
    linarith
  rw [hW0] at hsum
  linarith
