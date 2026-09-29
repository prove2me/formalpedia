-- Prove2me | solution 1 for LewisTorczon.BoundPS.corollary_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:06:11.353577+00:00
-- url     : https://prove2.me/submissions/0f5315cb-323b-4308-895d-5a57138f0481

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

lemma aux_ct44_coe (a b : EReal) (u t : ℝ) (ha : a ≤ (u : EReal)) (hb : (u : EReal) ≤ b) :
    ((clampCoord a b t : ℝ) : EReal) = max a (min b (t : EReal)) := by
  unfold clampCoord
  apply EReal.coe_toReal
  · apply ne_top_of_le_ne_top (b := ((max u t : ℝ) : EReal)) (EReal.coe_ne_top _)
    refine max_le (ha.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))) ?_
    exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  · apply ne_bot_of_le_ne_bot (b := ((min u t : ℝ) : EReal)) (EReal.coe_ne_bot _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_min ((EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans hb) ?_
    exact EReal.coe_le_coe_iff.mpr (min_le_right _ _)

lemma aux_ct44_pos (a b : EReal) (u t : ℝ) (ha : a ≤ (u : EReal)) (hb : (u : EReal) ≤ b)
    (h : u < clampCoord a b t) :
    clampCoord a b t ≤ t ∧ ((clampCoord a b t : ℝ) : EReal) ≤ b := by
  have hc := aux_ct44_coe a b u t ha hb
  constructor
  · by_contra hlt
    push_neg at hlt
    have h1 : ((clampCoord a b t : ℝ) : EReal) ≤ max (u : EReal) t := by
      rw [hc]; exact max_le_max ha (min_le_right _ _)
    rcases le_max_iff.mp h1 with h2 | h2
    · exact absurd (EReal.coe_le_coe_iff.mp h2) (not_le.mpr h)
    · exact absurd (EReal.coe_le_coe_iff.mp h2) (not_le.mpr hlt)
  · rw [hc]; exact max_le (ha.trans hb) (min_le_left _ _)

lemma aux_ct44_neg (a b : EReal) (u t : ℝ) (ha : a ≤ (u : EReal)) (hb : (u : EReal) ≤ b)
    (h : clampCoord a b t < u) :
    t ≤ clampCoord a b t ∧ a ≤ ((clampCoord a b t : ℝ) : EReal) := by
  have hc := aux_ct44_coe a b u t ha hb
  constructor
  · by_contra hlt
    push_neg at hlt
    have h1 : min (u : EReal) t ≤ ((clampCoord a b t : ℝ) : EReal) := by
      rw [hc]; exact le_trans (min_le_min_right _ hb) (le_max_right _ _)
    rcases min_le_iff.mp h1 with h2 | h2
    · exact absurd (EReal.coe_le_coe_iff.mp h2) (not_le.mpr h)
    · exact absurd (EReal.coe_le_coe_iff.mp h2) (not_le.mpr hlt)
  · rw [hc]; exact le_max_left _ _

lemma aux_ct44_projQ_apply {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    projQ lo hi f x j = clampCoord (lo j) (hi j) (x j - gradient f x j) - x j := by
  simp [projQ, boxProj]

lemma aux_ct44_coord {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi) (j : Fin n) (α : ℝ)
    (hpos : 0 < α * projQ lo hi f x j) (hle : |α| ≤ |projQ lo hi f x j|) :
    x + EuclideanSpace.single j α ∈ box lo hi ∧
      α * gradient f x j ≤ -(α * projQ lo hi f x j) := by
  rw [aux_ct44_projQ_apply] at hpos hle ⊢
  set t := x j - gradient f x j with ht
  set p := clampCoord (lo j) (hi j) t with hp
  obtain ⟨ha, hb⟩ := hx j
  have hcoord : ∀ β : ℝ, lo j ≤ ((x j + β : ℝ) : EReal) → ((x j + β : ℝ) : EReal) ≤ hi j →
      x + EuclideanSpace.single j β ∈ box lo hi := by
    intro β h1 h2 i
    by_cases hij : i = j
    · subst hij; simpa using And.intro h1 h2
    · simpa [hij] using hx i
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨hα, hq⟩ | ⟨hα, hq⟩
  · have hup : x j < p := by linarith
    obtain ⟨h1, h2⟩ := aux_ct44_pos (lo j) (hi j) (x j) t ha hb hup
    rw [abs_of_pos hα, abs_of_pos hq] at hle
    refine ⟨hcoord α ?_ ?_, ?_⟩
    · exact ha.trans (EReal.coe_le_coe_iff.mpr (by linarith))
    · exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans h2
    · have : gradient f x j ≤ -(p - x j) := by linarith
      nlinarith
  · have hup : p < x j := by linarith
    obtain ⟨h1, h2⟩ := aux_ct44_neg (lo j) (hi j) (x j) t ha hb hup
    rw [abs_of_neg hα, abs_of_neg hq] at hle
    refine ⟨hcoord α ?_ ?_, ?_⟩
    · exact h2.trans (EReal.coe_le_coe_iff.mpr (by linarith))
    · exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans hb
    · have : -(p - x j) ≤ gradient f x j := by linarith
      nlinarith

lemma aux_ct44_exists_coord {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hv : ε ≤ ‖v‖) : ∃ j, ε / n ≤ |v j| := by
  by_contra h
  push_neg at h
  have h1 : ‖v‖ ^ 2 ≤ (∑ j, ‖v j‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  have h2 : ‖v‖ ≤ ∑ j, ‖v j‖ := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg (v j))
    nlinarith [norm_nonneg v]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp at h2
    rw [h2, norm_zero] at hv
    linarith
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h3 : ∑ j, ‖v j‖ < ∑ _j : Fin n, ε / n :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => by
        rw [Real.norm_eq_abs]; exact h j)
    have h4 : ∑ _j : Fin n, ε / n = ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    linarith

lemma aux_ct44_descent {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (c η : ℝ) (_hc : 0 < c)
    (hη : ∀ y ∈ K, ∀ z ∈ K, dist y z < η → dist (fderiv ℝ f y) (fderiv ℝ f z) < c / 2)
    (x : EuclideanSpace ℝ (Fin n)) (hxbox : x ∈ box lo hi) (r : ℝ)
    (hball : Metric.closedBall x r ⊆ K) (j : Fin n) (hq : c ≤ |projQ lo hi f x j|)
    (α : ℝ) (hpos : 0 < α * projQ lo hi f x j) (hαc : |α| ≤ c) (hαr : |α| ≤ r)
    (hαη : |α| < η) :
    x + EuclideanSpace.single j α ∈ box lo hi ∧ f (x + EuclideanSpace.single j α) < f x := by
  obtain ⟨hbox, hgrad⟩ := aux_ct44_coord lo hi f x hxbox j α hpos (hαc.trans hq)
  refine ⟨hbox, ?_⟩
  set y := x + EuclideanSpace.single j α with hy
  have hxK : x ∈ K := hball (Metric.mem_closedBall_self ((abs_nonneg α).trans hαr))
  have hyx : y - x = EuclideanSpace.single j α := by simp [y]
  have hnorm : ‖EuclideanSpace.single j α‖ = |α| := by simp
  have hyb : y ∈ Metric.closedBall x |α| := by
    rw [Metric.mem_closedBall, dist_eq_norm, hyx, hnorm]
  have hseg : segment ℝ x y ⊆ Metric.closedBall x |α| :=
    (convex_closedBall x |α|).segment_subset (Metric.mem_closedBall_self (abs_nonneg _)) hyb
  have hsegK : ∀ z ∈ segment ℝ x y, z ∈ K := fun z hz =>
    hball (Metric.closedBall_subset_closedBall hαr (hseg hz))
  have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z (hKU (hsegK z hz))).differentiableAt
      (hU.mem_nhds (hKU (hsegK z hz)))
  have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ c / 2 := by
    intro z hz
    rw [← dist_eq_norm]
    exact (hη z (hsegK z hz) x hxK
      (lt_of_le_of_lt (Metric.mem_closedBall.mp (hseg hz)) hαη)).le
  have hmvt := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hfd : fderiv ℝ f x (EuclideanSpace.single j α) = α * gradient f x j := by
    rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp
  rw [hyx, hfd, hnorm] at hmvt
  have h1 := (abs_le.mp hmvt).2
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hpos
  have hαpos : 0 < |α| := abs_pos.mpr hα0
  have hαq : α * projQ lo hi f x j = |α| * |projQ lo hi f x j| := by
    rw [← abs_mul, abs_of_pos hpos]
  have h2 : |α| * c ≤ |α| * |projQ lo hi f x j| := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  nlinarith

lemma aux_ct44_stepOf_col {n m : ℕ} (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hdiag : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ ((R.M k).transpose j) =
      EuclideanSpace.single j (Δ * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j) := by
  ext i
  have h1 : P.B.mulVec (fun r => (((R.M k).transpose j r : ℤ) : ℝ)) i =
      (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) i j := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp only [stepOf, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, h1]
  by_cases h : i = j
  · subst h; simp
  · rw [hdiag h]; simp [h]

lemma aux_ct44_stepOf_neg {n : ℕ} (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    stepOf P Δ (-c) = -stepOf P Δ c := by
  ext i
  simp [stepOf, Matrix.mulVec, dotProduct]

lemma aux_ct44_single_neg {n : ℕ} (j : Fin n) (a : ℝ) :
    -(EuclideanSpace.single j a) = EuclideanSpace.single j (-a) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma aux_ct44_diag_ne {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ) (hM : M ∈ P.𝕄)
    (hdiag : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (j : Fin n) :
    (P.B * M.map (fun a : ℤ => (a : ℝ))) j j ≠ 0 := by
  intro h0
  have hdet : (P.B * M.map (fun a : ℤ => (a : ℝ))).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero P.B_det_ne_zero ?_
    rw [← Int.cast_det]
    exact_mod_cast P.𝕄_det_ne_zero M hM
  apply hdet
  rw [← hdiag.diagonal_diag, Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ j) h0

lemma aux_ct44_Dbound {n : ℕ} (P : GPSParams n) : ∃ D : ℝ, 0 < D ∧
    ∀ M ∈ P.𝕄, ∀ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j| ≤ D := by
  refine ⟨1 + ∑ M ∈ P.𝕄, ∑ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j|, by positivity, ?_⟩
  intro M hM j
  have h1 : |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j| ≤
      ∑ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j| :=
    Finset.single_le_sum (f := fun j => |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j| ≤
      ∑ M ∈ P.𝕄, ∑ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j| :=
    Finset.single_le_sum (f := fun M => ∑ j, |(P.B * M.map (fun a : ℤ => (a : ℝ))) j j|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hM
  linarith

lemma aux_ct44_mem_level {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m} (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by
  intro k
  induction k with
  | zero => exact ⟨hR.x_zero_mem, le_rfl⟩
  | succ k ih =>
    rw [hR.x_succ k]
    split_ifs with h
    · exact ⟨hR.step_feasible k, h.le.trans ih.2⟩
    · exact ih

lemma aux_ct44_τ_pos {n : ℕ} (P : GPSParams n) : (1 : ℝ) < (P.τ : ℝ) := by
  exact_mod_cast P.one_lt_τ

lemma aux_ct44_Δ_pos {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m} (hR : IsGPSRun P lo hi f R) :
    ∀ k, 0 < R.Δ k := by
  intro k
  have hτ : (0 : ℝ) < (P.τ : ℝ) := by linarith [aux_ct44_τ_pos P]
  induction k with
  | zero => exact hR.Δ_zero_pos
  | succ k ih =>
    by_cases h : f (R.x k + R.s k) < f (R.x k)
    · obtain ⟨w, _, hw⟩ := hR.Δ_succ_success k h
      rw [hw]; exact mul_pos (zpow_pos hτ w) ih
    · rw [hR.Δ_succ_failure k h]; exact mul_pos (zpow_pos hτ _) ih

lemma aux_ct44_Δ_succ_ge {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m} (hR : IsGPSRun P lo hi f R) (k : ℕ)
    (h : f (R.x k + R.s k) < f (R.x k)) : R.Δ k ≤ R.Δ (k + 1) := by
  obtain ⟨w, hwW, hw⟩ := hR.Δ_succ_success k h
  rw [hw]
  exact le_mul_of_one_le_left (aux_ct44_Δ_pos hR k).le
    (one_le_zpow₀ (aux_ct44_τ_pos P).le (P.W_nonneg w hwW))

lemma aux_ct44_Δ_succ_theta {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m} (hR : IsGPSRun P lo hi f R) (k : ℕ) :
    (P.τ : ℝ) ^ P.w₀ * R.Δ k ≤ R.Δ (k + 1) := by
  by_cases h : f (R.x k + R.s k) < f (R.x k)
  · refine le_trans ?_ (aux_ct44_Δ_succ_ge hR k h)
    exact mul_le_of_le_one_left (aux_ct44_Δ_pos hR k).le
      (zpow_le_one_of_nonpos₀ (aux_ct44_τ_pos P).le P.w₀_neg.le)
  · rw [hR.Δ_succ_failure k h]

lemma aux_ct44_finite_lb (Δ : ℕ → ℝ) (h : ∀ k, 0 < Δ k) :
    ∀ N, ∃ μ > 0, ∀ k ≤ N, μ ≤ Δ k := by
  intro N
  induction N with
  | zero => exact ⟨Δ 0, h 0, fun k hk => by rw [Nat.le_zero.mp hk]⟩
  | succ N ih =>
    obtain ⟨μ, hμ, hμk⟩ := ih
    refine ⟨min μ (Δ (N + 1)), lt_min hμ (h _), fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (N + 1) with h1 | h1
    · exact (min_le_left _ _).trans (hμk k (Nat.lt_succ_iff.mp h1))
    · rw [le_antisymm hk h1]; exact min_le_right _ _

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hliminf : ¬ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ‖projQ lo hi f (R.x k)‖ < ε) :
    ∃ Δstar : ℝ, 0 < Δstar ∧ ∀ k, Δstar < R.Δ k := by
  push_neg at hliminf
  obtain ⟨ε, hε, hfreq⟩ := hliminf
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hfreq
  have hqk : ∀ k ≥ K0, ε ≤ ‖projQ lo hi f (R.x k)‖ := fun k hk => hK0 k hk
  obtain ⟨j0, -⟩ := aux_ct44_exists_coord _ ε hε (hqk K0 le_rfl)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Fin.pos j0
  have hc : 0 < ε / n := div_pos hε hnpos
  have hLU : levelSet lo hi f (R.x 0) ⊆ U := fun x hx => hΩU hx.1
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hcpt.exists_cthickening_subset_open hU hLU
  have hKc : IsCompact (Metric.cthickening δ₀ (levelSet lo hi f (R.x 0))) := hcpt.cthickening
  have hcont : ContinuousOn (fderiv ℝ f) (Metric.cthickening δ₀ (levelSet lo hi f (R.x 0))) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hδ₀U
  have huc := hKc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηK⟩ := huc (ε / n / 2) (by positivity)
  obtain ⟨D, hD, hDb⟩ := aux_ct44_Dbound P
  have hδ : 0 < min (min (ε / n) δ₀) η / D := div_pos (lt_min (lt_min hc hδ₀) hη) hD
  have hΔpos := aux_ct44_Δ_pos hR
  have hmem := aux_ct44_mem_level hR
  have hsucc : ∀ k ≥ K0, R.Δ k < min (min (ε / n) δ₀) η / D →
      f (R.x k + R.s k) < f (R.x k) := by
    intro k hk hΔk
    obtain ⟨j, hj⟩ := aux_ct44_exists_coord _ ε hε (hqk k hk)
    have hd0 : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j ≠ 0 :=
      aux_ct44_diag_ne P (R.M k) (hR.M_mem k) (hR.diag k) j
    have hdD : |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| ≤ D :=
      hDb (R.M k) (hR.M_mem k) j
    have hq0 : projQ lo hi f (R.x k) j ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hj; linarith
    have habs : |R.Δ k * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| <
        min (min (ε / n) δ₀) η := by
      rw [abs_mul, abs_of_pos (hΔpos k)]
      calc R.Δ k * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j|
          ≤ R.Δ k * D := mul_le_mul_of_nonneg_left hdD (hΔpos k).le
        _ < min (min (ε / n) δ₀) η / D * D := mul_lt_mul_of_pos_right hΔk hD
        _ = min (min (ε / n) δ₀) η := by field_simp
    have key : ∀ α : ℝ, |α| = |R.Δ k * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| →
        0 < α * projQ lo hi f (R.x k) j →
        R.x k + EuclideanSpace.single j α ∈ box lo hi ∧
          f (R.x k + EuclideanSpace.single j α) < f (R.x k) := by
      intro α hα hpos
      rw [← hα] at habs
      exact aux_ct44_descent lo hi f U hU hf _ hδ₀U (ε / n) η hc hηK (R.x k) (hmem k).1 δ₀
        (Metric.closedBall_subset_cthickening (hmem k) δ₀) j hj α hpos
        (habs.le.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (habs.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (habs.trans_le (min_le_right _ _))
    apply hR.simple_decrease k
    have hcol := aux_ct44_stepOf_col P R k (hR.diag k) (R.Δ k) j
    by_cases hs : 0 < (R.Δ k * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j) *
        projQ lo hi f (R.x k) j
    · refine ⟨(R.M k).transpose j, ⟨j, Or.inl rfl⟩, ?_⟩
      rw [hcol]
      exact key _ rfl hs
    · refine ⟨-((R.M k).transpose j), ⟨j, Or.inr rfl⟩, ?_⟩
      rw [aux_ct44_stepOf_neg, hcol, aux_ct44_single_neg]
      refine key _ (abs_neg _) ?_
      have hne : (R.Δ k * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j) *
          projQ lo hi f (R.x k) j ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hΔpos k).ne' hd0) hq0
      have hlt := lt_of_le_of_ne (not_lt.mp hs) hne
      rw [neg_mul]
      linarith
  have hθpos : (0 : ℝ) < (P.τ : ℝ) ^ P.w₀ := zpow_pos (by linarith [aux_ct44_τ_pos P]) _
  have hlb : ∀ k ≥ K0, min (R.Δ K0) ((P.τ : ℝ) ^ P.w₀ * (min (min (ε / n) δ₀) η / D)) ≤
      R.Δ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      by_cases hlt : R.Δ k < min (min (ε / n) δ₀) η / D
      · exact ih.trans (aux_ct44_Δ_succ_ge hR k (hsucc k hk hlt))
      · push_neg at hlt
        exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left hlt hθpos.le).trans (aux_ct44_Δ_succ_theta hR k))
  obtain ⟨μ, hμ, hμk⟩ := aux_ct44_finite_lb R.Δ hΔpos K0
  have hpos' : 0 < min μ (min (R.Δ K0) ((P.τ : ℝ) ^ P.w₀ * (min (min (ε / n) δ₀) η / D))) :=
    lt_min hμ (lt_min (hΔpos K0) (mul_pos hθpos hδ))
  refine ⟨min μ (min (R.Δ K0) ((P.τ : ℝ) ^ P.w₀ * (min (min (ε / n) δ₀) η / D))) / 2,
    by positivity, fun k => ?_⟩
  have hle : min μ (min (R.Δ K0) ((P.τ : ℝ) ^ P.w₀ * (min (min (ε / n) δ₀) η / D))) ≤
      R.Δ k := by
    rcases le_or_gt k K0 with h | h
    · exact (min_le_left _ _).trans (hμk k h)
    · exact (min_le_right _ _).trans (hlb k h.le)
  linarith
