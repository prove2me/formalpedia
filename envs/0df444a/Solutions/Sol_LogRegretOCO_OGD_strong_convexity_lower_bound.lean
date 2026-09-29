-- Prove2me | solution 1 for LogRegretOCO.OGD.strong_convexity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:28:30.176437+00:00
-- url     : https://prove2.me/submissions/9b83ea28-1c26-415c-a10d-f3f817ec350f

import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model



namespace LogRegretOCO.OGD

open Set

lemma sc_lower {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (H : ℝ)
    (f : E n → ℝ) (hf : IsHStrongConvex P H f) (x y : E n) (hx : x ∈ P) (hy : y ∈ P) :
    2 * (f x - f y) ≤ 2 * inner ℝ (gradient f x) (x - y) - H * ‖y - x‖ ^ 2 := by
  obtain ⟨hd, hd2, hH⟩ := hf
  set d := y - x with hd_def
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, x + s • d ∈ P := fun s hs => hPc.add_smul_sub_mem hx hy hs
  set g : ℝ → ℝ := fun s => f (x + s • d) with hg
  set g1 : ℝ → ℝ := fun s => fderiv ℝ f (x + s • d) d with hg1
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • d) d s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hgd : ∀ s, HasDerivAt g (g1 s) s := fun s =>
    (hd (x + s • d)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hg1d : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt g1 (fderiv ℝ (fderiv ℝ f) (x + s • d) d d) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • d))
        (fderiv ℝ (fderiv ℝ f) (x + s • d) d) s :=
      (hd2 _ (hmem s hs)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have := h1.clm_apply (hasDerivAt_const s d)
    simpa using this
  set c := H * ‖d‖ ^ 2 with hc
  -- h' := g1 - g1 0 - c s is monotone on [0,1]
  set k : ℝ → ℝ := fun s => g1 s - g1 0 - c * s with hk
  have hkd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt k (fderiv ℝ (fderiv ℝ f) (x + s • d) d d - c) s :=
    fun s hs => by
      have := ((hg1d s hs).sub_const (g1 0)).sub ((hasDerivAt_id s).const_mul c)
      exact this.congr_deriv (by ring)
  have hkmono : MonotoneOn k (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun s hs => (hkd s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      exact (hkd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs; rw [interior_Icc] at hs
      rw [(hkd s (Ioo_subset_Icc_self hs)).deriv]
      have := hH _ (hmem s (Ioo_subset_Icc_self hs)) d
      linarith
  have hk0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ k s := fun s hs => by
    have := hkmono (left_mem_Icc.2 zero_le_one) hs hs.1
    simpa [hk] using this
  -- m := g - g 0 - g1 0 s - c s²/2 is monotone on [0,1]
  set m : ℝ → ℝ := fun s => g s - g 0 - g1 0 * s - c / 2 * s ^ 2 with hm
  have hmd : ∀ s, HasDerivAt m (k s) s := fun s => by
    have := (((hgd s).sub_const (g 0)).sub ((hasDerivAt_id s).const_mul (g1 0))).sub
      ((hasDerivAt_pow 2 s).const_mul (c / 2))
    exact this.congr_deriv (by rw [hk]; norm_num; ring)
  have hmmono : MonotoneOn m (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun s _ => (hmd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hmd s).differentiableAt.differentiableWithinAt
    · intro s hs; rw [interior_Icc] at hs
      rw [(hmd s).deriv]; exact hk0 s (Ioo_subset_Icc_self hs)
  have h1 := hmmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hm, hg] at h1
  have e1 : x + (1 : ℝ) • d = y := by rw [one_smul, hd_def]; abel
  rw [e1, zero_smul, add_zero] at h1
  have e2 : g1 0 = inner ℝ (gradient f x) d := by
    rw [hg1]; simp only [zero_smul, add_zero]; rw [inner_gradient_left]
  rw [e2] at h1
  have e3 : inner ℝ (gradient f x) (x - y) = - inner ℝ (gradient f x) d := by
    rw [← inner_neg_right, hd_def, neg_sub]
  rw [e3]
  linarith [h1]


lemma proj_le {n : ℕ} {P : Set (E n)} (hPc : Convex ℝ P) {y z u : E n} (hz : IsProj P y z)
    (hu : u ∈ P) : ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  obtain ⟨hzP, hmin⟩ := hz
  have key : 0 ≤ inner ℝ (z - y) (u - z) := by
    by_contra hneg
    push_neg at hneg
    set c := inner ℝ (z - y) (u - z) with hcdef
    have hne : u - z ≠ 0 := by
      intro h; rw [h, inner_zero_right] at hcdef; linarith
    set q := ‖u - z‖ ^ 2 with hqdef
    have hq : 0 < q := by positivity
    set s := min 1 (-c / q) with hsdef
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hq)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsq : s * q ≤ -c := by
      have := min_le_right 1 (-c / q)
      rw [← hsdef] at this
      calc s * q ≤ (-c / q) * q := mul_le_mul_of_nonneg_right this hq.le
        _ = -c := by field_simp
    have hw : z + s • (u - z) ∈ P := hPc.add_smul_sub_mem hzP hu ⟨hs0.le, hs1⟩
    have h1 := hmin _ hw
    have h2 : ‖z - y‖ ^ 2 ≤ ‖z + s • (u - z) - y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : z + s • (u - z) - y = (z - y) + s • (u - z) := by abel
    rw [e, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0,
      mul_pow, ← hcdef, ← hqdef] at h2
    nlinarith
  have e : y - u = (y - z) + (z - u) := by abel
  rw [e, norm_add_sq_real]
  have : inner ℝ (y - z) (z - u) = inner ℝ (z - y) (u - z) := by
    rw [← inner_neg_neg, neg_sub, neg_sub]
  rw [this]
  nlinarith [norm_nonneg (y - z)]

theorem ogd_main {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hPb : Bornology.IsBounded P) (hPne : P.Nonempty) (H G : ℝ) (hH : 0 < H) (T : ℕ)
    (hT : 1 ≤ T) (f : ℕ → E n → ℝ)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsHStrongConvex P H (f t))
    (hG : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η (t + 1) = 1 / (H * (t : ℝ)))
    (x : ℕ → E n) (hx : IsOGDRun P η f x) (u : E n) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤ G ^ 2 / (2 * H) * (1 + Real.log T) := by
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hx.1
      · exact (hx.2 k hk).1
  set D : ℕ → ℝ := fun t => ‖x t - u‖ ^ 2 with hD
  have step : ∀ t ∈ Finset.Icc 1 T, 2 * (f t (x t) - f t u) ≤
      H * ((t : ℝ) - 1) * D t - H * t * D (t + 1) + G ^ 2 / H * (t : ℝ)⁻¹ := by
    intro t htT
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 htT).1
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have hsc1 := sc_lower P hPc H (f t) (hsc t htT) (x t) u (hxP t ht1) hu
    set g := gradient (f t) (x t) with hgdef
    have hgG : ‖g‖ ≤ G := hG t htT _ (hxP t ht1)
    set A := inner ℝ g (x t - u) with hA
    set e := η (t + 1) with he
    have he' : e = 1 / (H * t) := hη t ht1
    have hepos : 0 < e := by rw [he']; positivity
    have hproj := proj_le hPc (hx.2 t ht1) hu
    have ex : x t - e • g - u = (x t - u) - e • g := by abel
    rw [ex, norm_sub_sq_real (x t - u) (e • g), inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hepos, mul_pow, real_inner_comm, ← hA] at hproj
    have hg2 : ‖g‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgG 2
    have hnr : ‖u - x t‖ = ‖x t - u‖ := norm_sub_rev _ _
    rw [hnr] at hsc1
    -- multiply the projection inequality by H t
    have hHt : 0 < H * t := by positivity
    have heHt : e * (H * t) = 1 := by rw [he']; field_simp
    have hmul := mul_le_mul_of_nonneg_left hproj hHt.le
    have hDt : D t = ‖x t - u‖ ^ 2 := rfl
    have hDt1 : D (t + 1) = ‖x (t + 1) - u‖ ^ 2 := rfl
    have hG2 : G ^ 2 / H * (t : ℝ)⁻¹ = e * G ^ 2 := by rw [he']; field_simp
    rw [hDt, hDt1, hG2]
    have k1 : H * t * (e ^ 2 * ‖g‖ ^ 2) = e * ‖g‖ ^ 2 := by
      calc H * t * (e ^ 2 * ‖g‖ ^ 2) = (e * (H * t)) * (e * ‖g‖ ^ 2) := by ring
        _ = e * ‖g‖ ^ 2 := by rw [heHt, one_mul]
    have k2 : H * t * (2 * e * A) = 2 * A := by
      calc H * t * (2 * e * A) = (e * (H * t)) * (2 * A) := by ring
        _ = 2 * A := by rw [heHt, one_mul]
    have k3 : e * ‖g‖ ^ 2 ≤ e * G ^ 2 := mul_le_mul_of_nonneg_left hg2 hepos.le
    nlinarith
  have hind : ∀ T' ≤ T, 2 * ∑ t ∈ Finset.Icc 1 T', (f t (x t) - f t u) + H * T' * D (T' + 1) ≤
      G ^ 2 / H * ∑ t ∈ Finset.Icc 1 T', (t : ℝ)⁻¹ := by
    intro T' hT'
    induction T' with
    | zero => simp
    | succ k ih =>
      have ih := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have hs := step (k + 1) (Finset.mem_Icc.2 ⟨by omega, hT'⟩)
      push_cast at hs ⊢
      nlinarith
  have h1 := hind T le_rfl
  have hDnn : 0 ≤ H * T * D (T + 1) := by positivity
  have hharm : ∑ t ∈ Finset.Icc 1 T, (t : ℝ)⁻¹ ≤ 1 + Real.log T := by
    have := harmonic_le_one_add_log T
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have h2 : G ^ 2 / H * ∑ t ∈ Finset.Icc 1 T, (t : ℝ)⁻¹ ≤ G ^ 2 / H * (1 + Real.log T) :=
    mul_le_mul_of_nonneg_left hharm (by positivity)
  have e : G ^ 2 / (2 * H) * (1 + Real.log T) = (G ^ 2 / H * (1 + Real.log T)) / 2 := by ring
  rw [e]
  linarith

end LogRegretOCO.OGD

open LogRegretOCO.OGD

theorem solution {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (H : ℝ)
    (f : E n → ℝ) (hf : IsHStrongConvex P H f) (x y : E n) (hx : x ∈ P) (hy : y ∈ P) :
    2 * (f x - f y) ≤ 2 * inner ℝ (gradient f x) (x - y) - H * ‖y - x‖ ^ 2 := by
  exact sc_lower P hPc H f hf x y hx hy
