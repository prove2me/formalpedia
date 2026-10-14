-- Prove2me | solution 1 for ModernOnlineLearning.OMD.theorem_6_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:06:34.507045+00:00
-- url     : https://prove2.me/submissions/089e07f3-62a3-4cac-840f-058e2f306617

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace RRAux_ModernOnlineLearning_OMD_theorem_6_11

open ModernOnlineLearning.OMD BeckTeboulleMD.EMDA

theorem right_deriv_nonneg (k : ℝ → ℝ) (k' : ℝ) (hk : HasDerivAt k k' 0)
    (h : ∀ s ∈ Set.Ioo (0:ℝ) 1, k 0 ≤ k s) : 0 ≤ k' := by
  have ht := hk.tendsto_slope_zero_right
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
  have := h s hs
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.1.le) (by linarith)

theorem curve_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y v : E) :
    HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
  have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  simpa using this

theorem first_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V) (ψ : E → ℝ) (g : E →L[ℝ] ℝ) (η : ℝ) (x y u : E)
    (hy : y ∈ V) (hu : u ∈ V) (hdy : DifferentiableAt ℝ ψ y)
    (hmin : ∀ z ∈ V, η * g y + bregman ψ y x ≤ η * g z + bregman ψ z x) :
    0 ≤ η * g (u - y) + fderiv ℝ ψ y (u - y) - fderiv ℝ ψ x (u - y) := by
  set v := u - y
  set c : ℝ → E := fun s => y + s • v with hc
  have hcd : HasDerivAt c v 0 := curve_deriv y v
  have hc0 : c 0 = y := by simp [hc]
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) (c 0) := by rw [hc0]; exact hdy.hasFDerivAt
  have d1 : HasDerivAt (fun s => η * g (c s)) (η * g v) 0 :=
    (g.hasFDerivAt.comp_hasDerivAt 0 hcd).const_mul η
  have d2 : HasDerivAt (fun s => ψ (c s)) (fderiv ℝ ψ y v) 0 := hψd.comp_hasDerivAt 0 hcd
  have d3 : HasDerivAt (fun s => fderiv ℝ ψ x (c s - x)) (fderiv ℝ ψ x v) 0 :=
    (fderiv ℝ ψ x).hasFDerivAt.comp_hasDerivAt 0 (hcd.sub_const x)
  have hk := d1.add ((d2.sub_const (ψ x)).sub d3)
  have := right_deriv_nonneg _ _ hk (by
    intro s hs
    have hm := hmin (c s) (hV.add_smul_sub_mem hy hu ⟨hs.1.le, hs.2.le⟩)
    simp only [bregman] at hm
    simp only [Pi.add_apply, Pi.sub_apply, hc0]
    linarith)
  linarith

theorem sc_breg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hsc : StrongConvexOn V lam ψ) (x y : E)
    (hx : x ∈ V) (hy : y ∈ V) (hdx : DifferentiableAt ℝ ψ x) :
    lam / 2 * ‖y - x‖ ^ 2 ≤ bregman ψ y x := by
  set K := lam / 2 * ‖x - y‖ ^ 2 with hK
  set v := y - x
  set c : ℝ → E := fun s => x + s • v with hc
  have hcd : HasDerivAt c v 0 := curve_deriv x v
  have hc0 : c 0 = x := by simp [hc]
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x) (c 0) := by rw [hc0]; exact hdx.hasFDerivAt
  have d2 : HasDerivAt (fun s => ψ (c s)) (fderiv ℝ ψ x v) 0 := hψd.comp_hasDerivAt 0 hcd
  have h1 := ((hasDerivAt_id (0:ℝ)).mul_const (ψ y - ψ x - K)).const_add (ψ x)
  have h2 := (hasDerivAt_pow 2 (0:ℝ)).mul_const K
  have hk := (h1.add h2).sub d2
  have := right_deriv_nonneg _ _ hk (by
    intro s hs
    have h := hsc.2 hx hy (show (0:ℝ) ≤ 1 - s by linarith [hs.2]) hs.1.le
      (show 1 - s + s = 1 by ring)
    have e : (1 - s) • x + s • y = c s := by simp only [hc, v]; module
    rw [e] at h
    try simp only [smul_eq_mul] at h
    simp only [Pi.add_apply, Pi.sub_apply, hc0, id]
    rw [← hK] at h
    nlinarith)
  simp at this
  simp only [bregman]
  rw [norm_sub_rev] at hK
  linarith

theorem quad_bound (A G r η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam)
    (h : A ≤ G * r - (1 / η) * (lam / 2 * r ^ 2)) :
    A ≤ η / (2 * lam) * G ^ 2 := by
  have : G * r - (1 / η) * (lam / 2 * r ^ 2) ≤ η / (2 * lam) * G ^ 2 := by
    have e : η / (2 * lam) * G ^ 2 - (G * r - (1 / η) * (lam / 2 * r ^ 2)) =
        (η * G - lam * r) ^ 2 / (2 * η * lam) := by field_simp; ring
    have : 0 ≤ (η * G - lam * r) ^ 2 / (2 * η * lam) := by positivity
    linarith
  linarith

theorem sum_bound (a η : ℕ → ℝ) (D2 : ℝ) :
    ∀ T : ℕ, 1 ≤ T → (∀ t ∈ Finset.Icc 1 T, a t ≤ D2) → (∀ t ∈ Finset.Icc 1 T, 0 < η t) →
    (∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t) →
    ∑ t ∈ Finset.Icc 1 T, (a t - a (t + 1)) / η t ≤ D2 / η T - a (T + 1) / η T := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro ha hη _
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have := ha 1 (by simp)
    have hp := hη 1 (by simp)
    have : a 1 / η 1 ≤ D2 / η 1 := div_le_div_of_nonneg_right this hp.le
    rw [sub_div]
    linarith
  | succ n hn ih =>
    intro ha hη hm
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (fun t ht => ha t (by simp at ht ⊢; omega))
      (fun t ht => hη t (by simp at ht ⊢; omega))
      (fun t ht => hm t (by simp at ht ⊢; omega))
    have h1 : 0 < η n := hη n (by simp; omega)
    have h2 : 0 < η (n + 1) := hη (n + 1) (by simp)
    have h3 : η (n + 1) ≤ η n := hm n (by simp; omega)
    have h4 : a (n + 1) ≤ D2 := ha (n + 1) (by simp)
    have key : (D2 - a (n + 1)) / η n ≤ (D2 - a (n + 1)) / η (n + 1) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    have e1 : D2 / η n - a (n + 1) / η n = (D2 - a (n + 1)) / η n := by ring
    have e2 : (a (n + 1) - a (n + 1 + 1)) / η (n + 1) + (D2 - a (n + 1)) / η (n + 1)
        = D2 / η (n + 1) - a (n + 1 + 1) / η (n + 1) := by ring
    linarith

end RRAux_ModernOnlineLearning_OMD_theorem_6_11

open ModernOnlineLearning.OMD in
-- Orabona, Theorem 6.11 (decreasing steps)
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (T : ℕ) (hT : 1 ≤ T) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hrun : IsOMDRun T X V ψ η ℓ x g)
    (hmono : ∀ t : ℕ, 1 ≤ t → t < T → η (t + 1) ≤ η t) :
    ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        bregmanMax T hT ψ u x / η T +
          (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2 := by
  intro u hu
  obtain ⟨hlam, -, -, -, -, -, -, hVconv, -, -, hsc⟩ := hsetting
  obtain ⟨-, hstep⟩ := hrun
  set a : ℕ → ℝ := fun t => if t ≤ T then BeckTeboulleMD.EMDA.bregman ψ u (x t) else 0 with ha
  have hround : ∀ t ∈ Finset.Icc 1 T, ℓ t (x t) - ℓ t u ≤
      η t / (2 * lam) * ‖g t‖ ^ 2 + (a t - a (t + 1)) / η t := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    obtain ⟨⟨hxtV, -⟩, -, hsub, ⟨hηt, -, hdt, hyV, hargmin⟩⟩ := hstep t ht
    set y := x (t + 1) with hy
    have h1 : ℓ t (x t) - ℓ t u ≤ g t (x t - u) := by
      have := hsub u hu
      have e : g t (u - x t) = - g t (x t - u) := by rw [← map_neg, neg_sub]
      linarith
    have hargmin' : ∀ z ∈ V, η t * g t y + BeckTeboulleMD.EMDA.bregman ψ y (x t) ≤
        η t * g t z + BeckTeboulleMD.EMDA.bregman ψ z (x t) := by
      intro z hz
      have := mul_le_mul_of_nonneg_left (hargmin z hz) hηt.le
      have e1 : η t * (g t y + 1 / η t * BeckTeboulleMD.EMDA.bregman ψ y (x t)) =
          η t * g t y + BeckTeboulleMD.EMDA.bregman ψ y (x t) := by field_simp
      have e2 : η t * (g t z + 1 / η t * BeckTeboulleMD.EMDA.bregman ψ z (x t)) =
          η t * g t z + BeckTeboulleMD.EMDA.bregman ψ z (x t) := by field_simp
      linarith
    -- key: η g(y - u) ≤ (a t - a (t+1)) - B(y, x t)
    have hkey : η t * g t (y - u) ≤ (a t - a (t + 1)) -
        BeckTeboulleMD.EMDA.bregman ψ y (x t) := by
      have hat : a t = BeckTeboulleMD.EMDA.bregman ψ u (x t) := by
        simp only [ha, if_pos ht'.2]
      rcases lt_or_eq_of_le ht'.2 with hlt | heq
      · -- interior round: use first-order optimality at y
        have hat1 : a (t + 1) = BeckTeboulleMD.EMDA.bregman ψ u y := by
          simp only [ha, if_pos (show t + 1 ≤ T by omega)]; rfl
        have hdy : DifferentiableAt ℝ ψ y := (hstep (t + 1) (by simp; omega)).2.2.2.2.2.1
        have hfo := RRAux_ModernOnlineLearning_OMD_theorem_6_11.first_order V hVconv ψ (g t)
          (η t) (x t) y u hyV hu hdy hargmin'
        have e3 : BeckTeboulleMD.EMDA.bregman ψ u (x t) - BeckTeboulleMD.EMDA.bregman ψ u y -
            BeckTeboulleMD.EMDA.bregman ψ y (x t) =
            fderiv ℝ ψ y (u - y) - fderiv ℝ ψ (x t) (u - y) := by
          simp only [BeckTeboulleMD.EMDA.bregman]
          have : fderiv ℝ ψ (x t) (u - x t) - fderiv ℝ ψ (x t) (y - x t) =
              fderiv ℝ ψ (x t) (u - y) := by
            rw [← map_sub]; congr 1; abel
          linarith
        have e4 : g t (y - u) = - g t (u - y) := by rw [← map_neg, neg_sub]
        rw [hat, hat1, e4]
        linarith
      · have hat1 : a (t + 1) = 0 := by
          simp only [ha, if_neg (show ¬ (t + 1 ≤ T) by omega)]
        have := hargmin' u hu
        have e4 : g t (y - u) = g t y - g t u := map_sub _ _ _
        rw [hat, hat1, e4]
        linarith
    have hB := RRAux_ModernOnlineLearning_OMD_theorem_6_11.sc_breg V ψ lam hsc (x t) y hxtV hyV hdt
    have hdiv := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 1 / η t)
    have e5 : 1 / η t * (η t * g t (y - u)) = g t (y - u) := by field_simp
    rw [e5] at hdiv
    have hB' := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 1 / η t)
    have hgl : g t (x t - y) ≤ ‖g t‖ * ‖y - x t‖ := by
      have := (g t).le_opNorm (x t - y)
      rw [Real.norm_eq_abs, norm_sub_rev] at this
      exact le_trans (le_abs_self _) this
    have hsplit : g t (x t - u) = g t (x t - y) + g t (y - u) := by
      rw [← map_add]; congr 1; abel
    have hq := RRAux_ModernOnlineLearning_OMD_theorem_6_11.quad_bound
      (g t (x t - u) - (a t - a (t + 1)) / η t) ‖g t‖ ‖y - x t‖ (η t) lam hηt hlam (by
        have e6 : (a t - a (t + 1)) / η t = 1 / η t * (a t - a (t + 1)) := by ring
        rw [e6]
        nlinarith)
    linarith
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib] at hsum
  have hηpos : ∀ t ∈ Finset.Icc 1 T, 0 < η t := fun t ht => (hstep t ht).2.2.2.1
  have hsb := RRAux_ModernOnlineLearning_OMD_theorem_6_11.sum_bound a η (bregmanMax T hT ψ u x) T hT
    (fun t ht => by
      simp only [ha, if_pos (Finset.mem_Icc.mp ht).2]
      exact Finset.le_sup' (fun t => BeckTeboulleMD.EMDA.bregman ψ u (x t)) ht)
    hηpos
    (fun t ht => hmono t (Finset.mem_Icc.mp ht).1 (by have := (Finset.mem_Icc.mp ht).2; omega))
  have haT1 : a (T + 1) = 0 := by simp only [ha, if_neg (show ¬ (T + 1 ≤ T) by omega)]
  rw [haT1, zero_div, sub_zero] at hsb
  have he : ∑ t ∈ Finset.Icc 1 T, η t / (2 * lam) * ‖g t‖ ^ 2 =
      (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
  linarith

#print axioms solution
