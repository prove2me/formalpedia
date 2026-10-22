-- Prove2me | solution 1 for NesterovRCD.Sublinear.expected_decrease
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:42:29.774512+00:00
-- url     : https://prove2.me/submissions/5f39c007-0def-48c8-ac28-1308c8dcc487

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic
set_option autoImplicit false

namespace ZZC3

open NesterovRCD.Sublinear

lemma coord_descent {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L) (i : Fin n)
    (x : Blocks E) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by
  obtain ⟨hdiff, hpos, hlip⟩ := hL
  set s : Blocks E := Pi.single i h with hs
  set ψ : ℝ → ℝ := fun t => f (x + t • s) - t * partialGrad f x i h - L i / 2 * t ^ 2 * ‖h‖ ^ 2 with hψ
  have hline : ∀ t : ℝ, HasDerivAt (fun r : ℝ => f (x + r • s)) (partialGrad f (x + t • s) i h) t := by
    intro t
    have h1 : HasFDerivAt f (fderiv ℝ f (x + t • s)) (x + t • s) := (hdiff _).hasFDerivAt
    have h2 : HasDerivAt (fun r : ℝ => x + r • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add x
    have := h1.comp_hasDerivAt t h2
    have e : partialGrad f (x + t • s) i h = fderiv ℝ f (x + t • s) s := by
      simp [partialGrad, hs]
    rw [e]
    exact this
  have hψd : ∀ t : ℝ, HasDerivAt ψ
      (partialGrad f (x + t • s) i h - partialGrad f x i h - L i * t * ‖h‖ ^ 2) t := by
    intro t
    have h1 := hline t
    have h2 : HasDerivAt (fun r : ℝ => r * partialGrad f x i h) (partialGrad f x i h) t := by
      simpa using (hasDerivAt_id t).mul_const (partialGrad f x i h)
    have h3 : HasDerivAt (fun r : ℝ => L i / 2 * r ^ 2 * ‖h‖ ^ 2) (L i * t * ‖h‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L i / 2)).mul_const (‖h‖ ^ 2)
      exact this.congr_deriv (by first | ring | (norm_num; ring) | norm_num)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · intro t _
      exact (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hts : t • s = Pi.single i (t • h) := by
        rw [hs]; ext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      have hl := hlip i x (t • h)
      have hl2 : ‖partialGrad f (x + t • s) i - partialGrad f x i‖ ≤ L i * (t * ‖h‖) := by
        rw [hts]
        calc _ ≤ L i * ‖t • h‖ := hl
          _ = L i * (t * ‖h‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      have hop := (partialGrad f (x + t • s) i - partialGrad f x i).le_opNorm h
      have hop2 : (partialGrad f (x + t • s) i - partialGrad f x i) h ≤ ‖partialGrad f (x + t • s) i - partialGrad f x i‖ * ‖h‖ :=
        (le_abs_self _).trans hop
      have e1 : (partialGrad f (x + t • s) i - partialGrad f x i) h = partialGrad f (x + t • s) i h - partialGrad f x i h := rfl
      have := mul_le_mul_of_nonneg_right hl2 (norm_nonneg h)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at h01
  nlinarith


lemma sharp_props {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : F →L[ℝ] ℝ) (v : F)
    (hv : IsSharp s v) : s v = ‖v‖ ^ 2 ∧ ‖s‖ ≤ ‖v‖ := by
  have hG : s v = ‖v‖ ^ 2 := by
    have hscale : ∀ lam : ℝ, lam * s v - lam ^ 2 * ‖v‖ ^ 2 / 2 ≤ s v - ‖v‖ ^ 2 / 2 := by
      intro lam
      have := hv (lam • v)
      rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at this
      simp only [smul_eq_mul] at this
      linarith
    have hN : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    apply le_antisymm
    · by_contra hcon
      push_neg at hcon
      have hB : 0 < ‖v‖ ^ 2 + 1 := by positivity
      set t := (s v - ‖v‖ ^ 2) / (‖v‖ ^ 2 + 1) with ht
      have ht0 : 0 < t := div_pos (by linarith) hB
      have ht1 : t * (‖v‖ ^ 2 + 1) = s v - ‖v‖ ^ 2 := by rw [ht]; field_simp
      have h1 := hscale (1 + t)
      have h2 : t * (s v - ‖v‖ ^ 2 - t * ‖v‖ ^ 2 / 2) ≤ 0 := by nlinarith [h1]
      have h3 : s v - ‖v‖ ^ 2 - t * ‖v‖ ^ 2 / 2 ≤ 0 := by
        by_contra h; push_neg at h; nlinarith [mul_pos ht0 h]
      nlinarith [mul_nonneg ht0.le hN]
    · by_contra hcon
      push_neg at hcon
      have hB : 0 < ‖v‖ ^ 2 + 1 := by positivity
      set t := min 1 ((‖v‖ ^ 2 - s v) / (‖v‖ ^ 2 + 1)) with ht
      have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hB)
      have ht1 : t ≤ 1 := min_le_left _ _
      have ht2 : t ≤ (‖v‖ ^ 2 - s v) / (‖v‖ ^ 2 + 1) := min_le_right _ _
      have ht3 : t * (‖v‖ ^ 2 + 1) ≤ ‖v‖ ^ 2 - s v := by
        have := mul_le_mul_of_nonneg_right ht2 hB.le
        rwa [div_mul_cancel₀ _ hB.ne'] at this
      have h1 := hscale (1 - t)
      have h2 : t * (‖v‖ ^ 2 - s v - t * ‖v‖ ^ 2 / 2) ≤ 0 := by nlinarith [h1]
      have h3 : ‖v‖ ^ 2 - s v - t * ‖v‖ ^ 2 / 2 ≤ 0 := by
        by_contra h; push_neg at h; nlinarith [mul_pos ht0 h]
      nlinarith [mul_nonneg ht0.le hN]
  refine ⟨hG, ?_⟩
  have hbound : ∀ w : F, s w ≤ ‖v‖ * ‖w‖ := by
    intro w
    have hq : ∀ lam : ℝ, lam * s w ≤ ‖v‖ ^ 2 / 2 + lam ^ 2 * ‖w‖ ^ 2 / 2 := by
      intro lam
      have := hv (lam • w)
      rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hG] at this
      simp only [smul_eq_mul] at this
      linarith
    by_cases hw : ‖w‖ = 0
    · have hw0 : w = 0 := norm_eq_zero.mp hw
      subst hw0; simp
    · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
      have h1 := hq (s w / ‖w‖ ^ 2)
      have h2 : (s w) ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
        have e : s w / ‖w‖ ^ 2 * s w = (s w) ^ 2 / ‖w‖ ^ 2 := by ring
        have e2 : (s w / ‖w‖ ^ 2) ^ 2 * ‖w‖ ^ 2 / 2 = (s w) ^ 2 / ‖w‖ ^ 2 / 2 := by field_simp
        rw [e, e2] at h1
        have : (s w) ^ 2 / ‖w‖ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
        rw [div_le_iff₀ (by positivity)] at this
        exact this
      exact (abs_le_of_sq_le_sq' (by nlinarith [h2] : (s w) ^ 2 ≤ (‖v‖ * ‖w‖) ^ 2) (by positivity)).2
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  have h1 := hbound w
  have h2 := hbound (-w)
  rw [map_neg, norm_neg] at h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end ZZC3

open NesterovRCD.Sublinear in
theorem solution {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (hn : 0 < n) (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (α : ℝ) (x : Blocks E) :
    wdual L (1 - α) (gradBlocks f x) ^ 2 / (2 * S L α)
      ≤ f x - ∑ i, prob L α i * f (coordStep f L sharp i x) := by
  have hLpos : ∀ i, 0 < L i := hL.2.1
  have hstep : ∀ i, f (coordStep f L sharp i x) ≤ f x - ‖partialGrad f x i‖ ^ 2 / (2 * L i) := by
    intro i
    obtain ⟨hG, hgn⟩ := ZZC3.sharp_props (partialGrad f x i) (sharp i (partialGrad f x i)) (hsharp i _)
    set g := partialGrad f x i with hg
    set v := sharp i g with hv
    have hd := ZZC3.coord_descent f L hL i x (-((L i)⁻¹ • v))
    have e1 : coordStep f L sharp i x = x + Pi.single i (-((L i)⁻¹ • v)) := by
      simp only [coordStep, sub_eq_add_neg, Pi.single_neg]
      rfl
    rw [e1]
    have hLi := hLpos i
    have e2 : g (-((L i)⁻¹ • v)) = -((L i)⁻¹ * ‖v‖ ^ 2) := by
      rw [map_neg, map_smul, hG]; simp
    have e3 : ‖-((L i)⁻¹ • v)‖ ^ 2 = ((L i)⁻¹) ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
    rw [e2, e3] at hd
    have hgv : ‖g‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgn 2
    have e4 : f x + -((L i)⁻¹ * ‖v‖ ^ 2) + L i / 2 * ((L i)⁻¹ ^ 2 * ‖v‖ ^ 2) = f x - ‖v‖ ^ 2 / (2 * L i) := by
      field_simp; ring
    have e5 : ‖g‖ ^ 2 / (2 * L i) ≤ ‖v‖ ^ 2 / (2 * L i) := by gcongr
    linarith
  have hSpos : 0 < S L α := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hLpos i) α) Finset.univ_nonempty
  have hprob : ∑ i, prob L α i = 1 := by
    unfold prob
    rw [← Finset.sum_div]
    exact div_self hSpos.ne'
  have hnn : 0 ≤ ∑ i, (L i ^ (1 - α))⁻¹ * ‖gradBlocks f x i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (hLpos i).le _)) (sq_nonneg _))
  have hw : wdual L (1 - α) (gradBlocks f x) ^ 2 = ∑ i, (L i ^ (1 - α))⁻¹ * ‖gradBlocks f x i‖ ^ 2 := by
    unfold wdual
    exact Real.sq_sqrt hnn
  have hsum : ∑ i, prob L α i * f (coordStep f L sharp i x) ≤
      ∑ i, prob L α i * (f x - ‖partialGrad f x i‖ ^ 2 / (2 * L i)) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hstep i) (div_nonneg (Real.rpow_nonneg (hLpos i).le _) hSpos.le))
  have hrhs : ∑ i, prob L α i * (f x - ‖partialGrad f x i‖ ^ 2 / (2 * L i)) =
      f x - wdual L (1 - α) (gradBlocks f x) ^ 2 / (2 * S L α) := by
    have : ∑ i, prob L α i * (f x - ‖partialGrad f x i‖ ^ 2 / (2 * L i)) =
        f x * ∑ i, prob L α i - ∑ i, prob L α i * (‖partialGrad f x i‖ ^ 2 / (2 * L i)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hprob, mul_one, hw, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hLi := hLpos i
    unfold prob gradBlocks
    rw [Real.rpow_sub hLi, Real.rpow_one, inv_div]
    field_simp
  linarith
