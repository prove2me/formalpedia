-- Prove2me | solution 1 for LogRegretOCO.FTAL.ftal_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T15:38:08.344968+00:00
-- url     : https://prove2.me/submissions/9f315599-556b-4f82-a16a-a81ff7d53335

import Theorems.Thm_LogRegretOCO_FTAL_ftl_be_the_leader
import Theorems.Thm_LogRegretOCO_FTAL_elliptical_potential
import Theorems.Thm_LogRegretOCO_FTAL_exp_concave_approx_lower_bound
import Theorems.Thm_LogRegretOCO_FTAL_surrogate_regret_le
import Definitions.Def_LogRegretOCO_FTAL_IsFTALRun
import Mathlib

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace LogRegretOCO.FTAL

variable {n : ℕ}

lemma inner_eq_dot' (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪a, b⟫ = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- convexity: tangent line below the function -/
lemma conv_step (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g) (s s' : ℝ) (hd : DifferentiableAt ℝ g s) :
    g s - g s' ≤ deriv g s * (s - s') := by
  rcases lt_trichotomy s' s with h | h | h
  · have := hg.slope_le_deriv (mem_univ s') (mem_univ s) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hg.deriv_le_slope (mem_univ s) (mem_univ s') h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- first-order optimality of a minimiser along a segment -/
lemma opt_cond (s : Finset ℕ) (g : ℕ → ℝ → ℝ) (v : ℕ → EuclideanSpace ℝ (Fin n))
    (P : Set (EuclideanSpace ℝ (Fin n))) (hPconv : Convex ℝ P) (z y : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ P) (hy : y ∈ P) (hdiff : ∀ τ ∈ s, DifferentiableAt ℝ (g τ) ⟪v τ, z⟫)
    (hmin : ∀ w ∈ P, ∑ τ ∈ s, g τ ⟪v τ, z⟫ ≤ ∑ τ ∈ s, g τ ⟪v τ, w⟫) :
    0 ≤ ∑ τ ∈ s, deriv (g τ) ⟪v τ, z⟫ * (⟪v τ, y⟫ - ⟪v τ, z⟫) := by
  set h : ℝ → ℝ := fun l => ∑ τ ∈ s, g τ (⟪v τ, z⟫ + l * (⟪v τ, y⟫ - ⟪v τ, z⟫)) with hh
  have hd : HasDerivAt h (∑ τ ∈ s, deriv (g τ) ⟪v τ, z⟫ * (⟪v τ, y⟫ - ⟪v τ, z⟫)) 0 := by
    apply HasDerivAt.fun_sum
    intro τ hτ
    have h1 : HasDerivAt (fun l : ℝ => ⟪v τ, z⟫ + l * (⟪v τ, y⟫ - ⟪v τ, z⟫))
        (⟪v τ, y⟫ - ⟪v τ, z⟫) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (⟪v τ, y⟫ - ⟪v τ, z⟫)).const_add ⟪v τ, z⟫
    have h2 : HasDerivAt (g τ) (deriv (g τ) ⟪v τ, z⟫) (⟪v τ, z⟫ + 0 * (⟪v τ, y⟫ - ⟪v τ, z⟫)) := by
      simpa using (hdiff τ hτ).hasDerivAt
    exact h2.comp 0 h1
  have hmem : ∀ l ∈ Icc (0 : ℝ) 1, h l = ∑ τ ∈ s, g τ ⟪v τ, z + l • (y - z)⟫ := by
    intro l _
    simp only [hh, inner_add_right, inner_smul_right, inner_sub_right]
  have hge : ∀ l ∈ Ioo (0 : ℝ) 1, 0 ≤ l⁻¹ • (h (0 + l) - h 0) := by
    intro l hl
    have hw : z + l • (y - z) ∈ P := hPconv.add_smul_sub_mem hz hy ⟨hl.1.le, hl.2.le⟩
    have h1 := hmin _ hw
    rw [zero_add, hmem l ⟨hl.1.le, hl.2.le⟩, hmem 0 ⟨le_rfl, zero_le_one⟩]
    simp only [zero_smul, add_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hl.1.le) (by linarith)
  have ht := hd.tendsto_slope_zero_right
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
  exact hge l hl

/-- strong monotonicity of `g'` along a segment in `P` -/
lemma strong_mono (g : ℝ → ℝ) (v : EuclideanSpace ℝ (Fin n)) (a : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin n))) (hPconv : Convex ℝ P) (y z : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ P) (hz : z ∈ P)
    (hgdiff2 : ∀ w ∈ P, DifferentiableAt ℝ (deriv g) ⟪v, w⟫)
    (hg2 : ∀ w ∈ P, a ≤ deriv (deriv g) ⟪v, w⟫) :
    a * (⟪v, y⟫ - ⟪v, z⟫) ^ 2 ≤ (deriv g ⟪v, y⟫ - deriv g ⟪v, z⟫) * (⟪v, y⟫ - ⟪v, z⟫) := by
  set d := ⟪v, y⟫ - ⟪v, z⟫ with hdd
  set ψ : ℝ → ℝ := fun l => deriv g (⟪v, z⟫ + l * d) with hψ
  have hpt : ∀ l ∈ Icc (0 : ℝ) 1, ⟪v, z⟫ + l * d = ⟪v, z + l • (y - z)⟫ := by
    intro l _; simp only [inner_add_right, inner_smul_right, inner_sub_right, hdd]
  have hmemP : ∀ l ∈ Icc (0 : ℝ) 1, z + l • (y - z) ∈ P := fun l hl =>
    hPconv.add_smul_sub_mem hz hy hl
  have hder : ∀ l ∈ Icc (0 : ℝ) 1,
      HasDerivAt ψ (deriv (deriv g) (⟪v, z⟫ + l * d) * d) l := by
    intro l hl
    have h1 : HasDerivAt (fun l : ℝ => ⟪v, z⟫ + l * d) d l := by
      simpa using ((hasDerivAt_id l).mul_const d).const_add ⟪v, z⟫
    have h2 : DifferentiableAt ℝ (deriv g) (⟪v, z⟫ + l * d) := by
      rw [hpt l hl]; exact hgdiff2 _ (hmemP l hl)
    exact h2.hasDerivAt.comp l h1
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope ψ _ (zero_lt_one)
    (fun l hl => (hder l hl).continuousAt.continuousWithinAt)
    (fun l hl => hder l (Ioo_subset_Icc_self hl))
  simp only [hψ, zero_mul, add_zero, one_mul, sub_zero, div_one] at hξeq
  have hy' : ⟪v, z⟫ + d = ⟪v, y⟫ := by rw [hdd]; ring
  rw [hy'] at hξeq
  rw [← hξeq]
  have hge : a ≤ deriv (deriv g) (⟪v, z⟫ + ξ * d) := by
    rw [hpt ξ (Ioo_subset_Icc_self hξ)]; exact hg2 _ (hmemP ξ (Ioo_subset_Icc_self hξ))
  have := mul_le_mul_of_nonneg_right hge (sq_nonneg d)
  nlinarith


/-- the regularised Gram matrix -/
noncomputable def Wm (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (v τ)) (WithLp.ofLp (v τ)) +
    ε • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma vmv_quad (g w : Fin n → ℝ) : w ⬝ᵥ (vecMulVec g g *ᵥ w) = (g ⬝ᵥ w) ^ 2 := by
  have : vecMulVec g g *ᵥ w = (g ⬝ᵥ w) • g := by
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, dotProduct_smul, smul_eq_mul, dotProduct_comm w g]; ring

lemma Wm_quad (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : ℕ) (w : Fin n → ℝ) :
    w ⬝ᵥ (Wm v ε t *ᵥ w) = ∑ τ ∈ Finset.Icc 1 t, (WithLp.ofLp (v τ) ⬝ᵥ w) ^ 2 + ε * (w ⬝ᵥ w) := by
  unfold Wm
  rw [add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]
  simp only [vmv_quad]

lemma Wm_symm (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : ℕ) : (Wm v ε t)ᵀ = Wm v ε t := by
  unfold Wm
  rw [transpose_add, transpose_sum, transpose_smul, transpose_one]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by rw [transpose_vecMulVec]

lemma self_dot_nonneg (w : Fin n → ℝ) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)

lemma Wm_pos (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (t : ℕ) (w : Fin n → ℝ) :
    ε * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Wm v ε t *ᵥ w) := by
  rw [Wm_quad]
  have : 0 ≤ ∑ τ ∈ Finset.Icc 1 t, (WithLp.ofLp (v τ) ⬝ᵥ w) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma dot_self_eq_zero (w : Fin n → ℝ) (h : w ⬝ᵥ w = 0) : w = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (w j))).1 h i
    (Finset.mem_univ i)
  simpa using this

lemma Wm_det (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (t : ℕ) :
    IsUnit (Wm v ε t).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨w, hw0, hw⟩ := (exists_mulVec_eq_zero_iff).2 h
  have h1 := Wm_pos v ε hε t w
  rw [hw, dotProduct_zero] at h1
  have h2 := self_dot_nonneg w
  have : w ⬝ᵥ w = 0 := by nlinarith
  exact hw0 (dot_self_eq_zero w this)

/-- Cauchy–Schwarz in the `W`-geometry -/
lemma cs_W (v : ℕ → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (t : ℕ) (u w : Fin n → ℝ) :
    0 ≤ u ⬝ᵥ ((Wm v ε t)⁻¹ *ᵥ u) ∧
      (u ⬝ᵥ w) ^ 2 ≤ (u ⬝ᵥ ((Wm v ε t)⁻¹ *ᵥ u)) * (w ⬝ᵥ (Wm v ε t *ᵥ w)) := by
  set W := Wm v ε t
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ (W *ᵥ b) = b ⬝ᵥ (W *ᵥ a) := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, Wm_symm, dotProduct_comm]
  set h := W⁻¹ *ᵥ u
  have hWh : W *ᵥ h = u := by rw [mulVec_mulVec, mul_nonsing_inv W (Wm_det v ε hε t), one_mulVec]
  have hA : u ⬝ᵥ h = h ⬝ᵥ (W *ᵥ h) := by rw [hWh, dotProduct_comm]
  have hA0 : 0 ≤ u ⬝ᵥ h := by
    rw [hA]; exact le_trans (mul_nonneg hε.le (self_dot_nonneg h)) (Wm_pos v ε hε t h)
  refine ⟨hA0, ?_⟩
  have hB : h ⬝ᵥ (W *ᵥ w) = u ⬝ᵥ w := by rw [hsym, hWh, dotProduct_comm]
  have hq : ∀ l : ℝ, 0 ≤ w ⬝ᵥ (W *ᵥ w) - 2 * l * (u ⬝ᵥ w) + l ^ 2 * (u ⬝ᵥ h) := by
    intro l
    have := le_trans (mul_nonneg hε.le (self_dot_nonneg (w - l • h))) (Wm_pos v ε hε t (w - l • h))
    have e : (w - l • h) ⬝ᵥ (W *ᵥ (w - l • h)) =
        w ⬝ᵥ (W *ᵥ w) - 2 * l * (u ⬝ᵥ w) + l ^ 2 * (u ⬝ᵥ h) := by
      rw [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, hB, hsym w h, hB, ← hA]
      simp only [smul_eq_mul]; ring
    linarith
  rcases eq_or_lt_of_le hA0 with h0 | hpos
  · -- then h = 0, so u = 0
    have hh0 : h ⬝ᵥ h = 0 := by
      have := Wm_pos v ε hε t h
      rw [← hA, ← h0] at this
      have h1 := self_dot_nonneg h
      have h2 : h ⬝ᵥ h ≤ 0 := by
        by_contra hc
        push_neg at hc
        have := mul_pos hε hc
        linarith
      exact le_antisymm h2 h1
    have : u = 0 := by rw [← hWh, dot_self_eq_zero h hh0, mulVec_zero]
    rw [this, zero_dotProduct]; simp
  · have := hq ((u ⬝ᵥ w) / (u ⬝ᵥ h))
    have e : w ⬝ᵥ (W *ᵥ w) - 2 * ((u ⬝ᵥ w) / (u ⬝ᵥ h)) * (u ⬝ᵥ w) +
        ((u ⬝ᵥ w) / (u ⬝ᵥ h)) ^ 2 * (u ⬝ᵥ h) =
        w ⬝ᵥ (W *ᵥ w) - (u ⬝ᵥ w) ^ 2 / (u ⬝ᵥ h) := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hpos] at this
    linarith

lemma quad_root {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c) (h : p ^ 2 ≤ q * (p + c)) :
    p ≤ q + c := by
  by_contra hlt
  push_neg at hlt
  nlinarith [mul_le_mul_of_nonneg_left (show q ≤ p by linarith) hc]


theorem ftl_main (P : Set (EuclideanSpace ℝ (Fin n))) (D R a b : ℝ)
    (g : ℕ → ℝ → ℝ) (v : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P)
    (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hv : ∀ t, 1 ≤ t → ‖v t‖ ≤ R)
    (hgconv : ∀ t, 1 ≤ t → ConvexOn ℝ Set.univ (g t))
    (hgdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (g t) (inner ℝ (v t) y))
    (hgdiff2 : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (deriv (g t)) (inner ℝ (v t) y))
    (hg1 : ∀ t, 1 ≤ t → ∀ y ∈ P, |deriv (g t) (inner ℝ (v t) y)| ≤ b)
    (hg2 : ∀ t, 1 ≤ t → ∀ y ∈ P, a ≤ deriv (deriv (g t)) (inner ℝ (v t) y))
    (hx : IsFTLRun P (fun t y => g t (inner ℝ (v t) y)) x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (g t (inner ℝ (v t) (x t)) - g t (inner ℝ (v t) u))
        ≤ n * b ^ 2 / a * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1)
          + b ^ 2 / a := by
  intro T hT u hu
  set f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun t y => g t (inner ℝ (v t) y) with hf
  have hbl := ftl_be_the_leader P f x hx T u hu
  rw [Finset.sum_sub_distrib]
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := fun t ht => (hx t ht).1
  obtain ⟨y0, hy0⟩ := hPne
  have hD0 : 0 ≤ D := by have := hdiam y0 hy0 y0 hy0; simpa using this
  have hRHS0 : 0 ≤ n * b ^ 2 / a * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by have : 0 ≤ a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 := by positivity
                              linarith)
  have hba : 0 < b ^ 2 / a := by positivity
  rcases eq_or_lt_of_le hD0 with hD | hD
  · -- degenerate case: `P` is a single point
    have heq : ∀ y ∈ P, ∀ z ∈ P, y = z := fun y hy z hz => by
      have := hdiam y hy z hz; rw [← hD] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have : ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun t ht => ?_
      have ht1 := (Finset.mem_Icc.1 ht).1
      rw [heq _ (hxP t ht1) _ (hxP (t + 1) (by omega)), sub_self]
    linarith
  -- main case
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set ε := b ^ 2 / (a ^ 2 * D ^ 2 * T) with hε
  have hεpos : 0 < ε := by positivity
  set c := a * ε * D ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hcT : T * c = b ^ 2 / a := by rw [hc, hε]; field_simp
  set ω : ℕ → ℝ := fun t => WithLp.ofLp (v t) ⬝ᵥ ((Wm v ε t)⁻¹ *ᵥ WithLp.ofLp (v t)) with hω
  have step : ∀ t ∈ Finset.Icc 1 T, f t (x t) - f t (x (t + 1)) ≤ b ^ 2 / a * ω t + c := by
    intro t htT
    have ht := (Finset.mem_Icc.1 htT).1
    have hxt := hxP t ht
    have hxt1 := hxP (t + 1) (by omega)
    set s : ℕ → ℝ := fun τ => ⟪v τ, x t⟫ with hs
    set r : ℕ → ℝ := fun τ => ⟪v τ, x (t + 1)⟫ with hr
    -- optimality conditions
    have opt1 := opt_cond (Finset.Ico 1 (t + 1)) g v P hPconv (x (t + 1)) (x t) hxt1 hxt
      (fun τ hτ => hgdiff τ (Finset.mem_Ico.1 hτ).1 _ hxt1) (hx (t + 1) (by omega)).2
    have opt2 := opt_cond (Finset.Ico 1 t) g v P hPconv (x t) (x (t + 1)) hxt hxt1
      (fun τ hτ => hgdiff τ (Finset.mem_Ico.1 hτ).1 _ hxt) (hx t ht).2
    have hmono : ∀ τ ∈ Finset.Ico 1 (t + 1),
        a * (s τ - r τ) ^ 2 ≤ (deriv (g τ) (s τ) - deriv (g τ) (r τ)) * (s τ - r τ) :=
      fun τ hτ => strong_mono (g τ) (v τ) a P hPconv (x t) (x (t + 1)) hxt hxt1
        (hgdiff2 τ (Finset.mem_Ico.1 hτ).1) (hg2 τ (Finset.mem_Ico.1 hτ).1)
    set p := deriv (g t) (s t) * (s t - r t) with hp
    have hQ : a * ∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 ≤ p := by
      have h1 := Finset.sum_le_sum hmono
      rw [← Finset.mul_sum] at h1
      have e1 : ∑ τ ∈ Finset.Ico 1 (t + 1), (deriv (g τ) (s τ) - deriv (g τ) (r τ)) * (s τ - r τ)
          = ∑ τ ∈ Finset.Ico 1 (t + 1), deriv (g τ) (s τ) * (s τ - r τ)
            - ∑ τ ∈ Finset.Ico 1 (t + 1), deriv (g τ) (r τ) * (s τ - r τ) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun τ _ => by ring
      have e2 : ∑ τ ∈ Finset.Ico 1 (t + 1), deriv (g τ) (s τ) * (s τ - r τ) =
          ∑ τ ∈ Finset.Ico 1 t, deriv (g τ) (s τ) * (s τ - r τ) + p := by
        rw [Finset.sum_Ico_succ_top ht]
      have e3 : ∑ τ ∈ Finset.Ico 1 t, deriv (g τ) (s τ) * (s τ - r τ) =
          -∑ τ ∈ Finset.Ico 1 t, deriv (g τ) ⟪v τ, x t⟫ * (⟪v τ, x (t + 1)⟫ - ⟪v τ, x t⟫) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun τ _ => by simp [hs, hr]; ring
      have e4 : ∑ τ ∈ Finset.Ico 1 (t + 1), deriv (g τ) (r τ) * (s τ - r τ) =
          ∑ τ ∈ Finset.Ico 1 (t + 1), deriv (g τ) ⟪v τ, x (t + 1)⟫ *
            (⟪v τ, x t⟫ - ⟪v τ, x (t + 1)⟫) := rfl
      rw [Finset.Ico_add_one_right_eq_Icc] at h1 e1 e2 e4 opt1
      rw [e1, e2, e3, e4] at h1
      linarith
    -- the `W`-geometry
    set Δ : Fin n → ℝ := WithLp.ofLp (x t) - WithLp.ofLp (x (t + 1)) with hΔ
    have hdτ : ∀ τ, WithLp.ofLp (v τ) ⬝ᵥ Δ = s τ - r τ := fun τ => by
      simp only [hΔ, dotProduct_sub, hs, hr, inner_eq_dot']
    have hΔΔ : Δ ⬝ᵥ Δ ≤ D ^ 2 := by
      have h1 : Δ ⬝ᵥ Δ = ‖x t - x (t + 1)‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_eq_dot']; simp [hΔ]
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _) (hdiam _ hxt _ hxt1) 2
    have hWΔ : Δ ⬝ᵥ (Wm v ε t *ᵥ Δ) ≤ ∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2 := by
      rw [Wm_quad]
      simp only [hdτ]
      have := mul_le_mul_of_nonneg_left hΔΔ hεpos.le
      linarith
    obtain ⟨hω0, hcs⟩ := cs_W v ε hεpos t (WithLp.ofLp (v t)) Δ
    rw [hdτ] at hcs
    have hg1t : |deriv (g t) (s t)| ≤ b := hg1 t ht _ hxt
    have hgsq : deriv (g t) (s t) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hg1t 2
    have hp0 : 0 ≤ p := le_trans (mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hQ
    -- p^2 ≤ (b^2 ω / a) (p + c)
    have hpsq : p ^ 2 ≤ b ^ 2 / a * ω t * (p + c) := by
      have h1 : p ^ 2 = deriv (g t) (s t) ^ 2 * (s t - r t) ^ 2 := by rw [hp]; ring
      have h2 : (s t - r t) ^ 2 ≤ ω t * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2) :=
        hcs.trans (mul_le_mul_of_nonneg_left hWΔ hω0)
      have h3 : a * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2) ≤ p + c := by
        rw [hc]; nlinarith
      have h4 : p ^ 2 ≤ b ^ 2 * (ω t * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2)) := by
        rw [h1]
        exact mul_le_mul hgsq h2 (sq_nonneg _) (sq_nonneg _)
      have h5 : b ^ 2 * (ω t * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2)) ≤
          b ^ 2 / a * ω t * (p + c) := by
        have e : b ^ 2 * (ω t * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2)) =
            b ^ 2 / a * ω t * (a * (∑ τ ∈ Finset.Icc 1 t, (s τ - r τ) ^ 2 + ε * D ^ 2)) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    have hpq := quad_root hp0 (by positivity) hc0 hpsq
    have hconv := conv_step (g t) (hgconv t ht) (s t) (r t) (hgdiff t ht _ hxt)
    show g t (s t) - g t (r t) ≤ _
    linarith
  have hsum := Finset.sum_le_sum step
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, hcT] at hsum
  have hell := elliptical_potential v R ε T hR hεpos (fun t ht => hv t (Finset.mem_Icc.1 ht).1)
  simp only at hell
  have hell' : ∑ t ∈ Finset.Icc 1 T, ω t ≤ n * Real.log (R ^ 2 * T / ε + 1) := hell
  have harg : R ^ 2 * T / ε = a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 := by
    rw [hε]; field_simp
  rw [harg] at hell'
  have hfin := mul_le_mul_of_nonneg_left hell' hba.le
  have e : b ^ 2 / a * (n * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1)) =
      n * b ^ 2 / a * Real.log (a ^ 2 * D ^ 2 * R ^ 2 * T ^ 2 / b ^ 2 + 1) := by ring
  rw [Finset.sum_sub_distrib] at hsum
  linarith


set_option maxHeartbeats 1000000 in
theorem ftal_main (P : Set (EuclideanSpace ℝ (Fin n))) (D G α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hG : 0 < G) (hα : 0 < α)
    (hdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t, 1 ≤ t → ConcaveOn ℝ P (fun y => Real.exp (-α * f t y)))
    (hx : IsFTALRun P (1 / 2 * min (1 / (4 * G * D)) α) f x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u)
        ≤ 64 * (1 / α + G * D) * n * (Real.log T + 1) := by
  intro T hT u hu
  set β := 1 / 2 * min (1 / (4 * G * D)) α with hβ
  have hβ0 : 0 < β := by rw [hβ]; apply mul_pos (by norm_num); apply lt_min _ hα; positivity
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := fun t ht => (hx t ht).1
  -- degenerate dimension
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hsub : ∀ a b : EuclideanSpace ℝ (Fin 0), a = b := fun a b => by ext i; exact i.elim0
    have : ∀ t, f t (x t) - f t u = 0 := fun t => by rw [hsub (x t) u]; ring
    simp [this]
  -- surrogate losses
  have hsur := surrogate_regret_le P f (approxLoss f x β) x T
    (fun t ht => hxP t (Finset.mem_Icc.1 ht).1)
    (fun t ht => by simp [approxLoss])
    (fun t ht y hy => exp_concave_approx_lower_bound P (f t) D G α β hPconv hD hG hα hdiam
      (hdiff t (Finset.mem_Icc.1 ht).1) (hgrad t (Finset.mem_Icc.1 ht).1)
      (hexp t (Finset.mem_Icc.1 ht).1) hβ0 le_rfl y hy (x t) (hxP t (Finset.mem_Icc.1 ht).1)) u hu
  rw [Finset.sum_sub_distrib]
  set v : ℕ → EuclideanSpace ℝ (Fin n) := fun t => gradient (f t) (x t) with hv
  set cc : ℕ → ℝ := fun t => ⟪v t, x t⟫ with hcc
  set g : ℕ → ℝ → ℝ := fun t w => f t (x t) + (w - cc t) + β / 2 * (w - cc t) ^ 2 with hg
  have hgeq : approxLoss f x β = fun t y => g t ⟪v t, y⟫ := by
    funext t y
    simp only [approxLoss, hg, hcc, hv, inner_sub_right]
  have hderiv : ∀ t w, HasDerivAt (g t) (1 + β * (w - cc t)) w := by
    intro t w
    have h1 := ((hasDerivAt_id w).sub_const (cc t))
    have h2 := (h1.pow 2).const_mul (β / 2)
    have := ((hasDerivAt_const w (f t (x t))).add h1).add h2
    exact this.congr_deriv (by norm_num <;> ring)
  have hderivg : ∀ t, deriv (g t) = fun w => 1 + β * (w - cc t) := fun t => by
    funext w; exact (hderiv t w).deriv
  have hderiv2 : ∀ t w, HasDerivAt (deriv (g t)) β w := by
    intro t w
    rw [hderivg]
    have := ((hasDerivAt_id w).sub_const (cc t)).const_mul β |>.const_add 1
    exact this.congr_deriv (by ring)
  -- apply the FTL bound
  set b := 1 + β * (G * D) with hb
  have hbpos : 0 < b := by positivity
  have hFTL := ftl_main P D G β b g v x hPne hPconv hdiam hG hβ0 hbpos
    (fun t ht => hgrad t ht _ (hxP t ht))
    (fun t ht => by
      refine ⟨convex_univ, fun y _ z _ a' b' ha' hb' hab => ?_⟩
      obtain rfl : b' = 1 - a' := by linarith
      simp only [hg, smul_eq_mul]
      nlinarith [mul_nonneg hβ0.le (mul_nonneg (mul_nonneg ha' hb') (sq_nonneg (y - z)))])
    (fun t ht y hy => (hderiv t _).differentiableAt)
    (fun t ht y hy => (hderiv2 t _).differentiableAt)
    (fun t ht y hy => by
      rw [hderivg]
      have h1 : |⟪v t, y⟫ - cc t| ≤ G * D := by
        rw [hcc, ← inner_sub_right]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hgrad t ht _ (hxP t ht)) (hdiam _ hy _ (hxP t ht))
          (norm_nonneg _) hG.le
      simp only
      calc |1 + β * (⟪v t, y⟫ - cc t)| ≤ |1| + |β * (⟪v t, y⟫ - cc t)| := abs_add_le _ _
        _ = 1 + β * |⟪v t, y⟫ - cc t| := by rw [abs_one, abs_mul, abs_of_pos hβ0]
        _ ≤ 1 + β * (G * D) := by nlinarith)
    (fun t ht y hy => by rw [(hderiv2 t _).deriv])
    (by rw [← hgeq]; exact hx) T hT u hu
  rw [← Finset.sum_sub_distrib] at hsur
  have hsur' : ∑ t ∈ Finset.Icc 1 T, (approxLoss f x β t (x t) - approxLoss f x β t u) =
      ∑ t ∈ Finset.Icc 1 T, (g t ⟪v t, x t⟫ - g t ⟪v t, u⟫) := by rw [hgeq]
  rw [Finset.sum_sub_distrib] at hsur hsur'
  rw [hsur'] at hsur
  rw [Finset.sum_sub_distrib] at hFTL
  -- arithmetic
  have hβGD : β * (G * D) ≤ 1 / 8 := by
    have h1 : β ≤ 1 / 2 * (1 / (4 * G * D)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ G * D)
    have e : 1 / 2 * (1 / (4 * G * D)) * (G * D) = 1 / 8 := by field_simp; ring
    linarith
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith [mul_pos hβ0 (mul_pos hG hD)]
  have hb2 : b ^ 2 ≤ 81 / 64 := by nlinarith
  have hinvβ : 1 / β ≤ 8 * (1 / α + G * D) := by
    have e : 1 / β = 2 / min (1 / (4 * G * D)) α := by rw [hβ]; field_simp
    rw [e]
    have hα' : 0 < 1 / α := by positivity
    have hGD : 0 < G * D := by positivity
    rcases min_choice (1 / (4 * G * D)) α with h | h
    · rw [h]
      have : 2 / (1 / (4 * G * D)) = 8 * (G * D) := by field_simp; ring
      rw [this]; linarith
    · rw [h]
      have : 2 / α = 2 * (1 / α) := by ring
      rw [this]; linarith
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hTR
  have harg : β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1 ≤ 2 * T ^ 2 := by
    have h1 : β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 ≤ T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have e : β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 = (β * (G * D)) ^ 2 * T ^ 2 := by ring
      rw [e]
      have h0 : 0 ≤ β * (G * D) := by positivity
      have h2 : (β * (G * D)) ^ 2 ≤ 1 := by nlinarith
      have h3 : 1 ≤ b ^ 2 := by nlinarith
      calc (β * (G * D)) ^ 2 * T ^ 2 ≤ 1 * T ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ ≤ b ^ 2 * T ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        _ = T ^ 2 * b ^ 2 := by ring
    have : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    linarith
  have hlog : Real.log (β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1) ≤ 1 + 2 * Real.log T := by
    calc Real.log (β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1) ≤ Real.log (2 * T ^ 2) :=
          Real.log_le_log (by positivity) harg
      _ = Real.log 2 + 2 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 1 + 2 * Real.log T := by linarith [Real.log_two_lt_d9]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : b ^ 2 / β ≤ 81 / 8 * (1 / α + G * D) := by
    rw [div_eq_mul_one_div]
    calc b ^ 2 * (1 / β) ≤ 81 / 64 * (8 * (1 / α + G * D)) :=
          mul_le_mul hb2 hinvβ (by positivity) (by norm_num)
      _ = 81 / 8 * (1 / α + G * D) := by ring
  set K := 1 / α + G * D with hKdef
  have hK0 : 0 < K := by positivity
  have hLpos : 0 ≤ Real.log (β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1) :=
    Real.log_nonneg (by have : 0 ≤ β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 := by positivity
                        linarith)
  have hmain : n * b ^ 2 / β * Real.log (β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1) + b ^ 2 / β
      ≤ 64 * K * n * (Real.log T + 1) := by
    have e : n * b ^ 2 / β = n * (b ^ 2 / β) := by ring
    rw [e]
    have h1 : n * (b ^ 2 / β) * Real.log (β ^ 2 * D ^ 2 * G ^ 2 * T ^ 2 / b ^ 2 + 1) ≤
        n * (81 / 8 * K) * (1 + 2 * Real.log T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hK (by positivity)) hlog hLpos (by positivity)
    have h3 : 1 ≤ n * (Real.log T + 1) := by
      have := mul_le_mul hnR (show (1 : ℝ) ≤ Real.log T + 1 by linarith) zero_le_one (by linarith)
      linarith
    have h4 : 81 / 8 * K * 1 ≤ 81 / 8 * K * (n * (Real.log T + 1)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have hnK : 0 ≤ (n : ℝ) * K := by positivity
    have hnKL : 0 ≤ (n : ℝ) * K * Real.log T := mul_nonneg hnK hlogT
    have e1 : n * (81 / 8 * K) * (1 + 2 * Real.log T) =
        81 / 8 * (n * K) + 81 / 4 * (n * K * Real.log T) := by ring
    have e2 : 81 / 8 * K * (n * (Real.log T + 1)) =
        81 / 8 * (n * K) + 81 / 8 * (n * K * Real.log T) := by ring
    have e3 : 64 * K * n * (Real.log T + 1) = 64 * (n * K) + 64 * (n * K * Real.log T) := by ring
    rw [e1] at h1
    rw [e2] at h4
    rw [e3]
    linarith
  rw [Finset.sum_sub_distrib] at hsur
  linarith

end LogRegretOCO.FTAL

open LogRegretOCO.FTAL

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (D G α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPclosed : IsClosed P)
    (hPbdd : Bornology.IsBounded P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hG : 0 < G) (hα : 0 < α)
    (hdiff : ∀ t, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t, 1 ≤ t → ConcaveOn ℝ P (fun y => Real.exp (-α * f t y)))
    (hx : IsFTALRun P (1 / 2 * min (1 / (4 * G * D)) α) f x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u)
        ≤ 64 * (1 / α + G * D) * n * (Real.log T + 1) := by
  exact ftal_main P D G α f x hPne hPconv hD hdiam hG hα hdiff hgrad hexp hx
