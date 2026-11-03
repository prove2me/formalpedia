-- Prove2me | solution 1 for HryniewiczCriterion.czIndexOfPath_eq_of_polarAngleLift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:03:24.834206+00:00
-- url     : https://prove2.me/submissions/dd5778b3-c680-4877-9b86-e3bee9329be4

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.UnitInterval
import Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne

open HryniewiczCriterion Matrix

namespace CZB2

noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- `⟨e_s, M e_s⟩`. -/
def dotv (M : M2) (s : ℝ) : ℝ :=
  M 0 0 * Real.cos s ^ 2 + (M 0 1 + M 1 0) * Real.cos s * Real.sin s + M 1 1 * Real.sin s ^ 2

/-- `e_s × M e_s`. -/
def crossv (M : M2) (s : ℝ) : ℝ :=
  M 1 0 * Real.cos s ^ 2 + (M 1 1 - M 0 0) * Real.cos s * Real.sin s - M 0 1 * Real.sin s ^ 2

def zv (M : M2) (s : ℝ) : ℂ := (dotv M s : ℂ) + (crossv M s : ℂ) * Complex.I

@[simp] theorem zv_re (M : M2) (s : ℝ) : (zv M s).re = dotv M s := by simp [zv]
@[simp] theorem zv_im (M : M2) (s : ℝ) : (zv M s).im = crossv M s := by simp [zv]

theorem mulVec_rv (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ![dotv M s * Real.cos s - crossv M s * Real.sin s,
      dotv M s * Real.sin s + crossv M s * Real.cos s] := by
  have h := Real.sin_sq_add_cos_sq s
  ext i; fin_cases i <;>
    simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dotv, crossv]
  · linear_combination (-(M 0 0 * Real.cos s) - M 0 1 * Real.sin s) * h
  · linear_combination (-(M 1 0 * Real.cos s) - M 1 1 * Real.sin s) * h

theorem dotProduct_eq (M : M2) (s : ℝ) :
    rotationVector s ⬝ᵥ (M *ᵥ rotationVector s) = dotv M s := by
  have h := Real.sin_sq_add_cos_sq s
  rw [mulVec_rv]
  simp [rotationVector, dotProduct, Fin.sum_univ_two]
  linear_combination dotv M s * h

theorem mulVec_eq_smul (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ‖zv M s‖ • rotationVector (s + Complex.arg (zv M s)) := by
  have hc := Complex.norm_mul_cos_arg (zv M s)
  have hs := Complex.norm_mul_sin_arg (zv M s)
  simp only [zv_re, zv_im] at hc hs
  rw [mulVec_rv]
  ext i; fin_cases i <;> simp [rotationVector, Real.cos_add, Real.sin_add]
  · rw [← hc, ← hs]; ring
  · rw [← hc, ← hs]; ring

theorem rot_mulVec (a x : ℝ) : rotationMatrix a *ᵥ rotationVector x = rotationVector (a + x) := by
  ext i; fin_cases i <;>
    simp [rotationMatrix, rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;> ring

theorem rot_mul_apply0 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 0 j = Real.cos a * M 0 j - Real.sin a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]; ring

theorem rot_mul_apply1 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 1 j = Real.sin a * M 0 j + Real.cos a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]

theorem rot_neg_mul (a : ℝ) : rotationMatrix (-a) * rotationMatrix a = 1 := by
  have h := Real.sin_sq_add_cos_sq a
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem rv_ne_zero (s : ℝ) : rotationVector s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have := Real.sin_sq_add_cos_sq s
  rw [h0, h1] at this; norm_num at this

theorem cos_sub_eq_one {r r' x y : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : r' • rotationVector x = r • rotationVector y) : Real.cos (x - y) = 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hsq : r' ^ 2 = r ^ 2 := by
    have : (r' * Real.sin x) ^ 2 + (r' * Real.cos x) ^ 2 = (r * Real.sin y) ^ 2 + (r * Real.cos y) ^ 2 := by
      rw [h0, h1]
    nlinarith
  have hrr : r' = r := by nlinarith
  subst hrr
  have hc : Real.cos x = Real.cos y := mul_left_cancel₀ hr.ne' h0
  have hs : Real.sin x = Real.sin y := mul_left_cancel₀ hr.ne' h1
  rw [Real.cos_sub, hc, hs]; linarith

theorem polar (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ s ∈ Set.Icc 0 (2 * Real.pi), ∃ ρ : ℝ, 0 < ρ ∧ x = ρ * Real.cos s ∧ y = ρ * Real.sin s := by
  set z : ℂ := ⟨x, y⟩
  have hz : z ≠ 0 := by
    intro e; rcases h with h | h
    · exact h (congrArg Complex.re e)
    · exact h (congrArg Complex.im e)
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  by_cases ha : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, ⟨ha, by linarith⟩, ‖z‖, hpos, hc.symm, hs.symm⟩
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨by linarith, by linarith⟩, ‖z‖, hpos, ?_, ?_⟩
    · rw [Real.cos_add_two_pi]; exact hc.symm
    · rw [Real.sin_add_two_pi]; exact hs.symm

theorem indef (c m b : ℝ) (h : 0 < m ^ 2 + 4 * b * c) :
    ∃ x y : ℝ, 0 < c * x ^ 2 + m * x * y - b * y ^ 2 := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · exact ⟨0, 1, by nlinarith⟩
  · subst hb
    have hm : m ≠ 0 := by intro e; subst e; norm_num at h
    refine ⟨m / (2 * |c| + 1), 1, ?_⟩
    have hd : 0 < 2 * |c| + 1 := by positivity
    have hm2 : 0 < m ^ 2 := by positivity
    have e : c * (m / (2 * |c| + 1)) ^ 2 + m * (m / (2 * |c| + 1)) * 1 - 0 * 1 ^ 2 =
        m ^ 2 * (c + (2 * |c| + 1)) / (2 * |c| + 1) ^ 2 := by field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    apply mul_pos hm2
    have := neg_abs_le c
    linarith
  · exact ⟨2 * b, m, by nlinarith⟩

/-- `e_s × B e_s = r sin(θ - s)` when `B e_s = r e_θ`. -/
theorem crossv_eq (B : M2) (s r θ : ℝ) (h : B *ᵥ rotationVector s = r • rotationVector θ) :
    crossv B s = r * Real.sin (θ - s) := by
  have hc := Real.sin_sq_add_cos_sq s
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [mulVec_rv] at h0 h1
  simp [rotationVector] at h0 h1
  rw [Real.sin_sub]
  linear_combination (-crossv B s) * hc + Real.cos s * h1 - Real.sin s * h0

/-- `crossv` at a nonzero vector, scaled. -/
theorem crossv_polar (B : M2) (ρ s : ℝ) :
    B 1 0 * (ρ * Real.cos s) ^ 2 + (B 1 1 - B 0 0) * (ρ * Real.cos s) * (ρ * Real.sin s) -
      B 0 1 * (ρ * Real.sin s) ^ 2 = ρ ^ 2 * crossv B s := by
  simp only [crossv]; ring

end

end CZB2

namespace CZB2

theorem int_eq_of_lt {z a : ℤ} (h1 : (a : ℝ) - 1 < z) (h2 : (z : ℝ) < a + 1) : z = a := by
  have h1' : a - 1 < z := by exact_mod_cast h1
  have h2' : z < a + 1 := by exact_mod_cast h2
  omega

theorem czIndexOfPath_eq_of_polarAngleLift (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1)) (h0 : φ 0 = 1)
    (hdet : (φ 1).det = 1) (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α) (k : ℤ) :
    (2 < (φ 1).trace → |α 1 - 2 * Real.pi * k| < Real.pi / 2 → czIndexOfPath φ = 2 * k) ∧
    ((φ 1).trace < 2 → 2 * Real.pi * k < α 1 → α 1 < 2 * Real.pi * k + 2 * Real.pi →
      czIndexOfPath φ = 2 * k + 1) := by
  have hpi := Real.pi_pos
  set P : ℝ → M2 := fun t => rotationMatrix (-α t) * φ t with hPdef
  have hφP : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t = rotationMatrix (α t) * P t ∧ (P t).PosDef := by
    intro t ht
    obtain ⟨Q, hQ, hφQ⟩ := hα.2.2 t ht
    have : P t = Q := by
      simp only [hPdef]; rw [hφQ, ← Matrix.mul_assoc, rot_neg_mul, Matrix.one_mul]
    rw [this]; exact ⟨hφQ, hQ⟩
  -- continuity
  have hφij : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hαc := hα.1
  have hPij : ∀ i j, ContinuousOn (fun t => P t i j) (Set.Icc 0 1) := by
    intro i j
    have h0j := hφij 0 j
    have h1j := hφij 1 j
    fin_cases i
    · simp only [hPdef, Fin.zero_eta, rot_mul_apply0]; fun_prop
    · simp only [hPdef, Fin.mk_one, rot_mul_apply1]; fun_prop
  -- the explicit lift from `s`
  set θs : ℝ → ℝ → ℝ := fun s t => s + α t + Complex.arg (zv (P t) s) with hθsdef
  have hdotpos : ∀ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < dotv (P t) s := by
    intro s t ht
    have := (hφP t ht).2.dotProduct_mulVec_pos (rv_ne_zero s)
    rwa [star_trivial, dotProduct_eq] at this
  have hzne : ∀ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, zv (P t) s ≠ 0 := fun s t ht e => by
    have := congrArg Complex.re e; simp at this; linarith [hdotpos s t ht]
  have hlift : ∀ s, IsAngleLift φ s (θs s) := by
    intro s
    refine ⟨?_, ?_, ?_⟩
    · have hz : ContinuousOn (fun t => zv (P t) s) (Set.Icc 0 1) := by
        have := hPij 0 0; have := hPij 0 1; have := hPij 1 0; have := hPij 1 1
        simp only [zv, dotv, crossv]; fun_prop
      have harg : ContinuousOn (fun t => Complex.arg (zv (P t) s)) (Set.Icc 0 1) := by
        intro t ht
        exact (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2
          (Or.inl (by simpa using hdotpos s t ht)))).comp_continuousWithinAt (hz t ht)
      exact (continuousOn_const.add hαc).add harg
    · have hP0 : P 0 = 1 := by
        simp only [hPdef, hα.2.1, h0, neg_zero, Matrix.mul_one]
        ext i j; fin_cases i <;> fin_cases j <;> simp [rotationMatrix]
      have hz0 : zv (P 0) s = 1 := by
        rw [hP0]
        apply Complex.ext <;> simp [dotv, crossv]
      simp [hθsdef, hα.2.1, hz0]
    · intro t ht
      refine ⟨‖zv (P t) s‖, norm_pos_iff.2 (hzne s t ht), ?_⟩
      rw [(hφP t ht).1, ← Matrix.mulVec_mulVec, mulVec_eq_smul, Matrix.mulVec_smul, rot_mulVec]
      simp only [hθsdef]
      congr 2; ring
  -- uniqueness of the end point of a lift
  have huniq : ∀ s θ, IsAngleLift φ s θ → θ 1 = θs s 1 := by
    intro s θ hθ
    let f : unitInterval → ℝ := fun t => θ t - θs s t
    have hfc : Continuous f :=
      (hθ.1.comp_continuous continuous_subtype_val (fun t => t.2)).sub
        ((hlift s).1.comp_continuous continuous_subtype_val (fun t => t.2))
    have hcos : ∀ t : unitInterval, Real.cos (f t) = 1 := by
      intro t
      obtain ⟨r', hr', e'⟩ := hθ.2.2 t t.2
      obtain ⟨r, hr, e⟩ := (hlift s).2.2 t t.2
      exact cos_sub_eq_one hr hr' (e'.symm.trans e)
    obtain ⟨m, hm⟩ := FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne f hfc Real.pi
      (2 * Real.pi) (by linarith) (by
        intro t m e
        have := hcos t
        rw [e, Real.cos_add_int_mul_two_pi, Real.cos_pi] at this
        norm_num at this)
    have hf0 : f 0 = 0 := by
      simp only [f, Set.Icc.coe_zero, hθ.2.1, (hlift s).2.1, sub_self]
    have hm1 : m = -1 := by
      obtain ⟨a1, a2⟩ := hm 0
      rw [hf0] at a1 a2
      apply int_eq_of_lt <;> push_cast <;> nlinarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (f 1)).1 (hcos 1)
    have hn0 : n = 0 := by
      obtain ⟨a1, a2⟩ := hm 1
      rw [← hn, hm1] at a1 a2
      push_cast at a1 a2
      apply int_eq_of_lt <;> push_cast <;> nlinarith
    have : f 1 = 0 := by rw [← hn, hn0]; simp
    simpa [f, sub_eq_zero] using this
  -- description of the winding interval
  set W := windingInterval φ with hWdef
  set δ : ℝ → ℝ := fun s => Complex.arg (zv (P 1) s) with hδdef
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hW1 : ∀ d ∈ W, ∃ s, 2 * Real.pi * d = α 1 + δ s := by
    rintro d ⟨s, -, θ, hθ, rfl⟩
    refine ⟨s, ?_⟩
    rw [huniq s θ hθ]
    simp only [hθsdef, hδdef]
    field_simp; ring
  have hW2 : ∀ s ∈ Set.Icc 0 (2 * Real.pi), (α 1 + δ s) / (2 * Real.pi) ∈ W := by
    intro s hs
    refine ⟨s, hs, θs s, hlift s, ?_⟩
    simp only [hθsdef, hδdef]; ring
  have hδlt : ∀ s, |δ s| < Real.pi / 2 := fun s =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa using hdotpos s 1 h1I))
  have hne : W.Nonempty := ⟨_, hW2 0 ⟨le_rfl, by linarith⟩⟩
  have hB := (hφP 1 h1I).1
  have hPm := (hφP 1 h1I).2
  have hsym : P 1 1 0 = P 1 0 1 := by
    have := congrFun (congrFun hPm.1 0) 1
    simpa [Matrix.conjTranspose_apply] using this
  have htrB : (φ 1).trace = (P 1 0 0 + P 1 1 1) * Real.cos (α 1) := by
    rw [hB, Matrix.trace_fin_two, rot_mul_apply0, rot_mul_apply1, hsym]
    ring
  constructor
  · intro htr hk
    have hbound : ∀ d ∈ W, |2 * Real.pi * d - 2 * Real.pi * k| < Real.pi := by
      intro d hd
      obtain ⟨s, hs⟩ := hW1 d hd
      rw [hs]
      have := hδlt s
      rw [abs_lt] at this hk ⊢
      constructor <;> linarith
    -- sign of `d - k` from the cross product
    have hsign : ∀ s, (0 < crossv (φ 1) s → k < (α 1 + δ s) / (2 * Real.pi)) ∧
        (crossv (φ 1) s < 0 → (α 1 + δ s) / (2 * Real.pi) < k) := by
      intro s
      obtain ⟨r, hr, e⟩ := (hlift s).2.2 1 h1I
      have hcr := crossv_eq (φ 1) s r _ e
      have hx : θs s 1 - s = α 1 + δ s := by simp only [hθsdef, hδdef]; ring
      rw [hx] at hcr
      have hb := hbound _ (hW2 (s := 0) ⟨le_rfl, by linarith⟩)
      have hb' : |α 1 + δ s - 2 * Real.pi * k| < Real.pi := by
        have := hδlt s
        rw [abs_lt] at this hk ⊢
        constructor <;> linarith
      have hsin : Real.sin (α 1 + δ s) = Real.sin (α 1 + δ s - 2 * Real.pi * k) := by
        rw [show α 1 + δ s - 2 * Real.pi * k = α 1 + δ s + (-k : ℤ) * (2 * Real.pi) by
          push_cast; ring, Real.sin_add_int_mul_two_pi]
      rw [hsin] at hcr
      rw [abs_lt] at hb'
      constructor
      · intro hpos
        rw [lt_div_iff₀ (by linarith)]
        by_contra hle
        push_neg at hle
        have : Real.sin (α 1 + δ s - 2 * Real.pi * k) ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
        nlinarith
      · intro hneg
        rw [div_lt_iff₀ (by linarith)]
        by_contra hle
        push_neg at hle
        have : 0 ≤ Real.sin (α 1 + δ s - 2 * Real.pi * k) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        nlinarith
    have hdetB := hdet
    rw [Matrix.det_fin_two] at hdetB
    have htrB' : (φ 1).trace = φ 1 0 0 + φ 1 1 1 := by simp [Matrix.trace, Fin.sum_univ_two]
    have hdisc : 0 < (φ 1 1 1 - φ 1 0 0) ^ 2 + 4 * φ 1 0 1 * φ 1 1 0 := by
      rw [htrB'] at htr; nlinarith
    -- a direction with positive and one with negative cross product
    have hexists : ∀ x y : ℝ, (0 < φ 1 1 0 * x ^ 2 + (φ 1 1 1 - φ 1 0 0) * x * y - φ 1 0 1 * y ^ 2 →
        ∃ s ∈ Set.Icc 0 (2 * Real.pi), 0 < crossv (φ 1) s) ∧
        (φ 1 1 0 * x ^ 2 + (φ 1 1 1 - φ 1 0 0) * x * y - φ 1 0 1 * y ^ 2 < 0 →
        ∃ s ∈ Set.Icc 0 (2 * Real.pi), crossv (φ 1) s < 0) := by
      intro x y
      have hxy : ∀ h : φ 1 1 0 * x ^ 2 + (φ 1 1 1 - φ 1 0 0) * x * y - φ 1 0 1 * y ^ 2 ≠ 0,
          x ≠ 0 ∨ y ≠ 0 := by
        intro h; by_contra hc; push_neg at hc; apply h; rw [hc.1, hc.2]; ring
      constructor
      · intro hq
        obtain ⟨s, hs, ρ, hρ, hx, hy⟩ := polar x y (hxy hq.ne')
        refine ⟨s, hs, ?_⟩
        rw [hx, hy, crossv_polar] at hq
        exact pos_of_mul_pos_right hq (by positivity)
      · intro hq
        obtain ⟨s, hs, ρ, hρ, hx, hy⟩ := polar x y (hxy hq.ne)
        refine ⟨s, hs, ?_⟩
        rw [hx, hy, crossv_polar] at hq
        by_contra hc; push_neg at hc
        have : 0 ≤ ρ ^ 2 * crossv (φ 1) s := mul_nonneg (by positivity) hc
        linarith
    obtain ⟨x₁, y₁, hq₁⟩ := indef _ _ _ hdisc
    obtain ⟨x₂, y₂, hq₂⟩ := indef (φ 1 0 1) (-(φ 1 1 1 - φ 1 0 0)) (φ 1 1 0) (by nlinarith)
    obtain ⟨s₁, hs₁, hc₁⟩ := (hexists x₁ y₁).1 hq₁
    obtain ⟨s₂, hs₂, hc₂⟩ := (hexists y₂ x₂).2 (by nlinarith)
    have hup := (hsign s₁).1 hc₁
    have hlo := (hsign s₂).2 hc₂
    have hbddA : BddAbove W := ⟨k + 1 / 2, fun d hd => by
      have := hbound d hd; rw [abs_lt] at this
      have : 2 * Real.pi * d < 2 * Real.pi * (k + 1 / 2) := by linarith
      exact (lt_of_mul_lt_mul_left this (by linarith)).le⟩
    have hbddB : BddBelow W := ⟨k - 1 / 2, fun d hd => by
      have := hbound d hd; rw [abs_lt] at this
      have : 2 * Real.pi * (k - 1 / 2) < 2 * Real.pi * d := by linarith
      exact (lt_of_mul_lt_mul_left this (by linarith)).le⟩
    have hsup1 : (k : ℝ) < sSup W := lt_csSup_of_lt hbddA (hW2 s₁ hs₁) hup
    have hsup2 : sSup W ≤ k + 1 := csSup_le hne (fun d hd => by
      have := hbound d hd; rw [abs_lt] at this
      have : 2 * Real.pi * d < 2 * Real.pi * (k + 1) := by linarith
      exact (lt_of_mul_lt_mul_left this (by linarith)).le)
    have hinf : sInf W < k := csInf_lt_of_lt hbddB (hW2 s₂ hs₂) hlo
    have hceil : ⌈sSup W⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    unfold czIndexOfPath
    simp only [← hWdef]
    rw [hceil, if_pos (by push_cast; linarith)]
    ring
  · intro htr hk1 hk2
    set p := P 1 0 0
    set q := P 1 0 1
    set u := P 1 1 1
    have hp : 0 < p := by
      have := hdotpos 0 1 h1I; simpa [dotv] using this
    have hu : 0 < u := by
      have := hdotpos (Real.pi / 2) 1 h1I; simpa [dotv] using this
    have hdetP : p * u - q * q = 1 := by
      have hd := hdet
      rw [hB, Matrix.det_mul, Matrix.det_fin_two (rotationMatrix _), Matrix.det_fin_two] at hd
      simp [rotationMatrix] at hd
      rw [hsym] at hd
      have hcs := Real.sin_sq_add_cos_sq (α 1)
      nlinarith
    set τ := p + u with hτ
    have hτpos : 0 < τ := by linarith
    have hτ2 : 2 ≤ τ := by nlinarith [sq_nonneg (p - u), sq_nonneg q]
    set β := Real.arccos (2 / τ) with hβdef
    have h2τ : 2 / τ ≤ 1 := by rw [div_le_one hτpos]; exact hτ2
    have h2τ0 : 0 < 2 / τ := by positivity
    have hcβ : Real.cos β = 2 / τ := Real.cos_arccos (by linarith) h2τ
    have hβ0 : 0 ≤ β := Real.arccos_nonneg _
    have hβ1 : β ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 h2τ0.le
    -- `|δ s| ≤ β`
    have hδβ : ∀ s, |δ s| ≤ β := by
      intro s
      have hz := hzne s 1 h1I
      have hd := hdotpos s 1 h1I
      have hcosδ : Real.cos (δ s) = dotv (P 1) s / ‖zv (P 1) s‖ := by
        simp only [hδdef]; rw [Complex.cos_arg hz, zv_re]
      have hnorm : ‖zv (P 1) s‖ ^ 2 = dotv (P 1) s ^ 2 + crossv (P 1) s ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, zv_re, zv_im]; ring
      have hid : dotv (P 1) s ^ 2 + crossv (P 1) s ^ 2 = τ * dotv (P 1) s - 1 := by
        have hE := Real.sin_sq_add_cos_sq s
        simp only [dotv, crossv, hτ]
        rw [hsym]
        linear_combination
          ((p * Real.cos s + q * Real.sin s) ^ 2 + (q * Real.cos s + u * Real.sin s) ^ 2 - 1) * hE -
            (Real.sin s ^ 2 + Real.cos s ^ 2) * hdetP
      have hnpos : 0 < ‖zv (P 1) s‖ := norm_pos_iff.2 hz
      have hge : 2 * ‖zv (P 1) s‖ ≤ τ * dotv (P 1) s := by
        nlinarith [sq_nonneg (τ * dotv (P 1) s - 2)]
      have hcos_ge : 2 / τ ≤ Real.cos (δ s) := by
        rw [hcosδ, div_le_div_iff₀ hτpos hnpos]; linarith
      by_contra hcon
      push_neg at hcon
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 (by linarith [hδlt s]) hcon
      rw [Real.cos_abs, hcβ] at this
      linarith
    -- `γ = α 1 - 2πk ∈ (β, 2π - β)`
    have hcosα : Real.cos (α 1) < 2 / τ := by
      rw [htrB] at htr
      rw [lt_div_iff₀ hτpos]; linarith
    have hcosγ : Real.cos (α 1 - 2 * Real.pi * k) = Real.cos (α 1) := by
      rw [show α 1 - 2 * Real.pi * k = α 1 + (-k : ℤ) * (2 * Real.pi) by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
    have hγ1 : β < α 1 - 2 * Real.pi * k := by
      by_contra hcon; push_neg at hcon
      have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hcon
      rw [hcβ, hcosγ] at this; linarith
    have hγ2 : α 1 - 2 * Real.pi * k < 2 * Real.pi - β := by
      by_contra hcon; push_neg at hcon
      have := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * Real.pi - (α 1 - 2 * Real.pi * k))
        (by linarith) (by linarith) (by linarith : 2 * Real.pi - (α 1 - 2 * Real.pi * k) ≤ β)
      rw [hcβ, Real.cos_two_pi_sub, hcosγ] at this; linarith
    have hlowd : ∀ d ∈ W, (α 1 - β) / (2 * Real.pi) ≤ d := by
      intro d hd
      obtain ⟨s, hs⟩ := hW1 d hd
      have := hδβ s; rw [abs_le] at this
      rw [div_le_iff₀ (by linarith)]; linarith
    have hupd : ∀ d ∈ W, d ≤ (α 1 + β) / (2 * Real.pi) := by
      intro d hd
      obtain ⟨s, hs⟩ := hW1 d hd
      have := hδβ s; rw [abs_le] at this
      rw [le_div_iff₀ (by linarith)]; linarith
    have hbddA : BddAbove W := ⟨_, hupd⟩
    have hk' : (k : ℝ) < (α 1 - β) / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    have hk'' : (α 1 + β) / (2 * Real.pi) < k + 1 := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    have hinf : (k : ℝ) < sInf W := lt_of_lt_of_le hk' (le_csInf hne hlowd)
    have hsup1 : (k : ℝ) < sSup W := by
      obtain ⟨d, hd⟩ := hne
      exact lt_of_lt_of_le (lt_of_lt_of_le hk' (hlowd d hd)) (le_csSup hbddA hd)
    have hsup2 : sSup W ≤ k + 1 := (csSup_le hne hupd).trans hk''.le
    have hceil : ⌈sSup W⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    unfold czIndexOfPath
    simp only [← hWdef]
    rw [hceil, if_neg (by push_cast; linarith)]
    ring

end CZB2

open HryniewiczCriterion

theorem solution (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1)) (h0 : φ 0 = 1)
    (hdet : (φ 1).det = 1) (α : ℝ → ℝ) (hα : IsPolarAngleLift φ α) (k : ℤ) :
    (2 < (φ 1).trace → |α 1 - 2 * Real.pi * k| < Real.pi / 2 → czIndexOfPath φ = 2 * k) ∧
    ((φ 1).trace < 2 → 2 * Real.pi * k < α 1 → α 1 < 2 * Real.pi * k + 2 * Real.pi →
      czIndexOfPath φ = 2 * k + 1) :=
  CZB2.czIndexOfPath_eq_of_polarAngleLift φ hc h0 hdet α hα k
