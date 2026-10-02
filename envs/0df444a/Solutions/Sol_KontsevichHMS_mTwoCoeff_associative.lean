-- Prove2me | solution 1 for KontsevichHMS.mTwoCoeff_associative
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:56:51.463407+00:00
-- url     : https://prove2.me/submissions/8d2ad355-6ffc-4c2f-9523-99a063fe2d18

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

set_option autoImplicit false

namespace KHMSCex

open scoped Real
open KontsevichHMS KontsevichHMS.Brane

/-! ## Circle and lattice helpers -/

lemma coe_int_sub {x y : ℝ} (h : (x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ))) :
    ∃ n : ℤ, x = y + n := by
  have h2 : ((x - y : ℝ) : AddCircle (1:ℝ)) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).1 h2
  refine ⟨n, ?_⟩
  simp at hn
  linarith

lemma coe_shift (x : ℝ) (k : ℤ) :
    (((x + k : ℝ)) : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) := by
  rw [AddCircle.coe_add]
  have : ((k : ℝ) : AddCircle (1:ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).2 ⟨k, by simp⟩
  rw [this, add_zero]

lemma proj_int {x y : ℝ × ℝ} (h : proj x = proj y) :
    ∃ m n : ℤ, x.1 = y.1 + m ∧ x.2 = y.2 + n := by
  simp only [proj, Prod.mk.injEq] at h
  obtain ⟨m, hm⟩ := coe_int_sub h.1
  obtain ⟨n, hn⟩ := coe_int_sub h.2
  exact ⟨m, n, hm, hn⟩

lemma proj_unique {x y : ℝ × ℝ} (h : proj x = proj y)
    (hx1 : x.1 ∈ Set.Ico (0:ℝ) 1) (hx2 : x.2 ∈ Set.Ico (0:ℝ) 1)
    (hy1 : y.1 ∈ Set.Ico (0:ℝ) 1) (hy2 : y.2 ∈ Set.Ico (0:ℝ) 1) : x = y := by
  simp only [proj, Prod.mk.injEq] at h
  have h1 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (by simpa using hx1) (by simpa using hy1)).1 h.1
  have h2 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (by simpa using hx2) (by simpa using hy2)).1 h.2
  exact Prod.ext h1 h2

/-! ## A Gaussian lattice-sum bound -/

lemma geom_hasSum (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun k : ℤ => z ^ (k.natAbs + 1)) (z * (1 + z) / (1 - z)) := by
  have h1 : HasSum (fun n : ℕ => z ^ (n + 1)) (z * (1 - z)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hz0 hz1).mul_left z
    simpa [pow_succ, mul_comm] using this
  have h2 : HasSum (fun n : ℕ => z ^ (n + 2)) (z ^ 2 * (1 - z)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hz0 hz1).mul_left (z ^ 2)
    simpa [pow_add, mul_comm] using this
  have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => z ^ (k.natAbs + 1))
    (by simpa using h1)
    (by
      have e : (fun n : ℕ => z ^ ((-((n : ℤ) + 1)).natAbs + 1)) = fun n : ℕ => z ^ (n + 2) := by
        funext n; congr 1
      show HasSum (fun n : ℕ => z ^ ((-((n : ℤ) + 1)).natAbs + 1)) _
      rw [e]; exact h2)
  have hne : (1 - z) ≠ 0 := by linarith
  convert h using 1
  field_simp

lemma exp_le_pow (c : ℝ) (hc : 0 < c) (k : ℤ) (hk : k ≠ 0) :
    Real.exp (-(c * (k : ℝ) ^ 2)) ≤ Real.exp (-(c / 2)) ^ (k.natAbs + 1) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
    have := Int.one_le_abs hk
    exact_mod_cast this
  have h2 : ((k.natAbs + 1 : ℕ) : ℝ) = |(k:ℝ)| + 1 := by
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  have h3 : (k:ℝ) ^ 2 = |(k:ℝ)| ^ 2 := (sq_abs _).symm
  rw [h3]
  have h4 : |(k:ℝ)| + 1 ≤ 2 * |(k:ℝ)| ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hc.le]

lemma gauss_sum {X : Type} (S : Set X) (F : ℤ → X) (a b : ℤ) (ha : a ≠ 0) (c : ℝ) (hc : 0 < c)
    (wt : X → ℝ)
    (hS : ∀ T ∈ S, ∃ n : ℤ, T = F n ∧ a * n + b ≠ 0)
    (hw : ∀ n : ℤ, wt (F n) = Real.exp (-(c * ((a * n + b : ℤ) : ℝ) ^ 2))) :
    Summable (fun T : S => wt T) ∧
      ∑' T : S, wt T ≤
        Real.exp (-(c / 2)) * (1 + Real.exp (-(c / 2))) / (1 - Real.exp (-(c / 2))) := by
  classical
  choose N hN hN0 using hS
  set z := Real.exp (-(c / 2)) with hz
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hz1 : z < 1 := by
    have := Real.exp_lt_exp.2 (show -(c / 2) < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hg := geom_hasSum z hz0 hz1
  let ι : S → ℤ := fun T => a * N T.1 T.2 + b
  have hι : Function.Injective ι := by
    intro T T' h
    have h' : N T.1 T.2 = N T'.1 T'.2 := by
      have h0 : a * N T.1 T.2 = a * N T'.1 T'.2 := by
        have := h
        simp only [ι] at this
        linarith
      exact mul_left_cancel₀ ha h0
    apply Subtype.ext
    rw [hN T.1 T.2, hN T'.1 T'.2, h']
  have hwT : ∀ T : S, wt T = Real.exp (-(c * ((ι T : ℤ) : ℝ) ^ 2)) := by
    intro T
    rw [hN T.1 T.2]
    exact hw _
  have hle : ∀ T : S, wt T ≤ (fun k : ℤ => z ^ (k.natAbs + 1)) (ι T) := by
    intro T
    rw [hwT T]
    exact exp_le_pow c hc _ (hN0 T.1 T.2)
  have hnn : ∀ T : S, 0 ≤ wt T := by
    intro T; rw [hwT T]; exact (Real.exp_pos _).le
  have hsc : Summable (fun T : S => (fun k : ℤ => z ^ (k.natAbs + 1)) (ι T)) :=
    hg.summable.comp_injective hι
  have hs : Summable (fun T : S => wt T) := Summable.of_nonneg_of_le hnn hle hsc
  refine ⟨hs, ?_⟩
  calc ∑' T : S, wt T ≤ ∑' T : S, (fun k : ℤ => z ^ (k.natAbs + 1)) (ι T) :=
        Summable.tsum_le_tsum hle hs hsc
    _ ≤ ∑' k : ℤ, z ^ (k.natAbs + 1) :=
        tsum_comp_le_tsum_of_inj hg.summable (fun k => pow_nonneg hz0 _) hι
    _ = z * (1 + z) / (1 - z) := hg.tsum_eq

/-! ## The four branes -/

noncomputable def B1 : Brane where
  dir := (1, -1)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (1/2, 0)
  grading := -1/4
  grading_dir := ⟨Real.sqrt 2 / 2, by positivity, by
    have e : π * (-1/4) = -(π/4) := by ring
    rw [e, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ext <;> simp⟩
  conn := 0

noncomputable def B2 : Brane where
  dir := (0, 1)
  dir_primitive := ⟨0, 1, by norm_num⟩
  base := (0, 0)
  grading := 1/2
  grading_dir := ⟨1, one_ne_zero, by
    have e : π * (1/2) = π/2 := by ring
    rw [e, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ext <;> simp⟩
  conn := 0

noncomputable def B3 : Brane where
  dir := (1, 1)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (0, 0)
  grading := 1/4
  grading_dir := ⟨Real.sqrt 2 / 2, by positivity, by
    have e : π * (1/4) = π/4 := by ring
    rw [e, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ext <;> simp⟩
  conn := 0

noncomputable def B4 : Brane where
  dir := (1, 0)
  dir_primitive := ⟨1, 0, by norm_num⟩
  base := (0, 0)
  grading := 0
  grading_dir := ⟨1, one_ne_zero, by
    rw [mul_zero, Real.cos_zero, Real.sin_zero]
    ext <;> simp⟩
  conn := 0

lemma t12 : Transverse B1 B2 := by simp [Transverse, det2, dirR, B1, B2]
lemma t23 : Transverse B2 B3 := by simp [Transverse, det2, dirR, B2, B3]
lemma t34 : Transverse B3 B4 := by simp [Transverse, det2, dirR, B3, B4]
lemma t13 : Transverse B1 B3 := by simp [Transverse, det2, dirR, B1, B3]
lemma t24 : Transverse B2 B4 := by simp [Transverse, det2, dirR, B2, B4]
lemma t14 : Transverse B1 B4 := by simp [Transverse, det2, dirR, B1, B4]

@[simp] lemma B1c : B1.conn = 0 := rfl
@[simp] lemma B2c : B2.conn = 0 := rfl
@[simp] lemma B3c : B3.conn = 0 := rfl
@[simp] lemma B4c : B4.conn = 0 := rfl

/-! ## Points -/

lemma proj_int_pt (x y : ℝ) (m n : ℤ) : proj (x + m, y + n) = proj (x, y) := by
  simp only [proj, coe_shift]

lemma proj_zero_int (n : ℤ) : proj (0, (n:ℝ)) = proj (0, 0) := by
  simpa using proj_int_pt 0 0 0 n

lemma mem_line {b : Brane} {x : ℝ × ℝ} (t : ℝ) (g : ℤ × ℤ)
    (h : x = b.base + t • b.dirR + ((g.1 : ℝ), (g.2 : ℝ))) : proj x ∈ b.line :=
  ⟨x, ⟨t, g, h⟩, rfl⟩

lemma p12_mem : proj (0, 1/2) ∈ isect B1 B2 :=
  ⟨mem_line (-1/2) (0, 0) (by ext <;> simp [B1, dirR] <;> norm_num),
   mem_line (1/2) (0, 0) (by ext <;> simp [B2, dirR])⟩

lemma q23_mem : proj (0, 0) ∈ isect B2 B3 :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B2, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B3, dirR])⟩

lemma q34_mem : proj (0, 0) ∈ isect B3 B4 :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B3, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma q24_mem : proj (0, 0) ∈ isect B2 B4 :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B2, dirR]),
   mem_line 0 (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma u14_mem : proj (1/2, 0) ∈ isect B1 B4 :=
  ⟨mem_line 0 (0, 0) (by ext <;> simp [B1, dirR]),
   mem_line (1/2) (0, 0) (by ext <;> simp [B4, dirR])⟩

lemma r13_mem : proj (1/4, 1/4) ∈ isect B1 B3 :=
  ⟨mem_line (-1/4) (0, 0) (by ext <;> simp [B1, dirR] <;> norm_num),
   mem_line (1/4) (0, 0) (by ext <;> simp [B3, dirR])⟩

/-! ## Real weights -/

noncomputable def wt (T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  Real.exp (-(16 * det2 (T.2.1 - T.1) (T.2.2 - T.1) / 2))

noncomputable def rc (b₁ b₂ b₃ : Brane) (p q r : Torus) : ℝ :=
  ∑' T : ↥(triangles b₁ b₂ b₃ p q r), wt T.1

lemma wt_nonneg (T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) : 0 ≤ wt T := (Real.exp_pos _).le

lemma rc_nonneg (b₁ b₂ b₃ : Brane) (p q r : Torus) : 0 ≤ rc b₁ b₂ b₃ p q r :=
  tsum_nonneg (fun T => wt_nonneg _)

lemma mTwo_eq (b₁ b₂ b₃ : Brane) (h1 : b₁.conn = 0) (h2 : b₂.conn = 0) (h3 : b₃.conn = 0)
    (p q r : Torus) : mTwoCoeff 16 b₁ b₂ b₃ p q r = (rc b₁ b₂ b₃ p q r : ℂ) := by
  unfold mTwoCoeff rc
  rw [Complex.ofReal_tsum]
  congr 1
  funext T
  simp [triangleWeight, wt, h1, h2, h3, Complex.ofReal_exp]

lemma nonempty_of_rc_ne_zero {b₁ b₂ b₃ : Brane} {p q r : Torus} (h : rc b₁ b₂ b₃ p q r ≠ 0) :
    ∃ T, T ∈ triangles b₁ b₂ b₃ p q r := by
  by_contra hne
  push Not at hne
  apply h
  unfold rc
  have : IsEmpty ↥(triangles b₁ b₂ b₃ p q r) := ⟨fun T => hne T.1 T.2⟩
  exact tsum_empty

/-! ## The four triangle families -/

noncomputable def F123 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1/2), (0, (n:ℝ)), ((1/2 - n)/2, (1/2 + n)/2))

noncomputable def F134 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((1/4, 1/4), ((n:ℝ), (n:ℝ)), (1/2 - n, (n:ℝ)))

noncomputable def F234 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 0), ((n:ℝ), (n:ℝ)), (0, (n:ℝ)))

noncomputable def F124 (n : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((0, 1/2), (0, (n:ℝ)), (1/2 - n, (n:ℝ)))

lemma char123 (r : Torus) :
    ∀ T ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F123 n ∧ 2 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B2, B3] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F123] <;> linarith

lemma char134 (r : Torus) :
    ∀ T ∈ triangles B1 B3 B4 (proj (1/4, 1/4)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F134 n ∧ 4 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B3, B4] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F134] <;> linarith

lemma char234 (r : Torus) :
    ∀ T ∈ triangles B2 B3 B4 (proj (0, 0)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F234 n ∧ 1 * n + 0 ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B2, B3, B4] at d1 d2 d3 hm hn
  have hQ1 : Q1 = n := by linarith
  have hQ2 : Q2 = n := by linarith
  have hR1 : R1 = 0 := by linarith
  have hR2 : R2 = n := by linarith
  subst hQ1 hQ2 hR1 hR2
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [det2] at hpos
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F234]

lemma char124 (r : Torus) :
    ∀ T ∈ triangles B1 B2 B4 (proj (0, 1/2)) (proj (0, 0)) r,
      ∃ n : ℤ, T = F124 n ∧ 2 * n + (-1) ≠ 0 := by
  rintro ⟨⟨P1, P2⟩, ⟨Q1, Q2⟩, ⟨R1, R2⟩⟩ ⟨hp, hp1, hp2, hq, hr, d1, d2, d3, hpos⟩
  have hP := proj_unique hp hp1 hp2 (by norm_num) (by norm_num)
  obtain ⟨m, n, hm, hn⟩ := proj_int hq
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  simp [det2, dirR, B1, B2, B4] at d1 d2 d3 hm hn
  refine ⟨n, ?_, by omega⟩
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
    simp [F124] <;> linarith

lemma w123 (n : ℤ) : wt (F123 n) = Real.exp (-(1 * ((2 * n + (-1) : ℤ) : ℝ) ^ 2)) := by
  unfold wt F123 det2
  simp only [Prod.mk_sub_mk]
  congr 1
  push_cast
  ring

lemma w134 (n : ℤ) : wt (F134 n) = Real.exp (-(1 * ((4 * n + (-1) : ℤ) : ℝ) ^ 2)) := by
  unfold wt F134 det2
  simp only [Prod.mk_sub_mk]
  congr 1
  push_cast
  ring

lemma w234 (n : ℤ) : wt (F234 n) = Real.exp (-(8 * ((1 * n + 0 : ℤ) : ℝ) ^ 2)) := by
  unfold wt F234 det2
  simp only [Prod.mk_sub_mk]
  congr 1
  push_cast
  ring

lemma w124 (n : ℤ) : wt (F124 n) = Real.exp (-(2 * ((2 * n + (-1) : ℤ) : ℝ) ^ 2)) := by
  unfold wt F124 det2
  simp only [Prod.mk_sub_mk]
  congr 1
  push_cast
  ring

/-! ## Bounds -/

lemma exp_neg_le_half (x : ℝ) (hx : 1 ≤ x) : Real.exp (-x) ≤ 1/2 := by
  have h1 : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h4 : (Real.exp 1)⁻¹ ≤ 1/2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num; linarith
  linarith

lemma bnd3 (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 1/2) : z * (1 + z) / (1 - z) ≤ 3 * z := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma c123_ge : Real.exp (-1) ≤ rc B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4)) := by
  have hs := (gauss_sum (triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4))) F123 2 (-1) (by norm_num) 1 one_pos wt (char123 _) w123).1
  have hmem : F123 0 ∈ triangles B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) (proj (1/4, 1/4)) := by
    refine ⟨rfl, by norm_num [F123], by norm_num [F123], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [F123, det2, dirR, B1, B2, B3]
  have h := hs.le_tsum ⟨F123 0, hmem⟩ (fun j _ => wt_nonneg _)
  have e : wt (F123 0) = Real.exp (-1) := by rw [w123]; norm_num
  unfold rc
  exact e ▸ h

lemma c134_ge : Real.exp (-1) ≤ rc B1 B3 B4 (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) := by
  have hs := (gauss_sum (triangles B1 B3 B4 (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0))) F134 4 (-1) (by norm_num) 1 one_pos wt (char134 _) w134).1
  have hmem : F134 0 ∈ triangles B1 B3 B4 (proj (1/4, 1/4)) (proj (0, 0)) (proj (1/2, 0)) := by
    refine ⟨rfl, by norm_num [F134], by norm_num [F134], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [F134, det2, dirR, B1, B3, B4]
  have h := hs.le_tsum ⟨F134 0, hmem⟩ (fun j _ => wt_nonneg _)
  have e : wt (F134 0) = Real.exp (-1) := by rw [w134]; norm_num
  unfold rc
  exact e ▸ h

lemma c234_le (w : Torus) : rc B2 B3 B4 (proj (0, 0)) (proj (0, 0)) w ≤ 3 * Real.exp (-4) := by
  have h := (gauss_sum (triangles B2 B3 B4 (proj (0, 0)) (proj (0, 0)) w) F234 1 0 (by norm_num) 8 (by norm_num) wt (char234 w) w234).2
  have e : Real.exp (-(8 / 2 : ℝ)) = Real.exp (-4) := by norm_num
  rw [e] at h
  exact h.trans (bnd3 _ (Real.exp_pos _).le (exp_neg_le_half 4 (by norm_num)))

lemma c124_le (w : Torus) : rc B1 B2 B4 (proj (0, 1/2)) (proj (0, 0)) w ≤ 3 * Real.exp (-1) := by
  have h := (gauss_sum (triangles B1 B2 B4 (proj (0, 1/2)) (proj (0, 0)) w) F124 2 (-1) (by norm_num) 2 (by norm_num) wt (char124 w) w124).2
  have e : Real.exp (-(2 / 2 : ℝ)) = Real.exp (-1) := by norm_num
  rw [e] at h
  exact h.trans (bnd3 _ (Real.exp_pos _).le (exp_neg_le_half 1 le_rfl))

lemma r_cases (n : ℤ) (r : Torus) (h : proj ((1/2 - n)/2, (1/2 + n)/2) = r) :
    r ∈ ({proj (1/4, 1/4), proj (3/4, 3/4)} : Set Torus) := by
  subst h
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    have e : (((1:ℝ)/2 - ((2 * j : ℤ) : ℝ)) / 2, ((1:ℝ)/2 + ((2 * j : ℤ) : ℝ)) / 2)
        = (1/4 + ((-j : ℤ) : ℝ), 1/4 + ((j : ℤ) : ℝ)) := by
      push_cast; ext <;> ring
    rw [e, proj_int_pt]
  · right
    have e : (((1:ℝ)/2 - ((2 * j + 1 : ℤ) : ℝ)) / 2, ((1:ℝ)/2 + ((2 * j + 1 : ℤ) : ℝ)) / 2)
        = (3/4 + ((-j - 1 : ℤ) : ℝ), 3/4 + ((j : ℤ) : ℝ)) := by
      push_cast; ext <;> ring
    rw [Set.mem_singleton_iff, e, proj_int_pt]

lemma lhs_ge : Real.exp (-1) * Real.exp (-1) ≤
    ∑' r : ↥(isect B1 B3), rc B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r *
      rc B1 B3 B4 r (proj (0, 0)) (proj (1/2, 0)) := by
  set g : ↥(isect B1 B3) → ℝ := fun r => rc B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r *
      rc B1 B3 B4 r (proj (0, 0)) (proj (1/2, 0)) with hg
  have hnn : ∀ r, 0 ≤ g r := fun r => mul_nonneg (rc_nonneg _ _ _ _ _ _) (rc_nonneg _ _ _ _ _ _)
  have hsupp : ∀ r : ↥(isect B1 B3), g r ≠ 0 →
      (r : Torus) ∈ ({proj (1/4, 1/4), proj (3/4, 3/4)} : Set Torus) := by
    intro r hr
    have h1 : rc B1 B2 B3 (proj (0, 1/2)) (proj (0, 0)) r ≠ 0 := left_ne_zero_of_mul hr
    obtain ⟨T, hT⟩ := nonempty_of_rc_ne_zero h1
    obtain ⟨n, rfl, -⟩ := char123 r T hT
    exact r_cases n r hT.2.2.2.2.1
  have hs : Summable g := by
    apply summable_of_hasFiniteSupport
    apply ((Set.toFinite ({proj (1/4, 1/4), proj (3/4, 3/4)} : Set Torus)).preimage
      Subtype.val_injective.injOn).subset
    intro r hr
    exact hsupp r hr
  calc Real.exp (-1) * Real.exp (-1) ≤ g ⟨_, r13_mem⟩ :=
        mul_le_mul c123_ge c134_ge (by positivity) (rc_nonneg _ _ _ _ _ _)
    _ ≤ ∑' r, g r := hs.le_tsum _ (fun j _ => hnn j)

lemma rhs_le : ∑' w : ↥(isect B2 B4), rc B2 B3 B4 (proj (0, 0)) (proj (0, 0)) w *
      rc B1 B2 B4 (proj (0, 1/2)) w (proj (1/2, 0)) ≤ (3 * Real.exp (-4)) * (3 * Real.exp (-1)) := by
  rw [tsum_eq_single ⟨proj (0, 0), q24_mem⟩]
  · exact mul_le_mul (c234_le _) (c124_le _) (rc_nonneg _ _ _ _ _ _) (by positivity)
  · intro w hw
    have h0 : rc B2 B3 B4 (proj (0, 0)) (proj (0, 0)) w = 0 := by
      by_contra h0
      obtain ⟨T, hT⟩ := nonempty_of_rc_ne_zero h0
      obtain ⟨n, rfl, -⟩ := char234 w T hT
      apply hw
      apply Subtype.ext
      rw [← hT.2.2.2.2.1]
      exact proj_zero_int n
    rw [h0, zero_mul]

lemma final_ineq : ¬ (Real.exp (-1) * Real.exp (-1) ≤ (3 * Real.exp (-4)) * (3 * Real.exp (-1))) := by
  intro h
  set y := Real.exp (-1) with hy
  have e4 : Real.exp (-4) = y ^ 4 := by rw [hy, ← Real.exp_nat_mul]; norm_num
  rw [e4] at h
  have hy0 : 0 < y := Real.exp_pos _
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hy1 : y * Real.exp 1 = 1 := by rw [hy, ← Real.exp_add]; norm_num
  have hy2 : y < 0.4 := by nlinarith
  have h3 : 1 ≤ 9 * y ^ 3 := by
    have : y ^ 2 * 1 ≤ y ^ 2 * (9 * y ^ 3) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have : y ^ 3 < 0.4 ^ 3 := by gcongr
  norm_num at this
  linarith

theorem cex : ¬ (∀ (area : ℝ) (harea : 0 < area) (b₁ b₂ b₃ b₄ : Brane)
    (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃) (h₃₄ : Transverse b₃ b₄)
    (h₁₃ : Transverse b₁ b₃) (h₂₄ : Transverse b₂ b₄) (h₁₄ : Transverse b₁ b₄)
    (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (s : ↥(isect b₃ b₄)) (u : ↥(isect b₁ b₄)),
    ∑' r : ↥(isect b₁ b₃),
        mTwoCoeff area b₁ b₂ b₃ p q r * mTwoCoeff area b₁ b₃ b₄ r s u
      = ∑' w : ↥(isect b₂ b₄),
        mTwoCoeff area b₂ b₃ b₄ q s w * mTwoCoeff area b₁ b₂ b₄ p w u) := by
  intro h
  have H := h 16 (by norm_num) B1 B2 B3 B4 t12 t23 t34 t13 t24 t14
    ⟨_, p12_mem⟩ ⟨_, q23_mem⟩ ⟨_, q34_mem⟩ ⟨_, u14_mem⟩
  have e1 := mTwo_eq B1 B2 B3 rfl rfl rfl
  have e2 := mTwo_eq B1 B3 B4 rfl rfl rfl
  have e3 := mTwo_eq B2 B3 B4 rfl rfl rfl
  have e4 := mTwo_eq B1 B2 B4 rfl rfl rfl
  simp only [e1, e2, e3, e4] at H
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_tsum, Complex.ofReal_inj] at H
  apply final_ineq
  calc Real.exp (-1) * Real.exp (-1) ≤ _ := lhs_ge
    _ = _ := H
    _ ≤ _ := rhs_le

end KHMSCex

open KontsevichHMS Brane in
theorem solution : ¬ (∀ (area : ℝ) (harea : 0 < area) (b₁ b₂ b₃ b₄ : Brane)
    (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃) (h₃₄ : Transverse b₃ b₄)
    (h₁₃ : Transverse b₁ b₃) (h₂₄ : Transverse b₂ b₄) (h₁₄ : Transverse b₁ b₄)
    (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (s : ↥(isect b₃ b₄)) (u : ↥(isect b₁ b₄)),
    ∑' r : ↥(isect b₁ b₃),
        mTwoCoeff area b₁ b₂ b₃ p q r * mTwoCoeff area b₁ b₃ b₄ r s u
      = ∑' w : ↥(isect b₂ b₄),
        mTwoCoeff area b₂ b₃ b₄ q s w * mTwoCoeff area b₁ b₂ b₄ p w u) := by
  exact KHMSCex.cex
