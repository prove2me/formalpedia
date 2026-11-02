-- Prove2me | solution 1 for KontsevichHMS.torus_fukaya_category_exists
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:54:58.205527+00:00
-- url     : https://prove2.me/submissions/5dd9d515-ce70-448c-82b7-132e72f1c52b

import Mathlib
import Definitions.Def_KontsevichHMS_AInfCategory
import Definitions.Def_KontsevichHMS_TorusBrane
/-! Reuses Nickrobbins95 accepted intersection proof dbbea4ee-4f5e-44ea-96a8-e22ac242c171 and coefficient counterexample8d2ad355-6ffc-4c2f-9523-99a063fe2d18. New work below transfers that counterexample to the canonical complex-linear A-infinity existence claim. -/

set_option autoImplicit false

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_ac_eq_iff (x y : ℝ) :
    ((x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ))) ↔ ∃ k : ℤ, x - y = k := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_proj_eq_iff (x y : ℝ × ℝ) :
    proj x = proj y ↔ (∃ k : ℤ, x.1 - y.1 = k) ∧ ∃ k : ℤ, x.2 - y.2 = k := by
  unfold proj
  rw [Prod.mk.injEq, k79522c41_ac_eq_iff, k79522c41_ac_eq_iff]

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_mem_line (b : Brane) (z : Torus) :
    z ∈ b.line ↔ ∃ (t : ℝ) (g : ℤ × ℤ),
      proj (b.base + t • b.dirR + ((g.1 : ℝ), (g.2 : ℝ))) = z := by
  unfold line liftLine
  constructor
  · rintro ⟨x, ⟨t, g, rfl⟩, hx⟩
    exact ⟨t, g, hx⟩
  · rintro ⟨t, g, hx⟩
    exact ⟨_, ⟨t, g, rfl⟩, hx⟩


open KontsevichHMS KontsevichHMS.Brane in
theorem hms_isect_finite_card (b₁ b₂ : Brane) (h : Transverse b₁ b₂) :
    ∃ hfin : (isect b₁ b₂).Finite,
      hfin.toFinset.card = (b₁.dir.1 * b₂.dir.2 - b₁.dir.2 * b₂.dir.1).natAbs := by
  classical
  set D : ℤ := b₁.dir.1 * b₂.dir.2 - b₁.dir.2 * b₂.dir.1 with hDdef
  have hD : (D : ℝ) ≠ 0 := by
    unfold Transverse det2 dirR at h
    rw [hDdef]; push_cast; exact h
  have hD0 : D ≠ 0 := by exact_mod_cast hD
  set c : ℝ := (b₂.base.1 - b₁.base.1) * (b₂.dir.2 : ℝ) - (b₂.base.2 - b₁.base.2) * (b₂.dir.1 : ℝ)
    with hc
  set F : ℤ → Torus := fun j => proj (b₁.base + ((c + j) / (D : ℝ)) • b₁.dirR) with hF
  -- every `F j` is an intersection point
  have h1 : ∀ j : ℤ, F j ∈ isect b₁ b₂ := by
    intro j
    refine ⟨(k79522c41_mem_line b₁ _).2 ⟨(c + j) / (D : ℝ), (0, 0), ?_⟩,
      (k79522c41_mem_line b₂ _).2 ?_⟩
    · simp only [hF]
      congr 1
      ext <;> simp
    · obtain ⟨a, b, hab⟩ := b₂.dir_primitive
      have hab' : (a : ℝ) * b₂.dir.1 + b * b₂.dir.2 = 1 := by exact_mod_cast hab
      refine ⟨-((b₁.dir.1 : ℝ) * (b₂.base.2 - b₁.base.2 + ((-(j * a) : ℤ) : ℝ))
          - (b₁.dir.2 : ℝ) * (b₂.base.1 - b₁.base.1 + ((j * b : ℤ) : ℝ))) / (D : ℝ),
        (j * b, -(j * a)), ?_⟩
      simp only [hF]
      congr 1
      ext
      · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [hDdef] at hD ⊢
        push_cast at hD ⊢
        field_simp
        linear_combination (b₁.dir.1 * (j : ℝ)) * hab'
      · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [hDdef] at hD ⊢
        push_cast at hD ⊢
        field_simp
        linear_combination (b₁.dir.2 * (j : ℝ)) * hab'
  have h2 : ∀ z ∈ isect b₁ b₂, ∃ j : ℤ, F j = z := by
    rintro z ⟨hz1, hz2⟩
    obtain ⟨t1, g1, e1⟩ := (k79522c41_mem_line b₁ z).1 hz1
    obtain ⟨t2, g2, e2⟩ := (k79522c41_mem_line b₂ z).1 hz2
    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := (k79522c41_proj_eq_iff _ _).1 (e1.trans e2.symm)
    simp only [dirR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hk1 hk2
    refine ⟨(g2.1 - g1.1 + k1) * b₂.dir.2 - (g2.2 - g1.2 + k2) * b₂.dir.1, ?_⟩
    have ht1 : t1 = (c + (((g2.1 - g1.1 + k1) * b₂.dir.2 - (g2.2 - g1.2 + k2) * b₂.dir.1 : ℤ)
        : ℝ)) / (D : ℝ) := by
      rw [eq_div_iff hD, hc, hDdef]
      push_cast
      linear_combination (b₂.dir.2 : ℝ) * hk1 - (b₂.dir.1 : ℝ) * hk2
    rw [← e1, hF]
    simp only
    rw [← ht1]
    refine (k79522c41_proj_eq_iff _ _).2 ⟨⟨-g1.1, ?_⟩, ⟨-g1.2, ?_⟩⟩
    · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; push_cast; ring
    · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast; ring
  have h3 : ∀ j k : ℤ, F (j + D * k) = F j := by
    intro j k
    simp only [hF]
    refine (k79522c41_proj_eq_iff _ _).2 ⟨⟨k * b₁.dir.1, ?_⟩, ⟨k * b₁.dir.2, ?_⟩⟩
    · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; push_cast; field_simp; ring
    · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast; field_simp; ring
  obtain ⟨a1, b1', hab1⟩ := b₁.dir_primitive
  have hab1' : (a1 : ℝ) * b₁.dir.1 + b1' * b₁.dir.2 = 1 := by exact_mod_cast hab1
  have h4 : ∀ j j' : ℤ, F j = F j' → D ∣ j - j' := by
    intro j j' hjj
    simp only [hF] at hjj
    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := (k79522c41_proj_eq_iff _ _).1 hjj
    simp only [dirR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hk1 hk2
    have hsD : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * D = j - j' := by field_simp; ring
    have hk1' : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * b₁.dir.1 = k1 := by
      linear_combination hk1
    have hk2' : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * b₁.dir.2 = k2 := by
      linear_combination hk2
    have hR : ((j - j' : ℤ) : ℝ) = ((a1 * k1 + b1' * k2 : ℤ) : ℝ) * (D : ℝ) := by
      push_cast
      linear_combination (-1 : ℝ) * hsD + ((a1 : ℝ) * D) * hk1' + ((b1' : ℝ) * D) * hk2'
        - (((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * D) * hab1'
    have hZ : j - j' = (a1 * k1 + b1' * k2) * D := by exact_mod_cast hR
    exact ⟨a1 * k1 + b1' * k2, by rw [hZ]; ring⟩
  set n : ℕ := D.natAbs with hn
  have hset : isect b₁ b₂ = F '' ((Finset.Ico (0:ℤ) (n:ℤ) : Finset ℤ) : Set ℤ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, rfl⟩ := h2 z hz
      refine ⟨j % D, ?_, ?_⟩
      · simp only [Finset.coe_Ico, Set.mem_Ico]
        refine ⟨Int.emod_nonneg _ hD0, ?_⟩
        exact Int.emod_lt j hD0
      · have := h3 (j % D) (j / D)
        rw [Int.emod_add_mul_ediv] at this
        exact this.symm
    · rintro ⟨j, -, rfl⟩
      exact h1 j
  have hinj : Set.InjOn F ((Finset.Ico (0:ℤ) (n:ℤ) : Finset ℤ) : Set ℤ) := by
    intro j hj j' hj' hjj
    simp only [Finset.coe_Ico, Set.mem_Ico] at hj hj'
    have hdvd := h4 j j' hjj
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    omega
  have hfin : (isect b₁ b₂).Finite := by
    rw [hset]
    exact (Finset.finite_toSet _).image F
  refine ⟨hfin, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfin, hset, hinj.ncard_image,
    Set.ncard_coe_finset, Int.card_Ico]
  simp

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

set_option autoImplicit false
namespace HMSTransfer
universe u
variable {R : Type*} [CommRing R] (C : AInfCategory.{u} R)

theorem m_zero_slot (L K : List C.A) : C.m (L ++ (0 : C.A) :: K) = 0 := by
  simpa using C.m_smul L K (0 : R) (0 : C.A)

theorem m_two_assoc (a b c : C.A)
    (ha : C.m [a] = 0) (hb : C.m [b] = 0) (hc : C.m [c] = 0)
    (habc : C.m [a,b,c] = 0) :
    C.m [C.m [a,b],c] = C.m [a,C.m [b,c]] := by
  have hs := C.stasheff [a,b,c] (by simp)
  have h13 : Finset.Icc (1 : ℕ) 3 = {1,2,3} := by decide
  have h12 : Finset.Icc (1 : ℕ) 2 = {1,2} := by decide
  norm_num [Finset.sum_range_succ, h13, h12] at hs
  have z1 := m_zero_slot C [] [b,c]
  have z2 := m_zero_slot C [a] [c]
  have z3 := m_zero_slot C [a,b] []
  have z4 := m_zero_slot C [] []
  simp only [List.nil_append, List.cons_append, List.nil_append] at z1 z2 z3 z4
  rw [ha,hb,hc,habc,z1,z2,z3,z4] at hs
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using hs

theorem m_one_zero (X Y : C.Obj) (d : ℤ) (a : C.A)
    (ha : a ∈ C.homDeg X Y d) (hz : C.homDeg X Y (d+1) = ⊥) : C.m [a] = 0 := by
  have hh := C.m_hom [a] (fun n => if n = 0 then X else Y) (by
    intro i
    fin_cases i
    simpa using ha.1)
  have hg := C.m_gr [a] [d] (List.Forall₂.cons ha.2 List.Forall₂.nil)
  have hm : C.m [a] ∈ C.homDeg X Y (d+1) := by
    refine ⟨by simpa using hh, ?_⟩
    convert hg using 1 <;> simp <;> ring
  rw [hz] at hm
  simpa using hm

def mTwoLeft (b : C.A) : C.A →ₗ[R] C.A where
  toFun a := C.m [a,b]
  map_add' a a' := C.m_add [] [b] a a'
  map_smul' r a := C.m_smul [] [b] r a

def mTwoRight (a : C.A) : C.A →ₗ[R] C.A where
  toFun b := C.m [a,b]
  map_add' b b' := C.m_add [a] [] b b'
  map_smul' r b := C.m_smul [a] [] r b

theorem map_finsupp_eq_sum {I : Type*} [Fintype I]
    (ψ : (I →₀ R) →ₗ[R] C.A) (v : I →₀ R) :
    ψ v = ∑ i, v i • ψ (Finsupp.single i 1) := by
  classical
  calc ψ v = ψ (∑ i, Finsupp.single i (v i)) := by rw [Finsupp.univ_sum_single]
       _ = ∑ i, v i • ψ (Finsupp.single i 1) := by
         rw [map_sum]
         apply Finset.sum_congr rfl
         intro i _
         rw [← map_smul]
         congr 1
         simp

theorem mTwo_expand_left {I : Type*} [Fintype I]
    (ψ : (I →₀ R) →ₗ[R] C.A) (v : I →₀ R) (b : C.A) :
    C.m [ψ v,b] = ∑ i, v i • C.m [ψ (Finsupp.single i 1),b] :=
  map_finsupp_eq_sum C ((mTwoLeft C b).comp ψ) v

theorem mTwo_expand_right {I : Type*} [Fintype I]
    (ψ : (I →₀ R) →ₗ[R] C.A) (v : I →₀ R) (a : C.A) :
    C.m [a,ψ v] = ∑ i, v i • C.m [a,ψ (Finsupp.single i 1)] :=
  map_finsupp_eq_sum C ((mTwoRight C a).comp ψ) v

theorem coefficient_assoc {I J K : Type*} [Fintype I] [Fintype J]
    (ψ : (I →₀ R) →ₗ[R] C.A) (χ : (J →₀ R) →ₗ[R] C.A)
    (ω : (K →₀ R) →ₗ[R] C.A) (hω : Function.Injective ω)
    (a b c : C.A) (v : I →₀ R) (w : J →₀ R)
    (p : I → K →₀ R) (q : J → K →₀ R)
    (hab : C.m [a,b] = ψ v) (hbc : C.m [b,c] = χ w)
    (hp : ∀ i, C.m [ψ (Finsupp.single i 1),c] = ω (p i))
    (hq : ∀ j, C.m [a,χ (Finsupp.single j 1)] = ω (q j))
    (hassoc : C.m [C.m [a,b],c] = C.m [a,C.m [b,c]]) (k : K) :
    (∑ i, v i * p i k) = ∑ j, w j * q j k := by
  classical
  have hleft : C.m [C.m [a,b],c] = ω (∑ i, v i • p i) := by
    rw [hab, mTwo_expand_left C, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp, map_smul]
  have hright : C.m [a,C.m [b,c]] = ω (∑ j, w j • q j) := by
    rw [hbc, mTwo_expand_right C, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hq, map_smul]
  have he := hω (hleft.symm.trans (hassoc.trans hright))
  have hk := congrArg (fun t : K →₀ R => t k) he
  simpa [Finset.sum_apply] using hk

theorem m_three_zero (X Y Z W : C.Obj) (d e f : ℤ) (a b c : C.A)
    (ha : a ∈ C.homDeg X Y d) (hb : b ∈ C.homDeg Y Z e)
    (hc : c ∈ C.homDeg Z W f)
    (hz : C.homDeg X W (d+e+f-1) = ⊥) : C.m [a,b,c] = 0 := by
  have hh := C.m_hom [a,b,c] (fun n => if n = 0 then X else
      if n = 1 then Y else if n = 2 then Z else W) (by
    intro i
    fin_cases i
    · simpa using ha.1
    · simpa using hb.1
    · simpa using hc.1)
  have hg := C.m_gr [a,b,c] [d,e,f]
    (List.Forall₂.cons ha.2 (List.Forall₂.cons hb.2 (List.Forall₂.cons hc.2 List.Forall₂.nil)))
  have hm : C.m [a,b,c] ∈ C.homDeg X W (d+e+f-1) := by
    refine ⟨by simpa using hh, ?_⟩
    convert hg using 1 <;> simp <;> ring
  rw [hz] at hm
  simpa using hm

end HMSTransfer

namespace HMSFukayaTransfer
open KontsevichHMS KontsevichHMS.Brane KHMSCex HMSTransfer

noncomputable def coefficientVector {I : Type} [Fintype I] (f : I → ℂ) : I →₀ ℂ :=
  Finsupp.onFinset Finset.univ f (by simp)

theorem no_category_at_sixteen :
    ¬ (∃ (C : AInfCategory.{0} ℂ) (ι : Brane → C.Obj) (e : C.Obj → C.A)
      (ψ : ∀ b₁ b₂ : Brane, (↥(isect b₁ b₂) →₀ ℂ) →ₗ[ℂ] C.A),
      C.IsStrictlyUnital e ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ →
        Function.Injective (ψ b₁ b₂) ∧
          LinearMap.range (ψ b₁ b₂) = C.homDeg (ι b₁) (ι b₂) (maslov b₁ b₂)) ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ → ∀ d : ℤ, d ≠ maslov b₁ b₂ →
        C.homDeg (ι b₁) (ι b₂) d = ⊥) ∧
      (∀ b₁ b₂ b₃ : Brane, Transverse b₁ b₂ → Transverse b₂ b₃ → Transverse b₁ b₃ →
        ∀ (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (ξ : ↥(isect b₁ b₃) →₀ ℂ),
          (∀ r, ξ r = mTwoCoeff 16 b₁ b₂ b₃ p q r) →
          C.m [ψ b₁ b₂ (Finsupp.single p 1), ψ b₂ b₃ (Finsupp.single q 1)] = ψ b₁ b₃ ξ)) := by
  classical
  rintro ⟨C,ι,e,ψ,_hu,hr,hother,hprod⟩
  letI : Fintype ↥(isect B1 B3) := (hms_isect_finite_card B1 B3 t13).1.fintype
  letI : Fintype ↥(isect B2 B4) := (hms_isect_finite_card B2 B4 t24).1.fintype
  letI : Fintype ↥(isect B1 B4) := (hms_isect_finite_card B1 B4 t14).1.fintype
  let p : ↥(isect B1 B2) := ⟨_,p12_mem⟩
  let q : ↥(isect B2 B3) := ⟨_,q23_mem⟩
  let s : ↥(isect B3 B4) := ⟨_,q34_mem⟩
  let u : ↥(isect B1 B4) := ⟨_,u14_mem⟩
  let a := ψ B1 B2 (Finsupp.single p 1)
  let b := ψ B2 B3 (Finsupp.single q 1)
  let c := ψ B3 B4 (Finsupp.single s 1)
  have d12 : maslov B1 B2 = 1 := by norm_num [maslov,B1,B2]
  have d23 : maslov B2 B3 = 0 := by norm_num [maslov,B2,B3]
  have d34 : maslov B3 B4 = 0 := by norm_num [maslov,B3,B4]
  have d14 : maslov B1 B4 = 1 := by norm_num [maslov,B1,B4]
  have mem_range (X Y : Brane) (ht : Transverse X Y) (v : ↥(isect X Y) →₀ ℂ) :
      ψ X Y v ∈ C.homDeg (ι X) (ι Y) (maslov X Y) := by
    rw [← (hr X Y ht).2]
    exact ⟨v,rfl⟩
  have ha : a ∈ C.homDeg (ι B1) (ι B2) 1 := by
    simpa only [d12] using mem_range B1 B2 t12 (Finsupp.single p 1)
  have hb : b ∈ C.homDeg (ι B2) (ι B3) 0 := by
    simpa only [d23] using mem_range B2 B3 t23 (Finsupp.single q 1)
  have hc : c ∈ C.homDeg (ι B3) (ι B4) 0 := by
    simpa only [d34] using mem_range B3 B4 t34 (Finsupp.single s 1)
  have ha0 : C.m [a] = 0 := m_one_zero C _ _ 1 a ha (by
    simpa using hother B1 B2 t12 2 (by rw [d12]; norm_num))
  have hb0 : C.m [b] = 0 := m_one_zero C _ _ 0 b hb (by
    simpa using hother B2 B3 t23 1 (by rw [d23]; norm_num))
  have hc0 : C.m [c] = 0 := m_one_zero C _ _ 0 c hc (by
    simpa using hother B3 B4 t34 1 (by rw [d34]; norm_num))
  have habc0 : C.m [a,b,c] = 0 := m_three_zero C _ _ _ _ 1 0 0 a b c ha hb hc (by
    simpa using hother B1 B4 t14 0 (by rw [d14]; norm_num))
  have hassoc := m_two_assoc C a b c ha0 hb0 hc0 habc0
  let v := coefficientVector (fun r : ↥(isect B1 B3) => mTwoCoeff 16 B1 B2 B3 p q r)
  let w := coefficientVector (fun r : ↥(isect B2 B4) => mTwoCoeff 16 B2 B3 B4 q s r)
  let P := fun r : ↥(isect B1 B3) =>
    coefficientVector (fun z : ↥(isect B1 B4) => mTwoCoeff 16 B1 B3 B4 r s z)
  let Q := fun r : ↥(isect B2 B4) =>
    coefficientVector (fun z : ↥(isect B1 B4) => mTwoCoeff 16 B1 B2 B4 p r z)
  have hab : C.m [a,b] = ψ B1 B3 v := hprod B1 B2 B3 t12 t23 t13 p q v (fun _ => rfl)
  have hbc : C.m [b,c] = ψ B2 B4 w := hprod B2 B3 B4 t23 t34 t24 q s w (fun _ => rfl)
  have hp (r : ↥(isect B1 B3)) :
      C.m [ψ B1 B3 (Finsupp.single r 1),c] = ψ B1 B4 (P r) :=
    hprod B1 B3 B4 t13 t34 t14 r s (P r) (fun _ => rfl)
  have hq (r : ↥(isect B2 B4)) :
      C.m [a,ψ B2 B4 (Finsupp.single r 1)] = ψ B1 B4 (Q r) :=
    hprod B1 B2 B4 t12 t24 t14 p r (Q r) (fun _ => rfl)
  have H := coefficient_assoc C (ψ B1 B3) (ψ B2 B4) (ψ B1 B4) (hr B1 B4 t14).1
    a b c v w P Q hab hbc hp hq hassoc u
  have Heq :
      ∑' r : ↥(isect B1 B3), mTwoCoeff 16 B1 B2 B3 p q r * mTwoCoeff 16 B1 B3 B4 r s u =
      ∑' r : ↥(isect B2 B4), mTwoCoeff 16 B2 B3 B4 q s r * mTwoCoeff 16 B1 B2 B4 p r u := by
    simpa [v,w,P,Q,coefficientVector,tsum_fintype] using H
  have e1 := mTwo_eq B1 B2 B3 rfl rfl rfl
  have e2 := mTwo_eq B1 B3 B4 rfl rfl rfl
  have e3 := mTwo_eq B2 B3 B4 rfl rfl rfl
  have e4 := mTwo_eq B1 B2 B4 rfl rfl rfl
  simp only [e1,e2,e3,e4] at Heq
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_tsum, Complex.ofReal_inj] at Heq
  apply final_ineq
  calc Real.exp (-1) * Real.exp (-1) ≤ _ := lhs_ge
       _ = _ := Heq
       _ ≤ _ := rhs_le

end HMSFukayaTransfer


open KontsevichHMS KontsevichHMS.Brane in
theorem solution : ¬ (∀ (area : ℝ) (harea : 0 < area),
∃ (C : AInfCategory.{0} ℂ) (ι : Brane → C.Obj) (e : C.Obj → C.A)
      (ψ : ∀ b₁ b₂ : Brane, (↥(isect b₁ b₂) →₀ ℂ) →ₗ[ℂ] C.A),
      C.IsStrictlyUnital e ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ →
        Function.Injective (ψ b₁ b₂) ∧
          LinearMap.range (ψ b₁ b₂) = C.homDeg (ι b₁) (ι b₂) (maslov b₁ b₂)) ∧
      (∀ b₁ b₂ : Brane, Transverse b₁ b₂ → ∀ d : ℤ, d ≠ maslov b₁ b₂ →
        C.homDeg (ι b₁) (ι b₂) d = ⊥) ∧
      (∀ b₁ b₂ b₃ : Brane, Transverse b₁ b₂ → Transverse b₂ b₃ → Transverse b₁ b₃ →
        ∀ (p : ↥(isect b₁ b₂)) (q : ↥(isect b₂ b₃)) (ξ : ↥(isect b₁ b₃) →₀ ℂ),
          (∀ r, ξ r = mTwoCoeff area b₁ b₂ b₃ p q r) →
          C.m [ψ b₁ b₂ (Finsupp.single p 1), ψ b₂ b₃ (Finsupp.single q 1)] = ψ b₁ b₃ ξ)) := by
  intro h
  exact HMSFukayaTransfer.no_category_at_sixteen (h 16 (by norm_num))

#print axioms solution
