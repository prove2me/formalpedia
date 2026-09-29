-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c38c8bef-276f-5529-9148-f43fc6433aaf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem

set_option autoImplicit false

noncomputable section

namespace H90Section

open Matrix

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

def cj (m : M2) : M2 := m.map (starRingEnd ℂ)

theorem cj_apply (m : M2) (i j : Fin 2) : cj m i j = (starRingEnd ℂ) (m i j) := rfl

theorem cj_mul (m n : M2) : cj (m * n) = cj m * cj n := Matrix.map_mul

theorem cj_add (m n : M2) : cj (m + n) = cj m + cj n := by
  ext i j; simp [cj]

theorem cj_smul (a : ℂ) (m : M2) : cj (a • m) = (starRingEnd ℂ a) • cj m := by
  ext i j; simp [cj]

theorem cj_one : cj 1 = 1 := by
  ext i j; simp [cj, Matrix.one_apply]

theorem cj_cj (m : M2) : cj (cj m) = m := by
  ext i j; simp [cj]

theorem continuous_cj : Continuous cj :=
  continuous_id.matrix_map Complex.continuous_conj

def bmat (lam : ℂ) (q : M2) : M2 := lam • (1 : M2) + (starRingEnd ℂ lam) • q

theorem continuous_bmat (lam : ℂ) : Continuous (bmat lam) := by
  unfold bmat; fun_prop

theorem mul_cj_bmat (q : M2) (hq : q * cj q = 1) (lam : ℂ) : q * cj (bmat lam q) = bmat lam q := by
  rw [bmat, cj_add, cj_smul, cj_smul, cj_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hq]
  simp only [starRingEnd_apply, star_star]
  rw [add_comm]

theorem cj_mul_eq_self (x xinv q b : M2) (hx : x * xinv = 1) (hq : xinv * cj x = q) (hb : q * cj b = b) :
    cj (x * b) = x * b := by
  rw [cj_mul]
  calc cj x * cj b = x * xinv * cj x * cj b := by rw [hx, Matrix.one_mul]
    _ = x * (xinv * cj x) * cj b := by rw [Matrix.mul_assoc x]
    _ = x * (q * cj b) := by rw [hq, Matrix.mul_assoc]
    _ = x * b := by rw [hb]

theorem det_smul_one_add (q : M2) (ω : ℂ) :
    Matrix.det (ω • (1 : M2) + q) = ω ^ 2 + Matrix.trace q * ω + Matrix.det q := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.one_apply]
  ring

theorem exists_det_ne_zero (q : M2) (ω₁ ω₂ ω₃ : ℂ) (h12 : ω₁ ≠ ω₂) (h13 : ω₁ ≠ ω₃) (h23 : ω₂ ≠ ω₃) :
    Matrix.det (ω₁ • (1 : M2) + q) ≠ 0 ∨ Matrix.det (ω₂ • (1 : M2) + q) ≠ 0 ∨
      Matrix.det (ω₃ • (1 : M2) + q) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [det_smul_one_add] at h1 h2 h3
  have e12 : (ω₁ - ω₂) * (ω₁ + ω₂ + Matrix.trace q) = 0 := by linear_combination h1 - h2
  have e13 : (ω₁ - ω₃) * (ω₁ + ω₃ + Matrix.trace q) = 0 := by linear_combination h1 - h3
  have a12 : ω₁ + ω₂ + Matrix.trace q = 0 := (mul_eq_zero.1 e12).resolve_left (sub_ne_zero.2 h12)
  have a13 : ω₁ + ω₃ + Matrix.trace q = 0 := (mul_eq_zero.1 e13).resolve_left (sub_ne_zero.2 h13)
  exact h23 (by linear_combination a12 - a13)

theorem bmat_eq_smul (lam ω : ℂ) (h : starRingEnd ℂ lam * ω = lam) (q : M2) :
    bmat lam q = (starRingEnd ℂ lam) • (ω • (1 : M2) + q) := by
  rw [bmat, smul_add, smul_smul, h]

theorem det_bmat (lam ω : ℂ) (h : starRingEnd ℂ lam * ω = lam) (q : M2) :
    Matrix.det (bmat lam q) = (starRingEnd ℂ lam) ^ 2 * Matrix.det (ω • (1 : M2) + q) := by
  rw [bmat_eq_smul lam ω h, Matrix.det_smul, Fintype.card_fin]

def lam₁ : ℂ := 1
def lam₂ : ℂ := Complex.I
def lam₃ : ℂ := (3 + 4 * Complex.I) / 5
def ω₁ : ℂ := 1
def ω₂ : ℂ := -1
def ω₃ : ℂ := (-7 + 24 * Complex.I) / 25

theorem h₁ : starRingEnd ℂ lam₁ * ω₁ = lam₁ := by simp [lam₁, ω₁]
theorem h₂ : starRingEnd ℂ lam₂ * ω₂ = lam₂ := by simp [lam₂, ω₂]
theorem h₃ : starRingEnd ℂ lam₃ * ω₃ = lam₃ := by
  simp only [lam₃, ω₃, starRingEnd_apply]
  rw [Complex.ext_iff]
  constructor <;> simp <;> norm_num
theorem lam₁_ne : starRingEnd ℂ lam₁ ≠ 0 := by simp [lam₁]
theorem lam₂_ne : starRingEnd ℂ lam₂ ≠ 0 := by simp [lam₂, Complex.I_ne_zero]
theorem lam₃_ne : starRingEnd ℂ lam₃ ≠ 0 := by
  simp only [lam₃, starRingEnd_apply, ne_eq, star_eq_zero, div_eq_zero_iff]
  push Not
  refine ⟨?_, by norm_num⟩
  intro h
  have := congrArg Complex.re h
  simp at this
theorem ω₁₂ : ω₁ ≠ ω₂ := by simp [ω₁, ω₂]; norm_num
theorem ω₁₃ : ω₁ ≠ ω₃ := by
  intro h; have := congrArg Complex.re h; simp [ω₁, ω₃] at this; norm_num at this
theorem ω₂₃ : ω₂ ≠ ω₃ := by
  intro h; have := congrArg Complex.re h; simp [ω₂, ω₃] at this; norm_num at this

theorem exists_det_bmat_ne_zero (q : M2) :
    Matrix.det (bmat lam₁ q) ≠ 0 ∨ Matrix.det (bmat lam₂ q) ≠ 0 ∨ Matrix.det (bmat lam₃ q) ≠ 0 := by
  rw [det_bmat lam₁ ω₁ h₁, det_bmat lam₂ ω₂ h₂, det_bmat lam₃ ω₃ h₃]
  rcases exists_det_ne_zero q ω₁ ω₂ ω₃ ω₁₂ ω₁₃ ω₂₃ with h | h | h
  · exact Or.inl (mul_ne_zero (pow_ne_zero _ lam₁_ne) h)
  · exact Or.inr (Or.inl (mul_ne_zero (pow_ne_zero _ lam₂_ne) h))
  · exact Or.inr (Or.inr (mul_ne_zero (pow_ne_zero _ lam₃_ne) h))

def F (q : M2) : ℝ :=
  max ‖Matrix.det (bmat lam₁ q)‖ (max ‖Matrix.det (bmat lam₂ q)‖ ‖Matrix.det (bmat lam₃ q)‖)

theorem continuous_F : Continuous F := by
  unfold F
  have hd : ∀ lam : ℂ, Continuous fun q : M2 => ‖Matrix.det (bmat lam q)‖ := fun lam =>
    ((continuous_bmat lam).matrix_det).norm
  exact (hd _).max ((hd _).max (hd _))

theorem F_pos (q : M2) : 0 < F q := by
  unfold F
  rcases exists_det_bmat_ne_zero q with h | h | h
  · exact lt_max_of_lt_left (norm_pos_iff.2 h)
  · exact lt_max_of_lt_right (lt_max_of_lt_left (norm_pos_iff.2 h))
  · exact lt_max_of_lt_right (lt_max_of_lt_right (norm_pos_iff.2 h))

theorem continuousOn_inv_bmat (lam : ℂ) (S : Set M2) (hS : ∀ q ∈ S, Matrix.det (bmat lam q) ≠ 0) :
    ContinuousOn (fun q => (bmat lam q)⁻¹) S := by
  have e : (fun q => (bmat lam q)⁻¹) = fun q => Ring.inverse (Matrix.det (bmat lam q)) • (bmat lam q).adjugate := by
    funext q; rw [Matrix.inv_def]
  rw [e]
  refine ContinuousOn.fun_smul ?_ ?_
  · have e2 : (fun q => Ring.inverse (Matrix.det (bmat lam q))) = fun q => (Matrix.det (bmat lam q))⁻¹ := by
      funext q; rw [Ring.inverse_eq_inv']
    rw [e2]
    exact ((continuous_bmat lam).matrix_det.continuousOn).inv₀ hS
  · exact ((continuous_bmat lam).matrix_adjugate).continuousOn

end H90Section

end

open H90Section in
theorem solution
    (B : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hB : IsCompact B) :
    ∃ K : Set (GL (Fin 2) ℂ), IsCompact K ∧
      ∀ x : GL (Fin 2) ℂ,
        ((x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) ∈ B →
        ∃ m k : GL (Fin 2) ℂ,
          ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = m ∧ k ∈ K ∧ x = m * k := by
  classical

  obtain ⟨mlow, hmpos, hmle⟩ : ∃ mlow : ℝ, 0 < mlow ∧ ∀ q ∈ B, mlow ≤ F q := by
    by_cases hne : B.Nonempty
    · obtain ⟨q₀, hq₀, hmin⟩ := hB.exists_isMinOn hne continuous_F.continuousOn
      exact ⟨F q₀, F_pos q₀, fun q hq => hmin hq⟩
    · refine ⟨1, one_pos, fun q hq => ?_⟩
      exact absurd ⟨q, hq⟩ hne

  set Bj : ℂ → Set M2 := fun lam => B ∩ {q | mlow ≤ ‖Matrix.det (bmat lam q)‖} with hBj
  have hBjc : ∀ lam, IsCompact (Bj lam) := fun lam =>
    hB.inter_right (isClosed_le continuous_const ((continuous_bmat lam).matrix_det.norm))
  have hBjdet : ∀ lam, ∀ q ∈ Bj lam, Matrix.det (bmat lam q) ≠ 0 := fun lam q hq =>
    norm_pos_iff.1 (lt_of_lt_of_le hmpos hq.2)
  set N₁ : Set M2 := ((fun q => (bmat lam₁ q)⁻¹) '' Bj lam₁) ∪ ((fun q => (bmat lam₂ q)⁻¹) '' Bj lam₂) ∪
    ((fun q => (bmat lam₃ q)⁻¹) '' Bj lam₃) with hN₁
  set N₂ : Set M2 := (bmat lam₁ '' B) ∪ (bmat lam₂ '' B) ∪ (bmat lam₃ '' B) with hN₂
  have hN₁c : IsCompact N₁ :=
    (((hBjc _).image_of_continuousOn (continuousOn_inv_bmat _ _ (hBjdet _))).union
      ((hBjc _).image_of_continuousOn (continuousOn_inv_bmat _ _ (hBjdet _)))).union
      ((hBjc _).image_of_continuousOn (continuousOn_inv_bmat _ _ (hBjdet _)))
  have hN₂c : IsCompact N₂ :=
    ((hB.image (continuous_bmat _)).union (hB.image (continuous_bmat _))).union (hB.image (continuous_bmat _))
  set K : Set (GL (Fin 2) ℂ) :=
    (Units.embedProduct (Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹' (N₁ ×ˢ (MulOpposite.op '' N₂)) with hK
  have hKc : IsCompact K :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hN₁c.prod (hN₂c.image MulOpposite.continuous_op))
  refine ⟨K, hKc, fun x hx => ?_⟩

  set q : M2 := ((x⁻¹ : GL (Fin 2) ℂ) : M2) * cj ((x : GL (Fin 2) ℂ) : M2) with hq
  have hqB : q ∈ B := hx
  have hxinv : ((x : GL (Fin 2) ℂ) : M2) * ((x⁻¹ : GL (Fin 2) ℂ) : M2) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinvx : ((x⁻¹ : GL (Fin 2) ℂ) : M2) * ((x : GL (Fin 2) ℂ) : M2) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hqq : q * cj q = 1 := by
    rw [hq, cj_mul, cj_cj]
    have e : cj ((x : GL (Fin 2) ℂ) : M2) * cj ((x⁻¹ : GL (Fin 2) ℂ) : M2) = 1 := by
      rw [← cj_mul, hxinv, cj_one]
    calc ((x⁻¹ : GL (Fin 2) ℂ) : M2) * cj ((x : GL (Fin 2) ℂ) : M2) *
          (cj ((x⁻¹ : GL (Fin 2) ℂ) : M2) * ((x : GL (Fin 2) ℂ) : M2))
        = ((x⁻¹ : GL (Fin 2) ℂ) : M2) * (cj ((x : GL (Fin 2) ℂ) : M2) * cj ((x⁻¹ : GL (Fin 2) ℂ) : M2)) *
            ((x : GL (Fin 2) ℂ) : M2) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, Matrix.mul_one, hinvx]

  obtain ⟨lam, hlamB, hlam3⟩ : ∃ lam : ℂ, q ∈ Bj lam ∧ (lam = lam₁ ∨ lam = lam₂ ∨ lam = lam₃) := by
    have hF := hmle q hqB
    simp only [F, le_max_iff] at hF
    rcases hF with h | h | h
    · exact ⟨lam₁, ⟨hqB, h⟩, Or.inl rfl⟩
    · exact ⟨lam₂, ⟨hqB, h⟩, Or.inr (Or.inl rfl)⟩
    · exact ⟨lam₃, ⟨hqB, h⟩, Or.inr (Or.inr rfl)⟩
  have hdet : Matrix.det (bmat lam q) ≠ 0 := hBjdet lam q hlamB
  set u : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (bmat lam q) hdet with hu
  have hu_val : ((u : GL (Fin 2) ℂ) : M2) = bmat lam q := rfl
  have hu_inv : ((u⁻¹ : GL (Fin 2) ℂ) : M2) = (bmat lam q)⁻¹ := by
    rw [Matrix.coe_units_inv, hu_val]
  refine ⟨x * u, u⁻¹, ?_, ?_, by group⟩
  ·
    rw [Units.val_mul, hu_val]
    exact cj_mul_eq_self _ _ q _ hxinv rfl (mul_cj_bmat q hqq lam)
  ·
    show Units.embedProduct (Matrix (Fin 2) (Fin 2) ℂ) u⁻¹ ∈ N₁ ×ˢ (MulOpposite.op '' N₂)
    refine ⟨?_, ⟨bmat lam q, ?_, ?_⟩⟩
    · show ((u⁻¹ : GL (Fin 2) ℂ) : M2) ∈ N₁
      rw [hu_inv]
      rcases hlam3 with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨q, hlamB, rfl⟩)
      · exact Or.inl (Or.inr ⟨q, hlamB, rfl⟩)
      · exact Or.inr ⟨q, hlamB, rfl⟩
    · rcases hlam3 with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨q, hqB, rfl⟩)
      · exact Or.inl (Or.inr ⟨q, hqB, rfl⟩)
      · exact Or.inr ⟨q, hqB, rfl⟩
    · show MulOpposite.op (bmat lam q) = MulOpposite.op (((u⁻¹)⁻¹ : GL (Fin 2) ℂ) : M2)
      rw [inv_inv, hu_val]

end S_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem (solution)
