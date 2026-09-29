-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/642afd33-98d8-5ef4-a025-02be69bb035a

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open WithZero

noncomputable section

namespace WhittakerEntryFormula

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev Fv : Type := v.adicCompletion ℚ

private abbrev mat (g : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v) := (g : Matrix (Fin 2) (Fin 2) (Fv v))

private def rowMax (g : GL (Fin 2) (Fv v)) : ℤᵐ⁰ := max (Valued.v (mat v g 1 0)) (Valued.v (mat v g 1 1))

private def ell (g : GL (Fin 2) (Fv v)) : Fv v :=
  if Valued.v (mat v g 1 1) ≤ Valued.v (mat v g 1 0) then mat v g 0 0 / mat v g 1 0 else mat v g 0 1 / mat v g 1 1

private def mTwo (g : GL (Fin 2) (Fv v)) : ℤ := -WithZero.log (rowMax v g)

private def mOne (g : GL (Fin 2) (Fv v)) : ℤ := -WithZero.log (Valued.v (mat v g).det) - mTwo v g

private def W (χ : AddChar (Fv v) ℂ) (z N lam om : ℂ) (g : GL (Fin 2) (Fv v)) : ℂ :=
  χ (ell v g) * z ^ mTwo v g * torusFactor N lam om (mOne v g - mTwo v g)

private theorem mat_mul (g k : GL (Fin 2) (Fv v)) (i j : Fin 2) :
    mat v (g * k) i j = mat v g i 0 * mat v k 0 j + mat v g i 1 * mat v k 1 j := by
  simp [mat, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_ne_zero (g : GL (Fin 2) (Fv v)) : (mat v g).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero

private theorem valued_det_ne_zero (g : GL (Fin 2) (Fv v)) : Valued.v (mat v g).det ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (det_ne_zero v g)

private theorem det_eq (g : GL (Fin 2) (Fv v)) :
    (mat v g).det = mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0 := Matrix.det_fin_two _

private theorem rowMax_ne_zero (g : GL (Fin 2) (Fv v)) : rowMax v g ≠ 0 := by
  intro h
  rw [rowMax] at h
  obtain ⟨hc, hd⟩ := max_le_iff.1 h.le
  have h0 : mat v g 1 0 = 0 := (Valuation.zero_iff _).1 (le_antisymm hc zero_le')
  have h1 : mat v g 1 1 = 0 := (Valuation.zero_iff _).1 (le_antisymm hd zero_le')
  exact det_ne_zero v g (by rw [det_eq, h0, h1]; ring)

private theorem rowMax_eq_of_le (g : GL (Fin 2) (Fv v)) (h : Valued.v (mat v g 1 1) ≤ Valued.v (mat v g 1 0)) :
    rowMax v g = Valued.v (mat v g 1 0) := by
  unfold rowMax; exact max_eq_left h

private theorem rowMax_eq_of_le' (g : GL (Fin 2) (Fv v)) (h : Valued.v (mat v g 1 0) ≤ Valued.v (mat v g 1 1)) :
    rowMax v g = Valued.v (mat v g 1 1) := by
  unfold rowMax; exact max_eq_right h

private theorem valued_sub_le (g : GL (Fin 2) (Fv v)) {s t s' t' : Fv v}
    (h : mat v g 1 0 * s + mat v g 1 1 * t = 1) (h' : mat v g 1 0 * s' + mat v g 1 1 * t' = 1)
    (hs : Valued.v s ≤ (rowMax v g)⁻¹) (ht : Valued.v t ≤ (rowMax v g)⁻¹)
    (hs' : Valued.v s' ≤ (rowMax v g)⁻¹) (ht' : Valued.v t' ≤ (rowMax v g)⁻¹) :
    Valued.v ((mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s' + mat v g 0 1 * t')) ≤
      Valued.v (mat v g).det / rowMax v g ^ 2 := by
  have hβ : rowMax v g ≠ 0 := rowMax_ne_zero v g
  have hdet : (mat v g).det = mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0 := det_eq v g
  have hts : Valued.v (t - t') ≤ (rowMax v g)⁻¹ := (Valuation.map_sub _ _ _).trans (max_le ht ht')
  have hss : Valued.v (s - s') ≤ (rowMax v g)⁻¹ := (Valuation.map_sub _ _ _).trans (max_le hs hs')
  rcases le_total (Valued.v (mat v g 1 1)) (Valued.v (mat v g 1 0)) with hdc | hcd
  ·
    have hβc : rowMax v g = Valued.v (mat v g 1 0) := rowMax_eq_of_le v g hdc
    have hc : mat v g 1 0 ≠ 0 := fun hc0 => hβ (by rw [hβc, hc0, map_zero])
    have hkey : (mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s' + mat v g 0 1 * t') =
        -((t - t') * (mat v g).det / mat v g 1 0) := by
      rw [hdet]
      field_simp
      linear_combination mat v g 0 0 * (h - h')
    rw [hβc] at hts ⊢
    rw [hkey, Valuation.map_neg, map_div₀, map_mul]
    calc Valued.v (t - t') * Valued.v (mat v g).det / Valued.v (mat v g 1 0)
        = Valued.v (t - t') * (Valued.v (mat v g).det / Valued.v (mat v g 1 0)) := mul_div_assoc _ _ _
      _ ≤ (Valued.v (mat v g 1 0))⁻¹ * (Valued.v (mat v g).det / Valued.v (mat v g 1 0)) :=
          mul_le_mul_left hts _
      _ = Valued.v (mat v g).det / Valued.v (mat v g 1 0) ^ 2 := by
          rw [pow_two, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; exact mul_left_comm _ _ _
  ·
    have hβd : rowMax v g = Valued.v (mat v g 1 1) := rowMax_eq_of_le' v g hcd
    have hd : mat v g 1 1 ≠ 0 := fun hd0 => hβ (by rw [hβd, hd0, map_zero])
    have hkey : (mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s' + mat v g 0 1 * t') =
        (s - s') * (mat v g).det / mat v g 1 1 := by
      rw [hdet, eq_div_iff hd]
      linear_combination mat v g 0 1 * (h - h')
    rw [hβd] at hss ⊢
    rw [hkey, map_div₀, map_mul]
    calc Valued.v (s - s') * Valued.v (mat v g).det / Valued.v (mat v g 1 1)
        = Valued.v (s - s') * (Valued.v (mat v g).det / Valued.v (mat v g 1 1)) := mul_div_assoc _ _ _
      _ ≤ (Valued.v (mat v g 1 1))⁻¹ * (Valued.v (mat v g).det / Valued.v (mat v g 1 1)) :=
          mul_le_mul_left hss _
      _ = Valued.v (mat v g).det / Valued.v (mat v g 1 1) ^ 2 := by
          rw [pow_two, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; exact mul_left_comm _ _ _

private theorem ell_spec (g : GL (Fin 2) (Fv v)) :
    ∃ s t : Fv v, mat v g 1 0 * s + mat v g 1 1 * t = 1 ∧ Valued.v s ≤ (rowMax v g)⁻¹ ∧
      Valued.v t ≤ (rowMax v g)⁻¹ ∧ ell v g = mat v g 0 0 * s + mat v g 0 1 * t := by
  have hβ : rowMax v g ≠ 0 := rowMax_ne_zero v g
  unfold ell
  split_ifs with hdc
  · have hβc : rowMax v g = Valued.v (mat v g 1 0) := rowMax_eq_of_le v g hdc
    have hc : mat v g 1 0 ≠ 0 := fun h0 => hβ (by rw [hβc, h0, map_zero])
    refine ⟨(mat v g 1 0)⁻¹, 0, by rw [mul_inv_cancel₀ hc, mul_zero, add_zero], ?_, ?_,
      by rw [div_eq_mul_inv, mul_zero, add_zero]⟩
    · rw [map_inv₀, hβc]
    · rw [map_zero]; exact zero_le'
  · have hβd : rowMax v g = Valued.v (mat v g 1 1) := rowMax_eq_of_le' v g (not_le.1 hdc).le
    have hd : mat v g 1 1 ≠ 0 := fun h0 => hβ (by rw [hβd, h0, map_zero])
    refine ⟨0, (mat v g 1 1)⁻¹, by rw [mul_inv_cancel₀ hd, mul_zero, zero_add], ?_, ?_,
      by rw [div_eq_mul_inv, mul_zero, zero_add]⟩
    · rw [map_zero]; exact zero_le'
    · rw [map_inv₀, hβd]

private theorem chi_eq_chi_ell (χ : AddChar (Fv v) ℂ) (hχ : ∀ x : Fv v, Valued.v x ≤ 1 → χ x = 1)
    (g : GL (Fin 2) (Fv v)) (hdom : mTwo v g ≤ mOne v g) {s t : Fv v}
    (h : mat v g 1 0 * s + mat v g 1 1 * t = 1) (hs : Valued.v s ≤ (rowMax v g)⁻¹)
    (ht : Valued.v t ≤ (rowMax v g)⁻¹) :
    χ (mat v g 0 0 * s + mat v g 0 1 * t) = χ (ell v g) := by
  obtain ⟨s₀, t₀, h₀, hs₀, ht₀, hℓ⟩ := ell_spec v g
  have hβ2 : rowMax v g ^ 2 ≠ 0 := pow_ne_zero 2 (rowMax_ne_zero v g)
  have hratio : Valued.v (mat v g).det / rowMax v g ^ 2 ≤ 1 := by
    rw [← WithZero.log_le_log (div_ne_zero (valued_det_ne_zero v g) hβ2) one_ne_zero, WithZero.log_one,
      WithZero.log_div (valued_det_ne_zero v g) hβ2, WithZero.log_pow]
    unfold mOne mTwo at hdom
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    omega
  have hχ0 : χ ((mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s₀ + mat v g 0 1 * t₀)) = 1 :=
    hχ _ ((valued_sub_le v g h h₀ hs ht hs₀ ht₀).trans hratio)
  rw [hℓ]
  calc χ (mat v g 0 0 * s + mat v g 0 1 * t)
      = χ (((mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s₀ + mat v g 0 1 * t₀)) +
          (mat v g 0 0 * s₀ + mat v g 0 1 * t₀)) := by rw [sub_add_cancel]
    _ = χ ((mat v g 0 0 * s + mat v g 0 1 * t) - (mat v g 0 0 * s₀ + mat v g 0 1 * t₀)) *
          χ (mat v g 0 0 * s₀ + mat v g 0 1 * t₀) := AddChar.map_add_eq_mul _ _ _
    _ = χ (mat v g 0 0 * s₀ + mat v g 0 1 * t₀) := by rw [hχ0, one_mul]

private theorem mat_unipotent (x : Fv v) : mat v (unipotent x) = !![1, x; 0, 1] := rfl

private theorem mat_scalarPi (π : Fv v) (hπ : π ≠ 0) : mat v (scalarPi π hπ) = !![π, 0; 0, π] := rfl

private theorem mat_diagZ (π : Fv v) (hπ : π ≠ 0) (m : ℤ) : mat v (diagZ π hπ m) = !![π ^ m, 0; 0, 1] := rfl

private theorem mat_one (i j : Fin 2) : mat v 1 i j = (1 : Matrix (Fin 2) (Fin 2) (Fv v)) i j := rfl

private theorem W_unipotent_mul (χ : AddChar (Fv v) ℂ) (z N lam om : ℂ) (x : Fv v) (g : GL (Fin 2) (Fv v)) :
    W v χ z N lam om (unipotent x * g) = χ x * W v χ z N lam om g := by
  have e : ∀ i j : Fin 2, mat v (unipotent x * g) i j = mat v (unipotent x) i 0 * mat v g 0 j +
      mat v (unipotent x) i 1 * mat v g 1 j := mat_mul v _ g
  have e00 : mat v (unipotent x * g) 0 0 = mat v g 0 0 + x * mat v g 1 0 := by rw [e, mat_unipotent]; simp
  have e01 : mat v (unipotent x * g) 0 1 = mat v g 0 1 + x * mat v g 1 1 := by rw [e, mat_unipotent]; simp
  have e10 : mat v (unipotent x * g) 1 0 = mat v g 1 0 := by rw [e, mat_unipotent]; simp
  have e11 : mat v (unipotent x * g) 1 1 = mat v g 1 1 := by rw [e, mat_unipotent]; simp
  have hrow : rowMax v (unipotent x * g) = rowMax v g := by unfold rowMax; rw [e10, e11]
  have hdet : (mat v (unipotent x * g)).det = (mat v g).det := by
    rw [det_eq, det_eq, e00, e01, e10, e11]; ring
  have hm2 : mTwo v (unipotent x * g) = mTwo v g := by unfold mTwo; rw [hrow]
  have hm1 : mOne v (unipotent x * g) = mOne v g := by unfold mOne; rw [hdet, hm2]
  have hβ : rowMax v g ≠ 0 := rowMax_ne_zero v g
  have hell : ell v (unipotent x * g) = ell v g + x := by
    unfold ell
    rw [e00, e01, e10, e11]
    split_ifs with hdc
    · have hc : mat v g 1 0 ≠ 0 := fun h0 => hβ (by rw [rowMax_eq_of_le v g hdc, h0, map_zero])
      field_simp
    · have hd : mat v g 1 1 ≠ 0 := fun h0 =>
        hβ (by rw [rowMax_eq_of_le' v g (not_le.1 hdc).le, h0, map_zero])
      field_simp
  unfold W
  rw [hm1, hm2, hell, AddChar.map_add_eq_mul]
  ring

private theorem valued_mat_le_one {k : GL (Fin 2) (Fv v)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (i j : Fin 2) : Valued.v (mat v k i j) ≤ 1 :=
  ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).1 hk).1.integral i j

private theorem valued_mat_inv_le_one {k : GL (Fin 2) (Fv v)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (i j : Fin 2) : Valued.v (mat v k⁻¹ i j) ≤ 1 :=
  ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).1 hk).2.integral i j

private theorem valued_comb_le {p q u w : Fv v} {γ : ℤᵐ⁰} (hp : Valued.v p ≤ 1) (hq : Valued.v q ≤ 1)
    (hu : Valued.v u ≤ γ) (hw : Valued.v w ≤ γ) : Valued.v (p * u + q * w) ≤ γ := by
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact (mul_le_mul' hp hu).trans (le_of_eq (one_mul γ))
  · rw [map_mul]; exact (mul_le_mul' hq hw).trans (le_of_eq (one_mul γ))

private theorem rowMax_mul_le (g k : GL (Fin 2) (Fv v)) (hk : ∀ i j : Fin 2, Valued.v (mat v k i j) ≤ 1) :
    rowMax v (g * k) ≤ rowMax v g := by
  have key : ∀ j : Fin 2, Valued.v (mat v (g * k) 1 j) ≤ rowMax v g := by
    intro j
    rw [mat_mul, mul_comm (mat v g 1 0), mul_comm (mat v g 1 1)]
    exact valued_comb_le v (hk 0 j) (hk 1 j) (le_max_left _ _) (le_max_right _ _)
  exact max_le (key 0) (key 1)

private theorem rowMax_mul_eq (g : GL (Fin 2) (Fv v)) {k : GL (Fin 2) (Fv v)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) : rowMax v (g * k) = rowMax v g := by
  refine le_antisymm (rowMax_mul_le v g k (valued_mat_le_one v hk)) ?_
  have h := rowMax_mul_le v (g * k) k⁻¹ (valued_mat_inv_le_one v hk)
  rwa [mul_inv_cancel_right] at h

private theorem valued_det_le_one (l : GL (Fin 2) (Fv v)) (hl : ∀ i j : Fin 2, Valued.v (mat v l i j) ≤ 1) :
    Valued.v (mat v l).det ≤ 1 := by
  rw [det_eq]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (hl 0 0) (hl 1 1)
  · rw [map_mul]; exact mul_le_one' (hl 0 1) (hl 1 0)

private theorem valued_det_eq_one {k : GL (Fin 2) (Fv v)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (mat v k).det = 1 := by
  have h1 : Valued.v (mat v k).det ≤ 1 := valued_det_le_one v k (valued_mat_le_one v hk)
  have h2 : Valued.v (mat v k⁻¹).det ≤ 1 := valued_det_le_one v k⁻¹ (valued_mat_inv_le_one v hk)
  have hprod : (mat v k).det * (mat v k⁻¹).det = 1 := by
    rw [← Matrix.det_mul]
    change ((k : Matrix (Fin 2) (Fin 2) (Fv v)) * ((k⁻¹ : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v))).det = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hmul : Valued.v (mat v k).det * Valued.v (mat v k⁻¹).det = 1 := by rw [← map_mul, hprod, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ℤᵐ⁰) = Valued.v (mat v k).det * Valued.v (mat v k⁻¹).det := hmul.symm
    _ ≤ Valued.v (mat v k).det * 1 := mul_le_mul_right h2 _
    _ = Valued.v (mat v k).det := mul_one _

private theorem W_mul_of_mem (χ : AddChar (Fv v) ℂ) (hχ : ∀ x : Fv v, Valued.v x ≤ 1 → χ x = 1) (z N lam om : ℂ)
    {k : GL (Fin 2) (Fv v)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) (g : GL (Fin 2) (Fv v)) :
    W v χ z N lam om (g * k) = W v χ z N lam om g := by
  have hrow : rowMax v (g * k) = rowMax v g := rowMax_mul_eq v g hk
  have hdet : Valued.v (mat v (g * k)).det = Valued.v (mat v g).det := by
    change Valued.v ((g : Matrix (Fin 2) (Fin 2) (Fv v)) * (k : Matrix (Fin 2) (Fin 2) (Fv v))).det = _
    rw [Matrix.det_mul, map_mul, valued_det_eq_one v hk, mul_one]
  have hm2 : mTwo v (g * k) = mTwo v g := by unfold mTwo; rw [hrow]
  have hm1 : mOne v (g * k) = mOne v g := by unfold mOne; rw [hdet, hm2]
  unfold W
  rw [hm1, hm2]
  by_cases hdom : mTwo v g ≤ mOne v g
  · congr 2
    obtain ⟨s, t, hst, hs, ht, hℓ⟩ := ell_spec v (g * k)
    rw [hrow] at hs ht
    have hk' := valued_mat_le_one v hk

    have hfun : mat v (g * k) 0 0 * s + mat v (g * k) 0 1 * t =
        mat v g 0 0 * (mat v k 0 0 * s + mat v k 0 1 * t) + mat v g 0 1 * (mat v k 1 0 * s + mat v k 1 1 * t) := by
      rw [mat_mul, mat_mul]; ring
    have hpair : mat v g 1 0 * (mat v k 0 0 * s + mat v k 0 1 * t) +
        mat v g 1 1 * (mat v k 1 0 * s + mat v k 1 1 * t) = 1 := by
      rw [← hst, mat_mul, mat_mul]; ring
    rw [hℓ, hfun]
    exact chi_eq_chi_ell v χ hχ g hdom hpair (valued_comb_le v (hk' 0 0) (hk' 0 1) hs ht)
      (valued_comb_le v (hk' 1 0) (hk' 1 1) hs ht)
  · have hneg : ¬ (0 : ℤ) ≤ mOne v g - mTwo v g := by omega
    simp only [torusFactor, if_neg hneg, mul_zero]

private theorem not_one_le_zero : ¬ ((1 : ℤᵐ⁰) ≤ 0) := by simp

private theorem W_one (χ : AddChar (Fv v) ℂ) (z N lam om : ℂ) : W v χ z N lam om 1 = 1 := by
  have h01 : mat v 1 0 1 = 0 := by rw [mat_one]; simp
  have h10 : mat v 1 1 0 = 0 := by rw [mat_one]; simp
  have h11 : mat v 1 1 1 = 1 := by rw [mat_one]; simp
  have hrow : rowMax v 1 = 1 := by
    unfold rowMax; rw [h10, h11, map_zero, map_one]; exact max_eq_right zero_le'
  have hdet : (mat v 1).det = 1 := by
    change ((1 : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v)).det = 1
    rw [Units.val_one, Matrix.det_one]
  have hm2 : mTwo v 1 = 0 := by unfold mTwo; rw [hrow, WithZero.log_one, neg_zero]
  have hm1 : mOne v 1 = 0 := by unfold mOne; rw [hdet, map_one, WithZero.log_one, hm2]; simp
  have hell : ell v 1 = 0 := by
    unfold ell; rw [h10, h11, h01, map_zero, map_one, if_neg not_one_le_zero, zero_div]
  unfold W
  rw [hm1, hm2, hell]
  simp [torusFactor, heckeRecursionSeq]

private theorem W_diagZ (χ : AddChar (Fv v) ℂ) (z N lam om : ℂ) {π : Fv v} (hπ : π ≠ 0)
    (hvπ : Valued.v π = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    W v χ z N lam om (diagZ π hπ m) = torusFactor N lam om m := by
  have h00 : mat v (diagZ π hπ m) 0 0 = π ^ m := by rw [mat_diagZ]; simp
  have h01 : mat v (diagZ π hπ m) 0 1 = 0 := by rw [mat_diagZ]; simp
  have h10 : mat v (diagZ π hπ m) 1 0 = 0 := by rw [mat_diagZ]; simp
  have h11 : mat v (diagZ π hπ m) 1 1 = 1 := by rw [mat_diagZ]; simp
  have hrow : rowMax v (diagZ π hπ m) = 1 := by
    unfold rowMax; rw [h10, h11, map_zero, map_one]; exact max_eq_right zero_le'
  have hdet : (mat v (diagZ π hπ m)).det = π ^ m := by rw [det_eq, h00, h01, h10, h11]; ring
  have hm2 : mTwo v (diagZ π hπ m) = 0 := by unfold mTwo; rw [hrow, WithZero.log_one, neg_zero]
  have hm1 : mOne v (diagZ π hπ m) = m := by
    unfold mOne; rw [hdet, map_zpow₀, hvπ, hm2, WithZero.log_zpow, WithZero.log_exp]; simp
  have hell : ell v (diagZ π hπ m) = 0 := by
    unfold ell; rw [h10, h11, h01, map_zero, map_one, if_neg not_one_le_zero, zero_div]
  unfold W
  rw [hm1, hm2, hell, AddChar.map_zero_eq_one, zpow_zero, sub_zero, one_mul, one_mul]

private theorem W_mul_scalarPi (χ : AddChar (Fv v) ℂ) (z : ℂ) (hz : z ≠ 0) (N lam om : ℂ) {π : Fv v} (hπ : π ≠ 0)
    (hvπ : Valued.v π = WithZero.exp (-1 : ℤ)) (g : GL (Fin 2) (Fv v)) :
    W v χ z N lam om (g * scalarPi π hπ) = z * W v χ z N lam om g := by
  have e : ∀ i j : Fin 2, mat v (g * scalarPi π hπ) i j = mat v g i j * π := by
    intro i j
    rw [mat_mul, mat_scalarPi]
    fin_cases j <;> simp
  have hvπ0 : Valued.v π ≠ 0 := by rw [hvπ]; exact WithZero.exp_ne_zero
  have hrow : rowMax v (g * scalarPi π hπ) = rowMax v g * Valued.v π := by
    unfold rowMax; rw [e 1 0, e 1 1, map_mul, map_mul, max_mul_mul_right]
  have hdet : (mat v (g * scalarPi π hπ)).det = (mat v g).det * (π * π) := by
    rw [det_eq, det_eq, e 0 0, e 0 1, e 1 0, e 1 1]; ring
  have hm2 : mTwo v (g * scalarPi π hπ) = mTwo v g + 1 := by
    unfold mTwo; rw [hrow, WithZero.log_mul (rowMax_ne_zero v g) hvπ0, hvπ, WithZero.log_exp]; ring
  have hm1 : mOne v (g * scalarPi π hπ) = mOne v g + 1 := by
    unfold mOne
    rw [hdet, hm2, map_mul, map_mul, WithZero.log_mul (valued_det_ne_zero v g) (mul_ne_zero hvπ0 hvπ0),
      WithZero.log_mul hvπ0 hvπ0, hvπ, WithZero.log_exp]
    ring
  have hiff : ∀ p q : ℤᵐ⁰, p * Valued.v π ≤ q * Valued.v π ↔ p ≤ q := fun p q =>
    ⟨fun h => by simpa [mul_inv_cancel_right₀ hvπ0] using mul_le_mul_left h (Valued.v π)⁻¹,
      fun h => mul_le_mul_left h _⟩
  have hell : ell v (g * scalarPi π hπ) = ell v g := by
    unfold ell
    rw [e 0 0, e 0 1, e 1 0, e 1 1, map_mul, map_mul, mul_div_mul_right _ _ hπ, mul_div_mul_right _ _ hπ]
    simp only [hiff]
  unfold W
  rw [hm1, hm2, hell, zpow_add_one₀ hz, show mOne v g + 1 - (mTwo v g + 1) = mOne v g - mTwo v g by ring]
  ring

end WhittakerEntryFormula

end

open WhittakerEntryFormula in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (hχ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → χ x = 1)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (z : ℂ) (hz : z ≠ 0) (N lam om : ℂ) :
    ∃ W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = χ x * W₂ g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g) ∧
      W₂ 1 = 1 ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W₂ g) ∧
      ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor N lam om m :=
  ⟨W v χ z N lam om, fun x g => W_unipotent_mul v χ z N lam om x g,
    fun _ g hk => W_mul_of_mem v χ hχ z N lam om hk g, W_one v χ z N lam om,
    fun g => W_mul_scalarPi v χ z hz N lam om hπ hϖ g, fun m => W_diagZ v χ z N lam om hπ hϖ m⟩

end S_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero (solution)
