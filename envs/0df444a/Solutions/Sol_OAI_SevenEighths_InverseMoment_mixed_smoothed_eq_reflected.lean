-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.mixed_smoothed_eq_reflected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:24:51.619256+00:00
-- url     : https://prove2.me/submissions/53bf590d-0c3e-4589-b8f2-349d054343f0

import Mathlib
import Definitions.Def_OAIHecke78B024

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
namespace OAI










open scoped BigOperators

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by
      ext x
      simp
    rw [hshift, gaussSum_one_right hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit

theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl

theorem additive_unit_sum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : F) :
    (∑ y : Fˣ, ψ (a * (y : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hgauss : (∑ y : Fˣ, ψ (a * (y : F))) =
      gaussSum (1 : MulChar F ℂ) (ψ.mulShift a) := by
    rw [gaussSum_eq_units_sum]
    simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
  rw [hgauss]
  split_ifs with ha
  · subst a
    simp only [AddChar.mulShift_zero, gaussSum_one_one]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fˣ))
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have hshift : ψ.mulShift a ≠ 1 := by
      intro heq
      exact hψ ((AddChar.mulShift_unit_eq_one_iff ψ hu).mp heq)
    exact gaussSum_one_left hshift

theorem sextic_fourth_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hexp : ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = 1 := by
    calc
      ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = (χ ^ 6)⁻¹ := by group
      _ = 1 := by rw [hχ, inv_one]
  rw [hexp]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp
    _ = _ := additive_unit_sum ψ hψ a

theorem active_zero_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
  classical
  have hquad : ((χ⁻¹) ^ 2)⁻¹ = χ ^ 2 := by group
  calc
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ ^ 2) (y : F) * ψ ((ε * x) * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
          rw [← hquad, MulChar.inv_apply', inv_inv]
    _ = gaussSum (χ ^ 2) (ψ.mulShift (ε * x)) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
    _ = (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
      rw [gaussSum_mulShift_any (χ ^ 2) ψ hχ₂ (ε * x)]
      rw [map_mul]
      ring

theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h

theorem trivial_fourier_coefficient (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (h : F) :
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
      if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  calc
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
        gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-h)) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = ∑ u : Fˣ, ψ ((-h) * (u : F)) := by
      rw [gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
    _ = if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
      simpa only [neg_eq_zero] using additive_unit_sum ψ hψ (-h)

end ShortDraftLocal


end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftCRT

open AddChar

variable {K : Type*} [Field K]

theorem addChar_crt_pair (ψ : AddChar K ℂ) (m n u v z : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hbez : u * n + v * m = 1) :
    ψ (z / (m * n)) = ψ (u * z / m) * ψ (v * z / n) := by
  rw [← map_add_eq_mul]
  congr 1
  calc
    z / (m * n) = z * (u * n + v * m) / (m * n) := by rw [hbez, mul_one]
    _ = u * z / m + v * z / n := by
      field_simp

theorem normalized_crt_pair {R : Type*} [CommRing R]
    (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam c₀ r d x u w : R)
    (hlam : ι lam ≠ 0) (hc₀ : ι c₀ ≠ 0) (hr : ι r ≠ 0)
    (hbez : u * r + (lam ^ 3 * w) * c₀ = 1) :
    ψ (-(ι d * (ι x / ι lam ^ 4)) / (ι c₀ * ι r)) =
      ψ (-(ι d * ι u * (ι x / ι lam ^ 4)) / ι c₀) *
        ψ (ι (-d * w * x) / (ι lam * ι r)) := by
  have hbezK : ι u * ι r + ι (lam ^ 3 * w) * ι c₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hbez
  have hsplit := addChar_crt_pair ψ (ι c₀) (ι r) (ι u)
    (ι (lam ^ 3 * w)) (-(ι d * (ι x / ι lam ^ 4))) hc₀ hr hbezK
  rw [hsplit]
  congr 1
  · congr 1
    ring
  · congr 1
    simp only [map_mul, map_pow, map_neg]
    field_simp

variable {R : Type*} [CommRing R]

end ShortDraftCRT

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

open AddChar MulChar

open AddChar MulChar

theorem canonical_A5_jfour (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (∑ h : (O ⧸ P)ˣ,
          (((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [ShortDraftLocal.nontrivial_fourier_coefficient (χ ^ 4) ψ hχ4 h,
      map_mul]
    simp only [inv_pow, MulChar.mul_apply]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.sextic_fourth_mask χ ψ hχ6 hψ (ε * x)]
  ring

theorem canonical_A5_jzero_active (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (2:ℕ) ≠ 0) (by decide : (2:ℕ) < 6)
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
        (∑ h : (O ⧸ P)ˣ,
          ((χ⁻¹) ^ 2) (h : O ⧸ P) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hh : (h : O ⧸ P) ≠ 0 := Units.ne_zero h
    rw [pow_zero, ShortDraftLocal.trivial_fourier_coefficient ψ hψ h,
      if_neg hh, map_mul]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.active_zero_local_row χ ψ hχ2 ε x]
  ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ShortDraftLocal

open AddChar MulChar

theorem general_inversion_gauss {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (a : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (y⁻¹)) *
          ψ (a * (y : F)) := by
            apply Fintype.sum_equiv (Equiv.inv Fˣ)
            intro y
            simp
    _ = ∑ y : Fˣ, (χ ^ (j + 2)) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      congr 1
      have hchar : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← hchar, MulChar.inv_apply']
    _ = gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem sextic_fourier_theta_row_general
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχj : χ ^ j ≠ 1) (hχj2 : χ ^ (j + 2) ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        (∑ h : Fˣ,
          (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ j) ψ hχj h, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, general_inversion_gauss χ ψ j (ε * x),
    gaussSum_mulShift_any (χ ^ (j + 2)) ψ hχj2 (ε * x), map_mul]
  ring

end ShortDraftLocal

namespace ActualEisensteinCubic

section

open AddChar MulChar

theorem canonical_A5_nonexceptional (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ)
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχj : χ ^ j ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar hj0 hj6
  have hχj2 : χ ^ (j + 2) ≠ 1 := by
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (3:ℕ) ≠ 0) (by decide : (3:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (5:ℕ) ≠ 0) (by decide : (5:ℕ) < 6)
    · have hχ1 : χ ≠ 1 := by
        simpa only [pow_one, χ] using canonicalSextic_pow_ne_one P hgood hchar
          (by decide : (1:ℕ) ≠ 0) (by decide : (1:ℕ) < 6)
      have hχ7 : χ ^ (5 + 2) = χ := by
        calc
          χ ^ (5 + 2) = χ ^ (6 + 1) := by congr 1
          _ = χ ^ 6 * χ := by rw [pow_add, pow_one]
          _ = χ := by rw [canonicalSextic_pow_six P hgood, one_mul]
      rw [hχ7]
      exact hχ1
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row_general χ ψ j hχj hχj2 σ ε x

end

open ConcreteTraceCRT

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace OscillatoryDeterminant

open Complex

theorem determinant (t a b : ℂ) (hq : q a b ≠ 0) :
    A t a b * D t a b - (B t a b)^2 =
      4/q a b + 3*t^2/4 := by
  dsimp [A, B, D]
  field_simp [hq]
  dsimp [q]
  ring_nf
  simp [Complex.I_sq]
  ring

end OscillatoryDeterminant

open Filter Real Asymptotics

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

end
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert (preTransparency := .instances) ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert (preTransparency := .instances) horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem mellinInv_euler_line_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (mellinEulerData V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section

variable {F : Type*} [Field F] [Fintype F]

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

end

open ActualEisensteinCubic

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

variable {F : Type*} [Field F] [Fintype F]

open ActualEisensteinCubic

attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldNormalized
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeNormalized
theorem canonical_A5_normalized (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    activeRow (canonicalSextic P hgood) ψ j σ ε x =
      (((canonicalSextic P hgood)⁻¹) ^ 2) σ *
        phase (canonicalSextic P hgood) ψ j ε * bracket (canonicalSextic P hgood) j x := by
  let χ := canonicalSextic P hgood
  have hψne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hr : (rootCard (O ⧸ P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard (O ⧸ P) : ℂ) ^ 2 = (Fintype.card (O ⧸ P) : ℂ) := by
    exact_mod_cast (rootCard_sq (F := O ⧸ P))
  by_cases hj0 : j = 0
  · subst j
    have hh := canonical_A5_jzero_active P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [← hsq]
    field_simp
  by_cases hj4 : j = 4
  · subst j
    have hh := canonical_A5_jfour P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    have hqNat : 1 ≤ Fintype.card (O ⧸ P) := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardunits : (Fintype.card (O ⧸ P)ˣ : ℂ) = (Fintype.card (O ⧸ P) : ℂ) - 1 := by
      rw [Fintype.card_units, Nat.cast_sub hqNat, Nat.cast_one]
    have hsum : (if (ε : O ⧸ P) * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1) =
        -1 + (Fintype.card (O ⧸ P) : ℂ) * if x = 0 then 1 else 0 := by
      by_cases hx : x = 0
      · simp [hx, hcardunits]
        ring
      · simp [hx, mul_ne_zero (Units.ne_zero ε) hx]
    rw [hsum]
    simp only [phase, bracket, tau,  ↓reduceIte]
    rw [← hsq]
    field_simp
  · have hh := canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, if_neg hj4, if_neg hj0]
    rw [← hsq]
    field_simp

end LocalReflectionBrackets

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

section

open CompletedDyadic

theorem cusp_coefficient_normalization (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt ((3:ℝ)^m)=(3:ℝ)^(m/6)*(3:ℝ)^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  have hr1 : (3:ℝ)^(m/6)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr2 : (3:ℝ)^(m/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbn : Real.sqrt b≠0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  field_simp

end

open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

theorem idealRowHom_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : ActualEisensteinCubic.O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S x := by
  rw [FiniteGaussPhase.span_finset_prod,map_prod]
  simp only [finiteSquarefreeRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CompletedGauss

open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_principal_global (a c0 r : Eis)
    (ha : lambda^2∣a-1) (hr : lambda^2∣r-1) :
    symbol (c0*r) a=symbol c0 a*symbol a r := by
  rw [symbol_mul_numerator _ _ a ha,
    symbol_reciprocity r a (primary_ne_zero r hr) (primary_ne_zero a ha) hr ha]

theorem A3_ramified_global (a b cprime d u : Eis)
    (hdet : a*d-b*(u*cprime)=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) :
    symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b)*symbol cprime a := by
  have h1 : symbol a (a-u*b)*symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b) := by
    rw [←symbol_mul_numerator _ _ _ hA]
    apply symbol_congr
    refine ⟨u*cprime,?_⟩
    linear_combination -u*hdet
  have h2 : symbol (a-u*b) a*symbol cprime a=1 := by
    rw [←symbol_mul_numerator _ _ _ ha,←symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨cprime-d,?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a-u*b) (primary_ne_zero a ha)
    (primary_ne_zero _ hA) ha hA] at h1
  calc
    _ = (symbol (a-u*b) a*symbol cprime a)*symbol (u*cprime-u*d) (a-u*b) := by rw [h2,one_mul]
    _ = (symbol (a-u*b) a*symbol (u*cprime-u*d) (a-u*b))*symbol cprime a := by ring
    _ = _ := by rw [h1]

theorem A3_ramified_global_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) (hr : lambda^2∣r-1) :
    symbol (u*(c0*r)-u*d) (a-u*b)=
      (symbol (-u) (a-u*b)*symbol c0 a)*symbol a r := by
  rw [A3_ramified_global a b (c0*r) d u hdet ha hA,
    A3_principal_global a c0 r ha hr]
  ring

theorem A3_unramified_global (a b c d : Eis)
    (hdet : a*d-b*c=1) (hb : lambda^2∣(-b)-1) (hc : lambda^2∣c-1)
    (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c := by
  have hp : lambda^2∣((-b)*c)-1 := primary_mul (-b) c hb hc
  have hprod : symbol d (-b)*symbol d c=1 := by
    rw [←symbol_mul_denominator]
    have hnine : (9:Eis)∣(-b)*c-1 := by
      convert (preTransparency := .instances) dvd_neg.mpr h9 using 1
      linear_combination hdet
    have hd : d∣(-b)*c-1 := by
      refine ⟨-a,?_⟩
      linear_combination hdet
    rw [symbol_denominator_congr d ((-b)*c) 1 hp (by simp) hnine hd,symbol_one]
  have hother : symbol a c*symbol d c=1 := by
    rw [←symbol_mul_numerator _ _ _ hc,←symbol_one_numerator c hc]
    apply symbol_congr
    refine ⟨b,?_⟩
    linear_combination hdet
  rw [symbol_neg_numerator _ _ hb]
  calc
    symbol d (-b) = symbol d (-b)*(symbol a c*symbol d c) := by rw [hother,mul_one]
    _ = (symbol d (-b)*symbol d c)*symbol a c := by ring
    _ = symbol a c := by rw [hprod,one_mul]

theorem A3_unramified_global_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hb : lambda^2∣(-b)-1)
    (hc : lambda^2∣c0*r-1) (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c0*symbol a r := by
  rw [A3_unramified_global a b (c0*r) d hdet hb hc h9,symbol_mul_denominator]

end

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_fixed_factor_congr (M c0 u a a0 b b0 : Eis)
    (h9M : (9:Eis)∣M) (hcM : c0∣M) (huM : u∣M)
    (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hA : lambda^2∣a-u*b-1) (hA0 : lambda^2∣a0-u*b0-1)
    (hma : M∣a-a0) (hmb : M∣b-b0) :
    symbol (-u) (a-u*b)*symbol c0 a=
      symbol (-u) (a0-u*b0)*symbol c0 a0 := by
  have hdiff : M∣(a-u*b)-(a0-u*b0) := by
    convert (preTransparency := .instances) dvd_sub hma (dvd_mul_of_dvd_right hmb u) using 1 ; ring
  have hfirst : symbol (-u) (a-u*b)=symbol (-u) (a0-u*b0) := by
    apply symbol_denominator_congr _ _ _ hA hA0 (h9M.trans hdiff)
    exact neg_dvd.mpr (huM.trans hdiff)
  have hsecond := symbol_denominator_congr c0 a a0 ha ha0 (h9M.trans hma) (hcM.trans hma)
  rw [hfirst,hsecond]

end ShortDraftCusp

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_add_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):primeCubicGauss p hp hprimary (e+3) h=primeCubicGauss p hp hprimary e h:=by
  unfold primeCubicGauss
  rw [pow_add,primeCubicMulChar_cube,mul_one]

lemma cubicUnitGaussSum_prime_cube_shift_pos (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(n+4))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^(n+1)):=by
  by_cases hd:p^n∣h
  · obtain ⟨r,rfl⟩:=hd
    have harg:p^n*r*p^3=p^(n+3)*r:=by rw [pow_add];ring
    rw [harg,show n+4=(n+3)+1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n+3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r]
    rw [show n+3+1=(n+1)+3 by omega,primeCubicGauss_add_three,pow_add]
    ring
  · have hlow:cubicUnitGaussSum h (p^(n+1))=0:=by
      by_contra hh
      exact hd (cubicUnitGaussSum_prime_power_support p hp hprimary n h hh)
    have hhigh:cubicUnitGaussSum (h*p^3) (p^(n+4))=0:=by
      by_contra hh
      have hh':cubicUnitGaussSum (h*p^3) (p^((n+3)+1))≠0:=by convert (preTransparency := .instances) hh using 1
      have hd':p^(n+3)∣h*p^3:=cubicUnitGaussSum_prime_power_support p hp hprimary (n+3) (h*p^3) hh'
      have hd'':p^3*p^n∣p^3*h:=by simpa only [pow_add,mul_comm,mul_left_comm,mul_assoc] using hd'
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp hd'')
    rw [hhigh,hlow,mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (k:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(k+3))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^k)-
        if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2 else 0:=by
  cases k with
  | zero=>
    rw [Nat.zero_add,cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p^3) h)]
    have he:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at he ⊢
    rw [he]
    ring
  | succ n=>
    simpa only [show n+1+3=n+4 by omega,Nat.succ_ne_zero,ite_false,sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

private lemma primeExpansionTerm_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (h:Eis) (k:ℕ):
    primeExpansionTerm p s (h*p^3) (k+3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        primeExpansionTerm p s h k-
      if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*unramifiedPrimeDeletedSeries p s h else 0:=by
  have hv:unramifiedPrimeDeletedSeries p s (h*p^3*p^(k+3))=
      unramifiedPrimeDeletedSeries p s (h*p^k):=by
    have he:h*p^3*p^(k+3)=(h*p^k*p^3)*p^3:=by rw [pow_add];ring
    rw [he,unramifiedPrimeDeletedSeries_cube_shift p hp,
      unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h,hv,pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero,mul_one,cubicUnitGaussSum_one]
    ring
  · ring

theorem unramifiedCubicGaussSeries_cube_step (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+3))=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^a)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph (a+3)
  have hold:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph a
  change unramifiedCubicGaussSeries s (h*p^a)=
    ∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a) k at hold
  have harg:h*p^(a+3)=(h*p^a)*p^3:=by rw [pow_add,mul_assoc]
  change unramifiedCubicGaussSeries s (h*p^(a+3))=
    ∑k∈Finset.range (a+3+2),primeExpansionTerm p s (h*p^(a+3)) k at he
  rw [show a+3+2=3+(a+2) by omega,Finset.sum_range_add,harg] at he
  have hsmall:∑k∈Finset.range 3,primeExpansionTerm p s (h*p^a*p^3) k=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    have hg1:cubicUnitGaussSum (h*p^a*p^3) p=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ hp.ne_zero
        ((dvd_pow_self p (by decide:3≠0)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    have hg2:cubicUnitGaussSum (h*p^a*p^3) (p^2)=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
        ((pow_dvd_pow p (by omega:2≤3)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,primeExpansionTerm,
      pow_zero,pow_one,cubicUnitGaussSum_one,mul_one,one_mul,zero_add,hg1,hg2,
      mul_zero,zero_mul,add_zero]
    rw [unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hsmall] at he
  have htail:∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a*p^3) (3+k)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedPrimeDeletedSeries p s (h*p^a):=by
    simp_rw [show ∀k:ℕ,3+k=k+3 by omega,primeExpansionTerm_cube_shift p hp hprimary]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←hold]
    simp
  rw [htail,←harg] at he
  exact he.trans (by ring)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

local instance instFintypeUnitsO_3_rf3572b_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [if_neg (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [if_pos hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.BesselReflection
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace CompletedGauss

section
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem squarefree_cube_decomposition_unique {I J I' J':Ideal Eis}
    (hJ:J≠0) (hJ':J'≠0) (hI:Squarefree I) (hI':Squarefree I')
    (h:I*J^3=I'*J'^3) : I=I' ∧ J=J' := by
  have hf:=congrArg normalizedFactors h
  rw [normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    normalizedFactors_pow,normalizedFactors_pow] at hf
  have hi:=(squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi':=(squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P:Ideal Eis) :
      (normalizedFactors I).count P=(normalizedFactors I').count P ∧
      (normalizedFactors J).count P=(normalizedFactors J').count P := by
    have he:=congrArg (Multiset.count P) hf
    simp only [Multiset.count_add,Multiset.count_nsmul] at he
    have h1:=Multiset.nodup_iff_count_le_one.mp hi P
    have h2:=Multiset.nodup_iff_count_le_one.mp hi' P
    omega
  constructor
  · calc
      I=(normalizedFactors I).prod:=(Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _=(normalizedFactors I').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).1))
      _=I':=Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J=(normalizedFactors J).prod:=(Ideal.prod_normalizedFactors_eq_self hJ).symm
      _=(normalizedFactors J').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).2))
      _=J':=Ideal.prod_normalizedFactors_eq_self hJ'

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (_hh:h≠0) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=unramifiedGaussResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,unramifiedGaussResidue_prime_cube p hp hprimary _,
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem unramifiedGaussResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=unramifiedGaussResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    unramifiedGaussResidue_prime_cube p hp hprimary _] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem unramifiedGaussResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=
      if n%3=0 then unramifiedGaussResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [unramifiedGaussResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact unramifiedGaussResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,unramifiedGaussResidue_prime_square p hp hprimary h hph]

end

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaBesselScale_pos : 0<thetaBesselScale := norm_pos_iff.mpr thetaFrequencyScale_ne_zero

lemma thetaBesselScale_eq : thetaBesselScale=1/Real.sqrt 27 := by
  have hl : ‖eisLam‖^2=(3:ℝ) := by
    have h := congrArg norm TraceLambdaPhase.eisLam_sq
    norm_num only [norm_pow,norm_neg,Complex.norm_ofNat] at h
    exact h
  have hd : ‖(3:ℂ)*eisLam‖=Real.sqrt 27 := by
    rw [norm_mul,Complex.norm_ofNat]
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤27 by norm_num),
      Real.sqrt_nonneg (27:ℝ),norm_nonneg eisLam]
  rw [thetaBesselScale,thetaFrequencyScale,norm_div,norm_one,hd]

lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedBesselValue_prime_power_vanish (side:Bool) (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    ramifiedBesselValue side (h*p^k)=0 := by
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hr:ramifiedArithmeticResidue side (h*p^k) hf=0:=by
      unfold ramifiedArithmeticResidue
      apply Finset.sum_eq_zero
      intro i hi
      rw [ramifiedSixIndex_multiplier]
      have hc:IsCoprime ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i)) p:=
        (ramified_primary_coprime (ramifiedSixUnit side i) (ramifiedSixPower i) p hpp).of_mul_left_right
      have hnot:¬p∣((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h:=by
        intro hd
        rcases hp.dvd_mul.mp hd with hd|hd
        · exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)
        · exact hph hd
      rw [←mul_assoc,unramifiedGaussResidue_prime_power_table p hp hpp _ hnot,hk]
      norm_num
    rw [hr,mul_zero,zero_div]
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedFunction_valuation_ne_two (F:Eis→ℂ)
    (hzero:∀(p:Eis),Prime p→lambda^2∣p-1→∀h:Eis,¬p∣h→∀k:ℕ,k%3=2→F (h*p^k)=0)
    (I P:Ideal Eis) (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (u:Eisˣ) (m:ℕ) (hF:F ((u.val*lambda^m)*primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hbase:¬p∣(u.val*lambda^m)*primaryGenerator J:=by
    intro hd
    rcases hp.dvd_mul.mp hd with hd|hd
    · exact hp.not_isUnit (((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right).symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hF
  rw [hgen,show (u.val*lambda^m)*(p^(multiplicity P I)*primaryGenerator J)=
    ((u.val*lambda^m)*primaryGenerator J)*p^(multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm

theorem ramifiedBesselValue_squarefree_cube_support (side:Bool) (h:Eis) (hh:h≠0)
    (hB:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (ramifiedBesselValue side)
      (fun p hp hpp h hph k hk=>ramifiedBesselValue_prime_power_vanish side p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma onceCuspScale_not_three_dvd (t:Eisˣ) : ¬(3:Eis)∣onceCuspScale t := by
  rintro ⟨z,hz⟩
  have hq:Ideal.absNorm (Ideal.span {onceCuspScale t})=3:=by
    simpa only [Fin.val_zero,pow_zero,mul_one] using onceCusp_q_absNorm t 0
  have he:=congrArg (fun x:Eis=>Ideal.absNorm (Ideal.span {x})) hz
  rw [hq,←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm] at he
  omega

lemma onceCuspScale_lambda_dvd (t:Eisˣ) : lambda∣onceCuspScale t := by
  refine ⟨(t:Eis)*(traceRamifiedUnit:Eis),?_⟩
  rw [onceCuspScale,trace_eq_ramifiedUnit]
  ring

theorem ramifiedBesselValue_exact_lambda_valuation (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) : lambda∣h ∧ ¬lambda^2∣h := by
  have hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side):=by
    by_contra hnot
    exact hb (by simp only [ramifiedBesselValue,dif_neg hnot])
  have hl3:lambda∣(3:Eis):=
    (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  constructor
  · have hd:=hl3.trans hf
    simpa only [sub_add_cancel] using dvd_add hd
      (onceCuspScale_lambda_dvd (ramifiedCuspScaleUnit side))
  · intro h2
    have h3:(3:Eis)∣h:=three_dvd_lambda_sq.trans h2
    have hq:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit side):=by
      convert (preTransparency := .instances) dvd_sub h3 hf using 1 ; ring
    exact onceCuspScale_not_three_dvd _ hq

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_power_vanish (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    sourceResidualFourierCoefficient (h*p^k)=0 := by
  rw [sourceResidualFourierCoefficient,sourceArithmeticResidue_prime_power_table p hp hpp h hph k,hk]
  norm_num

theorem sourceResidualFourierCoefficient_full_squarefree_cube_support (h:Eis) (hh:h≠0)
    (hB:sourceResidualFourierCoefficient h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (sourceResidualFourierCoefficient)
      (fun p hp hpp h hph k hk=>sourceResidualFourierCoefficient_prime_power_vanish p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaPrimaryProduct_injective : Function.Injective thetaPrimaryProduct := by
  intro p q he
  have hprod : p.1.val*p.2.val^3=q.1.val*q.2.val^3 := congrArg Subtype.val he
  have h := squarefree_cube_decomposition_unique
    (primaryGenerator_ne_zero_ideal _ p.2.property)
    (primaryGenerator_ne_zero_ideal _ q.2.property) p.1.property.1 q.1.property.1 hprod
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

lemma thetaFullFrequency_product (p : ThetaFullIndex) :
    thetaFullFrequency p=p.1.val*(lambda^p.2.1*primaryGenerator (thetaPrimaryProduct p.2.2).val) := by
  simp only [thetaFullFrequency,thetaPrimaryProduct,primaryGenerator_mul,primaryGenerator_pow]
  ring

lemma thetaFullFrequency_ne_zero (p : ThetaFullIndex) : thetaFullFrequency p≠0 := by
  rw [thetaFullFrequency_product]
  exact mul_ne_zero p.1.ne_zero
    (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      (thetaPrimaryProduct p.2.2).property)

lemma thetaFullFrequency_span (p : ThetaFullIndex) :
    Ideal.span {thetaFullFrequency p}=ramifiedIdeal^p.2.1*(thetaPrimaryProduct p.2.2).val := by
  rw [thetaFullFrequency_product,Ideal.span_singleton_mul_left_unit p.1.isUnit,
    lambdaFactor_generator_span]

theorem thetaFullFrequency_injective : Function.Injective thetaFullFrequency := by
  rintro ⟨u,m,p⟩ ⟨v,n,q⟩ he
  have hs := congrArg (fun x:Eis=>Ideal.span {x}) he
  rw [thetaFullFrequency_span,thetaFullFrequency_span] at hs
  have hmap : lambdaFactorMap (m,thetaPrimaryProduct p)=lambdaFactorMap (n,thetaPrimaryProduct q) :=
    Subtype.ext hs
  have hij := lambdaFactorMap_bijective.1 hmap
  have hmn : m=n := congrArg Prod.fst hij
  have hpq : p=q := thetaPrimaryProduct_injective (congrArg Prod.snd hij)
  subst n
  subst q
  have huv : u=v := by
    apply Units.ext
    have hh : lambda^m*primaryGenerator (thetaPrimaryProduct p).val≠0 :=
      mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
        (thetaPrimaryProduct p).property
    apply mul_right_cancel₀ hh
    simpa only [thetaFullFrequency_product] using he
  subst v
  rfl

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

namespace SourceCuspDatum

lemma heightScale_pos (d : SourceCuspDatum) : 0<d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

end SourceCuspDatum

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspRadialLength_pos (h : Eis) : 0<sourceCuspRadialLength h := by
  by_cases hh:h=0
  · simp only [sourceCuspRadialLength,if_pos hh,zero_lt_one]
  · rw [sourceCuspRadialLength,if_neg hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : Eis) :
    ‖sourceCuspRadialCoefficient j z h‖=‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient,norm_mul,breveE_norm,mul_one]

lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) :
    sourceCuspRadialCoefficient j z 0=0 := by
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,cuspFrequency,
    map_zero,zero_div,mul_zero,zero_mul]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CubicReflectionKernel

lemma paperKernel_three_halves_bound (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖paperKernel V x‖≤C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

end CubicReflectionKernel

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CompletedGauss
open CubicEisenstein CubicReflectionKernel

theorem paperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*paperKernel V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem thetaFullFrequency_tsum (c w : Eis→ℂ)
    (hsupp : ∀h:Eis,h≠0→c h≠0→∃p:ThetaFullIndex,thetaFullFrequency p=h) :
    (∑'h:{h:Eis // h≠0},w h.val*c h.val)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*c (thetaFullFrequency p) := by
  let phi : ThetaFullIndex→{h:Eis // h≠0} := fun p=>⟨thetaFullFrequency p,thetaFullFrequency_ne_zero p⟩
  let f : {h:Eis // h≠0}→ℂ := fun h=>w h.val*c h.val
  have hinj : Function.Injective phi := by
    intro p q hpq
    exact thetaFullFrequency_injective (congrArg Subtype.val hpq)
  change (∑'h:{h:Eis // h≠0},f h)=∑'p:ThetaFullIndex,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:ThetaFullIndex=>f (phi p))=>phi p.val)
  · exact hinj.comp Subtype.val_injective
  · intro h hh
    have hc : c h.val≠0 := by
      intro hz
      exact hh (by simp only [f,hz,mul_zero])
    obtain ⟨p,hp⟩:=hsupp h.val h.property hc
    have hphi : phi p=h := Subtype.ext hp
    have hfp : f (phi p)≠0 := by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma squarefreeCube_scale_le_norm_third (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (u:Eisˣ) (m:ℕ) :
    (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖≤
      ‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ) := by
  have hn:1≤‖eisEmbedding (primaryGenerator I)‖:=cubePrime_norm_ge_one _ hI
  have hn':1≤‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ):=
    Real.one_le_rpow hn (by norm_num)
  have hb:(‖eisEmbedding (primaryGenerator J)‖^3)^(1/3:ℝ)=‖eisEmbedding (primaryGenerator J)‖:=by
    rw [←Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  have he:‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ)=
      (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    rw [map_mul,map_mul,map_pow,norm_mul,norm_mul,norm_pow,
      Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),ramified_norm_third,hb]
  rw [he]
  have hscale:0≤(3:ℝ)^((m:ℝ)/6):=Real.rpow_nonneg (by norm_num) _
  have hbn:0≤‖eisEmbedding (primaryGenerator J)‖:=norm_nonneg _
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hscale hn') hbn

lemma coefficient_polynomial_of_squarefree_cube_support (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hsupport:∀h:Eis,h≠0→F h≠0→∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)
    (hbound:∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→
      ∀(u:Eisˣ) (m:ℕ),
      ‖F ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖)
    (h:Eis) (hh:h≠0) : ‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  by_cases hz:F h=0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨u,m,I,J,hsq,hI,hJ,rfl⟩:=hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  have hb:=mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC
  exact (by simpa only [mul_assoc] using hb)

theorem three_cusp_coefficients_polynomial_bound :
    ∃C:ℝ,0<C ∧ ∀h:Eis,h≠0→
      ‖sourceResidualFourierCoefficient h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) ∧
      ∀side:Bool,‖ramifiedBesselValue side h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_squarefree_cube_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  constructor
  · exact coefficient_polynomial_of_squarefree_cube_support sourceResidualFourierCoefficient C hC.le
      sourceResidualFourierCoefficient_full_squarefree_cube_support
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).1) h hh
  · intro side
    exact coefficient_polynomial_of_squarefree_cube_support (ramifiedBesselValue side) C hC.le
      (ramifiedBesselValue_squarefree_cube_support side)
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).2 side) h hh

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hDp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C*‖eisEmbedding h‖^(1/3:ℝ))*(‖eisEmbedding h‖^(-4:ℝ)/D^(-4:ℝ))=_
        ring
      _=_:=by rw [he]

theorem three_cusp_coefficients_weighted_summable :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖sourceResidualFourierCoefficient h‖*‖cuspFrequency h‖^(-4:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖ramifiedBesselValue side h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_polynomial_bound
  constructor
  · exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).1)
  · intro side
    exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).2 side)

lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    calc
      _=‖A‖*‖F h‖*(‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)):=by rw [hp];ring
      _=_:=by ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=(Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hDp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by rw [hf];ring
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by rw [hw]
      _=_:=by rw [←radial_inverse_weight _ hx];ring

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_weighted_summable (j:Fin 3) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖(sourceCuspCoefficients j).value h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  fin_cases j
  · exact three_cusp_coefficients_weighted_summable.1
  · exact three_cusp_coefficients_weighted_summable.2 false
  · exact three_cusp_coefficients_weighted_summable.2 true

theorem sourceCuspRadialCoefficient_weighted_summable (j:Fin 3) (z:ℂ) :
    Summable (fun h:Eis=>‖sourceCuspRadialCoefficient j z h‖*
      (sourceCuspRadialLength h)^(-(3/2):ℝ)) := by
  let A:ℂ:=(-2*Real.pi*Complex.I)/(sourceCuspScale j:ℂ)^2
  have hs:=radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficients j).value A
    (sourceCuspCoefficients_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh:h=0
  · subst h
    simp only [ite_true,sourceCuspRadialCoefficient_zero,norm_zero,zero_mul]
  · rw [if_neg hh,sourceCuspRadialCoefficient_norm,sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength,if_neg hh]
    congr 1
    apply congrArg norm
    dsimp only [A]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaBesselScale_square : thetaBesselScale^2=(1/27:ℝ) := by
  rw [thetaBesselScale_eq,div_pow,one_pow,Real.sq_sqrt (by norm_num)]

lemma sourceCuspRadialScale_ratio (j:Fin 3) :
    thetaBesselScale/sourceCuspRadialScale j=sourceCuspScale j := by
  rw [sourceCuspRadialScale]
  field_simp [thetaBesselScale_pos.ne']

lemma sourceCuspKernel_argument (j:Fin 3) (X r Q:ℝ) :
    27*thetaBesselScale^2*(sourceCuspRadialScale j)^2*X*r/Q^2=
      X*r/(27*(sourceCuspScale j)^2*Q^2) := by
  rw [sourceCuspRadialScale,div_pow,thetaBesselScale_square]
  ring

lemma SourceCuspDatum.smoothedKernel_eq (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  simp only [SourceCuspDatum.smoothedKernel,sourceCuspRadialScale_ratio,sourceCuspKernel_argument]

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_full_support (j:Fin 3) (h:Eis) (hh:h≠0)
    (hc:(sourceCuspCoefficients j).value h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  have hs : ∃u:Eisˣ,∃m:ℕ,∃I J:Ideal Eis,Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u:Eis)*ActualEisensteinCubic.lambda^m*primaryGenerator I*(primaryGenerator J)^3 := by
    fin_cases j
    · exact sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support false h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support true h hh hc
  obtain ⟨u,m,I,J,hI,hIg,hJg,he⟩:=hs
  exact ⟨(u,m,(⟨I,hI,hIg⟩,⟨J,hJg⟩)),he.symm⟩

lemma sourceCuspRadialCoefficient_full_support (j:Fin 3) (z:ℂ) (h:Eis)
    (hh:h≠0) (hc:sourceCuspRadialCoefficient j z h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  apply sourceCuspCoefficients_full_support j h hh
  intro hz
  apply hc
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,hz,
    star_zero,mul_zero,zero_div,zero_mul]

theorem sourceCuspRadialCoefficient_tsum_full_index (j:Fin 3) (z:ℂ) (w:Eis→ℂ) :
    (∑'h:Eis,w h*sourceCuspRadialCoefficient j z h)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        sourceCuspRadialCoefficient j z (thetaFullFrequency p) := by
  have hs:Function.support (fun h:Eis=>w h*sourceCuspRadialCoefficient j z h)⊆
      {h:Eis|h≠0}:=by
    intro h hh hz
    subst h
    exact hh (by
      change w 0*sourceCuspRadialCoefficient j z 0=0
      rw [sourceCuspRadialCoefficient_zero,mul_zero])
  calc
    _=∑'h:{h:Eis//h≠0},w h.val*sourceCuspRadialCoefficient j z h.val:=
      (tsum_subtype_eq_of_support_subset hs).symm
    _=_:=thetaFullFrequency_tsum (sourceCuspRadialCoefficient j z) w
      (sourceCuspRadialCoefficient_full_support j z)

lemma SourceCuspDatum.smoothedKernel_full_index (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [d.smoothedKernel_eq]
  congr 1
  have he:=sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
    (fun h=>CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))
  simpa only [mul_comm] using he

lemma SourceCuspDatum.smoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hs:=paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    (sourceCuspRadialCoefficient_weighted_summable _ _)
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
    CubicReflectionKernel.paperKernel (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma fixedCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedCuspArray j u m I J := by
  have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
  rw [fixedCuspArray,if_pos h,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

lemma fixedConjugateCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedConjugateCuspArray j u m I J := by
  rw [fixedCuspArray_reconstruct j u m I J h,star_mul]
  simp only [fixedConjugateCuspArray,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

lemma frequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=activeRow χ ψ j σ ε x := by
  unfold frequencyRow finiteAdditiveFourierCoeff frequencyMultiplier activeRow
  simp only [Units.ne_zero,ite_false,Units.val_inv_eq_inv_val,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring_nf

open ActualEisensteinCubic CompletedGauss

attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldFrequency
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeFrequency
theorem canonical_frequencyRow_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    (∑h:(ActualEisensteinCubic.O⧸P)ˣ,frequencyRow (actualSextic P hgood) ψ j σ ε x h)=
      (((actualSextic P hgood)⁻¹)^2) σ *
        phase (actualSextic P hgood) ψ j ε*bracket (actualSextic P hgood) j x := by
  rw [frequencyRow_units]
  simpa only [actualSextic] using canonical_A5_normalized P hgood hchar ψ hψ j hj σ ε x

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_heightScale (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).heightScale=‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul,norm_mul]
  have hn:‖eisEmbedding (s.upper 1 1)‖=1 := by
    rcases s.lower_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hn,mul_one]

lemma datum_dualPoint (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).dualPoint=
      eisEmbedding (s.upper 0 0*s.upper 0 1)-
        eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0)) := by
  rw [SourceCuspDatum.dualPoint,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,upper_right_removed_last,
    upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_add,map_neg,map_mul]
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  field_simp [hc,ht]
  linear_combination (eisEmbedding (s.upper 0 0)*eisEmbedding (((g:SL(2,Eis))*H) 1 1)-
    eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 0 1))*hd

lemma datum_multiplier (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).multiplier=
      -star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma)*
        eisEmbedding (s.upper 0 0)^2/eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [SourceCuspDatum.multiplier,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul]
  change -star (levelTwoComplexCharacter (g*s.gamma))/
    (eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 1 1))^2=_
  rw [map_mul,star_mul]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hp:eisEmbedding (s.upper 0 0)^2*eisEmbedding (s.upper 1 1)^2=1 := by
    rw [←mul_pow,hd,one_pow]
  field_simp [hc,ht]
  linear_combination (star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma))*hp

lemma datum_additive_phase (h:((g:SL(2,Eis))*H) 1 0≠0) (freq:ℂ) (scale:ℂ) :
    ShortDraftTrace.breveE (-freq*(s.datum g h).dualPoint/scale)=
      ShortDraftTrace.breveE (-freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale)*
      ShortDraftTrace.breveE (freq*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/scale) := by
  rw [s.datum_dualPoint]
  rw [show -freq*(eisEmbedding (s.upper 0 0*s.upper 0 1)-
      eisEmbedding (s.upper 0 0)^2*(eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)))/scale=
    -freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale+
      freq*eisEmbedding (s.upper 0 0)^2*eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)/scale by ring]
  simp only [AddChar.map_add_eq_mul,mul_div_assoc]

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hM⟩ =
      eisEmbedding (symbol (M 1 0-u*M 1 1) (M 0 0-u*M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_ramified_relative_matrix]
  rfl

lemma A3_unramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(A3WeylCusp u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hM⟩ =
      eisEmbedding (symbol (-M 1 1) (-M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_unramified_relative_matrix]
  rfl

end ShortDraftCusp

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayIndex_ne_zero (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayIndex u m I J≠0 :=
  mul_ne_zero (mul_ne_zero (ramifiedElement_ne_zero u m) hI) (pow_ne_zero _ hJ)

lemma fixedCuspArrayIndex_norm_sq (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖^2=
      (3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hr:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=‖eisEmbedding (u.val*lambda^m)‖^2*‖eisEmbedding (primaryGenerator I)‖^2*
      (‖eisEmbedding (primaryGenerator J)‖^2)^3 := by
        simp only [fixedCuspArrayIndex,map_mul,map_pow,norm_mul,norm_pow]
        ring
    _=_ := by rw [hr,primaryGenerator_norm_sq I hI,primaryGenerator_norm_sq J hJ]

lemma fixedCuspArrayIndex_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      Real.sqrt ((3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3) := by
  rw [←fixedCuspArrayIndex_norm_sq u m I J hI hJ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

lemma fixedCuspArrayWeight_div_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      1/((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hn:0<(Ideal.absNorm I:ℝ) := by
    rw [←primaryGenerator_norm_sq I hI]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hI))
  have hb:0<(Ideal.absNorm J:ℝ) := by
    rw [←primaryGenerator_norm_sq J hJ]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [fixedCuspArrayWeight,fixedCuspArrayIndex_norm u m I J hI hJ]
  simpa only [Real.rpow_natCast] using cusp_coefficient_normalization (m:ℝ)
    (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) hn hb

theorem fixedConjugateCuspArray_div_norm (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))/
      (‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℂ)=
    (fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J/
      (((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [fixedConjugateCuspArray_reconstruct j u m I J h]
  calc
    _=(fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J*
      ((fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℝ):ℂ) := by
        push_cast
        ring
    _=_ := by
      rw [fixedCuspArrayWeight_div_norm u m I J h.2.1 h.2.2]
      push_cast
      ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullFrequency_eq_fixedCuspArrayIndex (p:ThetaFullIndex) :
    thetaFullFrequency p=fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val := rfl

lemma sourceCuspRadialLength_full_index (p:ThetaFullIndex) :
    sourceCuspRadialLength (thetaFullFrequency p)=
      (3:ℝ)^p.2.1*(Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength,if_neg (thetaFullFrequency_ne_zero p),thetaFullFrequency_eq_fixedCuspArrayIndex]
  exact fixedCuspArrayIndex_norm_sq p.1 p.2.1 p.2.2.1.val p.2.2.2.val
    p.2.2.1.property.2 p.2.2.2.property

lemma thetaRamifiedScale_eq (m:ℕ) :
    ramifiedScale 1 completedRamifiedStep m=(3:ℝ)^((m:ℝ)/3) := by
  unfold ramifiedScale completedRamifiedStep
  rw [one_mul,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma thetaRamifiedScale_cube (m:ℕ) :
    (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  rw [thetaRamifiedScale_eq,←Real.rpow_mul_natCast (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [show ((m:ℝ)/3)*(3:ℝ)=m by ring,Real.rpow_natCast]

lemma sourceCusp_full_index_kernel_argument (p:ThetaFullIndex) (j:Fin 3) (Q X:ℝ) :
    X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2)=
      (X/(27*(sourceCuspScale j)^2*Q^2))*(ramifiedScale 1 completedRamifiedStep p.2.1)^3*
        (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength_full_index,thetaRamifiedScale_cube]
  ring

lemma sourceCuspRadialCoefficient_angle (j:Fin 3) (z:ℂ) (h:Eis) (hh:h≠0) :
    sourceCuspRadialCoefficient j z h=
      ((-2*Real.pi*Complex.I*thetaFrequencyScale)/(sourceCuspScale j:ℂ)^2)*
        sourceFrequencyAngle h*
        (star ((sourceCuspCoefficients j).value h)/(‖eisEmbedding h‖:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) := by
  have hn:(‖eisEmbedding h‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))
  have hs:(sourceCuspScale j:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  rw [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,sourceCuspRadialLength,if_neg hh]
  rw [cuspFrequency_eq_thetaFrequencyScale]
  unfold sourceFrequencyAngle
  push_cast
  field_simp [hn,hs]

theorem sourceCuspRadialCoefficient_fixed_array
    (j:Fin 3) (z:ℂ) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) (h:fixedCuspArrayEligible I J) :
    sourceCuspRadialCoefficient j z (fixedCuspArrayIndex u m I J)=
      (fixedRadialCoefficientScalar/(sourceCuspScale j:ℂ)^2)*
        (fixedConjugateCuspArray j u m I J*
          sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
          ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
            (z/(sourceCuspScale j:ℂ))))/
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm I:ℝ)*
          (Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [sourceCuspRadialCoefficient_angle _ _ _
    (fixedCuspArrayIndex_ne_zero u m I J h.2.1 h.2.2),
    fixedConjugateCuspArray_div_norm j u m I J h,thetaRamifiedScale_eq]
  unfold fixedRadialCoefficientScalar
  push_cast
  ring

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullIndex_denominator_pos (p:ThetaFullIndex) :
    0< ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ) := by
  have hI:0<(Ideal.absNorm p.2.2.1.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.1.property.2]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.1.property.2))
  have hJ:0<(Ideal.absNorm p.2.2.2.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.2.property]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.2.property))
  rw [thetaRamifiedScale_eq]
  positivity

theorem SourceCuspDatum.smoothedFullCoefficient_normalization (d:SourceCuspDatum) (p:ThetaFullIndex) :
    (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)=
    (fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency p)*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
          (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
      ((ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ) := by
  have hs:(sourceCuspScale d.index:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos _).ne'
  have hn:((ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (thetaFullIndex_denominator_pos p).ne'
  simp only [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rw [sourceCuspRadialCoefficient_fixed_array _ _ _ _ _ _
    ⟨p.2.2.1.property.1,p.2.2.1.property.2,p.2.2.2.property⟩]
  field_simp [hs,hn]

end CubicEisenstein

open scoped Classical BigOperators

namespace CubicEisenstein
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma smoothed_row_factor (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g hc).multiplier*((s.datum g hc).heightScale:ℂ)=
      -star (levelTwoComplexCharacter g)*
        (star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*
        ((‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ):ℂ)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [s.datum_multiplier,s.datum_heightScale]
  push_cast
  ring

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical Matrix MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein
open scoped Classical BigOperators ContDiff MatrixGroups

open CompletedGauss CompletedDyadic

theorem sum_smoothedKernel_common_cusp {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).smoothedKernel W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).multiplier*(Q:ℂ))*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    (sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).smoothedKernel_full_index_norm_summable W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).smoothedKernel W X=∑'p,F i p := by
    rw [(d i).smoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).smoothedFullCoefficient_normalization p
  dsimp only [F]
  calc
    _=w i*(((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring

end CubicEisenstein

open scoped Classical BigOperators

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
open CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

theorem embedded_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    eisEmbedding (symbol a (∏i,p i))=
      ∏i,(actualSextic (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk _ a))^2 := by
  change eisEmbedding (idealSymbol (Ideal.span {∏i,p i}) a)=_
  rw [←idealRowHom_square,idealRowHom_product p hg Finset.univ a]
  simp only [ActualEisensteinCubic.finiteSquarefreeRow,actualSextic,Finset.prod_pow]

theorem conjugate_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk _ a) := by
  rw [embedded_symbol_product p hg a,star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_pow,MulChar.star_apply',MulChar.pow_apply' _ (by decide : (2:ℕ)≠0)]

theorem conjugate_symbol_product_frequency {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis)
    (σ : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i : Eis⧸Ideal.span {p i})*h i) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i : Eis⧸Ideal.span {p i})*h i) := by
  rw [conjugate_symbol_product p hg a]
  simp only [ha]

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_field_inverse {F : Type*} [Field F] (a d B : F) (σ ε : Fˣ) (h x : F)
    (had : a*d=1) (ha : a=(σ:F)*h) (hε : B*(σ:F)*(ε:F)=-1) :
    h≠0 ∧ -d*B⁻¹*x=((ε:F)*x)*h⁻¹ := by
  have hh : h≠0 := by
    intro hz
    rw [ha,hz,mul_zero,zero_mul] at had
    exact zero_ne_one had
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hε
    exact neg_ne_zero.mpr (one_ne_zero : (1:F)≠0) hε.symm
  have hd : d=((σ:F)*h)⁻¹ := eq_inv_of_mul_eq_one_right (ha ▸ had)
  have he : (ε:F)=-(B*(σ:F))⁻¹ := by
    have heq : (B*(σ:F))*(-(ε:F))=1 := by linear_combination -hε
    exact neg_eq_iff_eq_neg.mp (eq_inv_of_mul_eq_one_right heq)
  refine ⟨hh,?_⟩
  rw [hd,he]
  field_simp

attribute [local instance] OAI.ShortDraftCusp.A4quotientField
lemma A4_active_local {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (a b c0 d : Eis) (hdet : a*d-b*(c0*∏i,p i)=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (x : Eis) (i : ι) :
    h i≠0 ∧
      -(Ideal.Quotient.mk (Ideal.span {p i}) d)*
        (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹*
        Ideal.Quotient.mk (Ideal.span {p i}) x =
      ((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk (Ideal.span {p i}) x)*(h i)⁻¹ := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have had : Ideal.Quotient.mk (Ideal.span {p i}) a*
      Ideal.Quotient.mk (Ideal.span {p i}) d=1 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hdet
    simpa only [map_sub,map_mul,map_one,hz,mul_zero,sub_zero] using he
  exact A4_field_inverse _ _ _ (σ i) (ε i) (h i) _ had (ha i) (hε i)

lemma A4_complement_inverse {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (c0 U w : Eis) (hbez : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (i : ι) (v t : Eis) (hlocal : t*p i+v*cofactor p i=1) :
    (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹=
      Ideal.Quotient.mk (Ideal.span {p i}) (w*v) := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hw := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hbez
  have hv := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hlocal
  simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at hw
  simp only [map_add,map_mul,map_one,hp0,mul_zero,zero_add] at hv
  symm
  apply eq_inv_of_mul_eq_one_right
  simp only [map_mul,map_pow]
  calc
    _ = ((Ideal.Quotient.mk _ ramifiedTraceLambda)^3*Ideal.Quotient.mk _ w*
        Ideal.Quotient.mk _ c0)*(Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (cofactor p i)) := by ring
    _ = 1 := by rw [hw,hv,mul_one]

end ShortDraftCusp

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]

attribute [local instance] OAI.ShortDraftCusp.A4phaseField
theorem A4_phase_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
      (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹) := by
  let hr : (∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs:=ShortDraftCRT.normalized_crt_pair eisEmbedding ShortDraftTrace.breveE
    ramifiedTraceLambda c0 (∏i,p i) d x U w
    (by simpa only [ramifiedEmbedding_traceLambda] using eisLam_ne_zero)
    (eisEmbedding_ne_zero hc0) (eisEmbedding_ne_zero hr) hbez
  simp only [ramifiedEmbedding_traceLambda] at hs
  rw [hs,←A4BadPhase_eq c0 hc0 d U x]
  congr 1
  have he : ShortDraftTrace.breveE (eisEmbedding (-d*w*x)/(eisLam*eisEmbedding (∏i,p i)))=
      quotientTrace (∏i,p i) hr (Ideal.Quotient.mk _ (-d*w*x)) := by
    simp only [quotientTrace,eisTraceModChar,traceModChar_mk]
    congr 1
    rw [mul_comm eisLam]
  rw [he,addChar_finite_crt_factor (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productElementCRT_mk]
  obtain ⟨t,v,hlocal⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
  have hc:=coordinate_trace_character p hp hcop i t v hlocal
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (quotientTrace (∏i,p i) hr) i (Ideal.Quotient.mk _ (-d*w*x))=_
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates (∏i,p i) hr) i
    (Ideal.Quotient.mk _ (-d*w*x))=_
  rw [hc]
  change quotientTrace (p i) (hp i)
    (Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (-d*w*x))=_
  apply congrArg (quotientTrace (p i) (hp i))
  have hinv:=A4_complement_inverse p c0 U w hbez i v t hlocal
  have hphase:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).2
  rw [hinv] at hphase
  convert (preTransparency := .instances) hphase using 1 ; simp only [map_mul,map_neg] ; ring

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

attribute [local instance] OAI.ShortDraftCusp.A4frequencyField
theorem A3_A4_frequency_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    star (eisEmbedding (CubicJacobiGlobal.symbol a (∏i,p i)))*
      ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (h i) := by
  rw [conjugate_symbol_product_frequency p hg a σ h ha,
    A4_phase_product p hp hcop a b c0 d U w x hc0 hdet hbez σ ε h ha hε]
  calc
    _ = A4BadPhase c0 hc0 d U x *
      ((∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i:Eis⧸Ideal.span {p i})*h i))*
       ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹)) := by ring
    _ = _ := by
      congr 1
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hn:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).1
      simp only [frequencyMultiplier,if_neg hn]

lemma A4BadPhase_eq_of_residue (c0:Eis) (hc0:c0≠0) (d U d' U' x:Eis)
    (hres:ramifiedTraceLambda^3*c0∣d*U-d'*U') :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d' U' x := by
  unfold A4BadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert (preTransparency := .instances) hd using 1 ; ring

end ShortDraftCusp

open scoped BigOperators Classical

open scoped Classical BigOperators

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical BigOperators

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dif_pos hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) : ramifiedTraceLambda∣h := by
  apply ramifiedTraceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact (ramifiedBesselValue_exact_lambda_valuation false h hh).1
  · exact (ramifiedBesselValue_exact_lambda_valuation true h hh).1

lemma sourceCuspPhaseNumerator_embedding (j:Fin 3) (u h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    eisEmbedding (sourceCuspPhaseNumerator j u h)=
      -eisLam^4*cuspFrequency h*(eisEmbedding u)^2/(sourceCuspScale j:ℂ) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,ite_true,map_mul,map_pow,
      ramifiedEmbedding_traceLambda,cuspFrequency,sourceCuspScale]
    norm_num only [Matrix.cons_val_zero,Complex.ofReal_one,div_one]
    field_simp [eisLam_ne_zero]
    linear_combination (eisEmbedding h*(eisEmbedding u)^2)*TraceLambdaPhase.eisLam_sq
  · have hdiv:=sourceCuspCoefficients_ramified_divisibility j hj h hh
    have hprod:=congrArg eisEmbedding (paperLambdaQuotient_mul h hdiv)
    have hscale:sourceCuspScale j=3 := by fin_cases j <;> simp_all [sourceCuspScale]
    have hfour:eisLam^4=(9:ℂ) := by
      calc
        eisLam^4=(eisLam^2)^2:=by ring
        _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num
    rw [sourceCuspPhaseNumerator,if_neg hj]
    simp only [map_mul,map_neg,map_pow]
    rw [cuspFrequency,hscale,←hprod,map_mul,ramifiedEmbedding_traceLambda,hfour]
    norm_num only [Complex.ofReal_ofNat]
    field_simp [eisLam_ne_zero]
    ; ring

lemma sourceCuspPhaseNumerator_phase (j:Fin 3) (u h c d:Eis) (hc:c≠0)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    ShortDraftTrace.breveE (cuspFrequency h*(eisEmbedding u)^2*
      (eisEmbedding d/eisEmbedding c)/(sourceCuspScale j:ℂ))=
    ShortDraftTrace.breveE (-(eisEmbedding d*
      (eisEmbedding (sourceCuspPhaseNumerator j u h)/eisLam^4))/eisEmbedding c) := by
  rw [sourceCuspPhaseNumerator_embedding j u h hh]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc,
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne']

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma PrincipalStratumArithmetic.frequency_congruence {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} (D:PrincipalStratumArithmetic p N a0 c0)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) ((D.gamma v:SL(2,Eis)) 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace CubicEisenstein

section
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    (sourceCuspCoefficients s.index).value (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':(sourceCuspCoefficients s.index).value
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]

lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding d/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (-(eisEmbedding d*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]

lemma datum_integral_phase (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p))*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      ShortDraftTrace.breveE (-(eisEmbedding (((g:SL(2,Eis))*H) 1 1)*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc

lemma datum_common_row_factor (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (levelTwoComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring

end FixedCuspShape
end

open scoped Classical BigOperators ContDiff MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_character_of_relative_level (M:SL(2,Eis)) (u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol q (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  have hdet:M 0 0*M 1 1-M 0 1*(u*(q*r))=1 := by
    have hd:=M.property
    simp only [Matrix.det_fin_two,hC] at hd
    linear_combination hd
  rw [A3_ramified_literal_character,hC,show (u*q)*r=u*(q*r) by ring,
    A3_ramified_global_factor _ _ _ _ _ _ hdet ha hA hr,map_mul]

theorem A3_unramified_character_of_relative_level (M:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb:=levelThree_primary ⟨M*(A3WeylCusp u)⁻¹,hG⟩
  change lambda^2∣(((M*(A3WeylCusp u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hb
  rw [A3_unramified_relative_matrix] at hb
  have hdet:M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    simpa only [Matrix.det_fin_two,hC] using M.property
  rw [hC] at hc
  rw [A3_unramified_literal_character,A3_unramified_global_factor _ _ _ _ _ hdet hb hc h9,map_mul]

end

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

theorem A3_ramified_fixed_sector_character (M M0:SL(2,Eis)) (N u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (hG0:M0*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (ha0:lambda^2∣M0 0 0-1)
    (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r)
    (h9N:(9:Eis)∣N) (hqN:q∣N) (huN:u∣N)
    (hA:N∣M 0 0-M0 0 0) (hB:N∣M 0 1-M0 0 1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M0 0 0-u*M0 0 1)*symbol q (M0 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_ramified_character_of_relative_level M u q r hG ha hr hC]
  rw [A3_ramified_fixed_factor_congr N q u (M 0 0) (M0 0 0) (M 0 1) (M0 0 1)
    h9N hqN huN ha ha0 (A3_ramified_relative_primary M u hG)
    (A3_ramified_relative_primary M0 u hG0) hA hB]

theorem A3_unramified_fixed_sector_character (M M0:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r)
    (hA:c0∣M 0 0-M0 0 0) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M0 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_unramified_character_of_relative_level M u c0 r hG hc h9 hC,
    symbol_congr hA]

end ShortDraftCusp

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma inverse_fixed (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ramifiedTraceLambda^3*c0∣D.matrix v 1 1-D.matrix (fun _=>1) 1 1 := by
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  exact (hD9.trans hN).trans (D.matrix_fixed v 1 1)

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

theorem ramified_character (D:ControlledStratumArithmetic p N a0 c0 true)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u q:Eis) (hc0:c0=u*q) (hcu:(3:Eis)∣c0-u)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(lowerCuspMatrix u)⁻¹,
      D.ramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr ha u hcu v⟩=
      D.ramifiedFixedFactor u q*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  exact A3_ramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) N u q (∏i,p i)
    (D.ramified_relative h3N hr ha u hcu v) (D.ramified_relative h3N hr ha u hcu (fun _=>1))
    (D.numerator_primary h3N hr ha v) (D.numerator_primary h3N hr ha (fun _=>1)) hr
    (by rw [D.denominator,hc0]) h9N
    ((hc0 ▸ dvd_mul_left q u).trans hcN) ((hc0 ▸ dvd_mul_right u q).trans hcN)
    (D.matrix_fixed v 0 0) (D.matrix_fixed v 0 1)

theorem unramified_character (D:ControlledStratumArithmetic p N a0 c0 false)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(A3WeylCusp u)⁻¹,
      D.unramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr hc u hau v⟩=
      D.unramifiedFixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcond:=D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  exact A3_unramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) u c0 (∏i,p i)
    (D.unramified_relative h3N hr hc u hau v) (D.denominator_primary hr hc v)
    (dvd_mul_of_dvd_right hcond.2 _) (D.denominator v)
    (((dvd_mul_left c0 9).trans hN).trans (D.matrix_fixed v 0 0))

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

theorem relative_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  cases mode
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.false_eq_true,↓reduceIte,
      unramifiedFixedFactor] using D.unramified_character hN hr hbase a0 (by simp) v
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.true_eq,↓reduceIte,
      ramifiedFixedFactor] using D.ramified_character hN hr hbase c0 1 (by simp) (by simp) v

end ControlledStratumArithmetic
end

section
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma sourceGamma_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    levelTwoComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  sourceLevelInclusion_character _

end ControlledStratumArithmetic

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.LocalReflection
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem localFourier_zeroMark (ψ : AddChar F ℂ) (h : F) :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

theorem marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Poisson
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

attribute [local instance] OAI.SevenEighths.InverseMoment.markedQuotientField
attribute [local instance] OAI.SevenEighths.InverseMoment.markedQuotientFintype
theorem actual_marked_active_eq
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      -LocalReflectionBrackets.activeRow (CompletedGauss.actualSextic P hg) ψ 0 σ ε x := by
  simpa only [localReflectionActive, localFourier,
    LocalReflectionBrackets.activeRow, pow_zero] using
    marked_active_eq_neg_trivial (CompletedGauss.actualSextic P hg) ψ hψ σ ε x

theorem actual_marked_active_formula
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ *
        LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2 *
        (((CompletedGauss.actualSextic P hg) ^ 2)⁻¹)
          ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x) := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x,
    LocalReflectionBrackets.canonical_A5_normalized P hg hchar ψ hψ 0 (by norm_num)]
  simp only [LocalReflectionBrackets.phase, LocalReflectionBrackets.bracket,
    show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
  ring

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedStratum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section Local
variable {F : Type*} [Field F] [Fintype F]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

end Local

attribute [local instance] OAI.SevenEighths.InverseMoment.markedStratumField
attribute [local instance] OAI.SevenEighths.InverseMoment.markedStratumFintype
theorem actual_mixed_frequency_units (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    (∑ h : (Eis ⧸ P)ˣ, mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (Eis ⧸ P) : ℂ)⁻¹ * tau (actualSextic P hg) ψ 2 *
          (((actualSextic P hg) ^ 2)⁻¹) ((σ : Eis ⧸ P) * (ε : Eis ⧸ P) * x)
      else (((actualSextic P hg)⁻¹) ^ 2) σ *
        phase (actualSextic P hg) ψ j ε * bracket (actualSextic P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ControlledMultiplier
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseMoment.controlledField
attribute [local instance] OAI.SevenEighths.InverseMoment.controlledFintype
theorem controlled_phase_product (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) (x : Eis) :
    star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) (v i) := by
  have hbad : A4BadPhase c0 hc0 (D.matrix v 1 1) D.U x =
      A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x := by
    apply A4BadPhase_eq_of_residue
    convert (preTransparency := .instances) dvd_mul_of_dvd_left (D.inverse_fixed hN v) D.U using 1 ; ring
  have hlocal := A3_A4_frequency_product p hp hcop hg (D.matrix v 0 0) (D.matrix v 0 1)
    c0 (D.matrix v 1 1) D.U D.w x hc0 (D.determinant v) D.bezout D.sigma D.epsilon
    (fun i => (v i : Eis ⧸ Ideal.span {p i})) (D.frequency_congruence v) D.epsilon_value
  rw [D.relative_character hN hr hbase v, star_mul]
  calc
    _ = star D.fixedFactor * (star (eisEmbedding (symbol (D.matrix v 0 0) (∏ i, p i))) *
        ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
          (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) := by ring
    _ = _ := by rw [hlocal, hbad]; ring

theorem controlled_local_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ, fullLocalFourierWeight hp F v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, ∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
        finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) v *
          frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
            (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_assoc, controlled_phase_product D hN hr hbase hp hc0 hcop hg v x]
  simp only [fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

theorem mixedActiveBracket_eq_units [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (D : ControlledStratumArithmetic p N a0 c0 mode) (i : ι) (x : Eis) :
    (∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
      finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (mixedPrimeFunction p hg j S i) v *
        frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
          (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v) =
      mixedActiveBracket hp hg j S D i x := by
  have hh := actual_mixed_frequency_units (Ideal.span {p i}) (hg i) (hc i)
    (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (decide (i ∈ S)) (j i) (hj i) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x)
  have hfun : mixedPrimeFunction p hg j S i = fun t =>
      if i ∈ S then zeroMark t else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) t := rfl
  rw [hfun]
  by_cases hi : i ∈ S
  · simpa only [hi, decide_true, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      ite_true, markedFrequencyRow] using hh
  · simpa only [hi, decide_false, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      Bool.false_eq_true, ite_false, frequencyRow] using hh

theorem controlled_mixed_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, mixedActiveBracket hp hg j S D i x := by
  rw [controlled_local_multiplier D hN hr hbase hp hc0 hcop hg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact mixedActiveBracket_eq_units hp hg hc j hj S D i x

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReflectedDual
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseMoment.dualQuotientFintype
theorem mixed_smoothed_eq_reflected_oai (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  have hden : c0 * (∏ i, p i) ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hmat (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      (D.sourceGamma hN hr hbase v : SL(2, Eis)) *
        ControlledStratumArithmetic.fixedCusp a0 c0 mode = D.matrix v :=
    D.sourceGamma_mul hN hr hbase v
  have hchar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      levelTwoComplexCharacter (D.sourceGamma hN hr hbase v) =
        complexCharacter (D.relativeGamma hN hr hbase v) :=
    D.sourceGamma_character hN hr hbase v
  have hC : ∀ v, ((D.sourceGamma hN hr hbase v : SL(2, Eis)) *
      ControlledStratumArithmetic.fixedCusp a0 c0 mode) 1 0 = c0 * ∏ i, p i := by
    intro v
    exact (congrArg (fun M : SL(2, Eis) => M 1 0) (hmat v)).trans (D.denominator v)
  have he := s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hden hC
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) W lo hi hlo hsupp hW X hX
  change mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X = _ at he
  rw [he]
  unfold mixedReflectedValue
  apply congrArg (fun z : ℂ => fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) * z)
  apply tsum_congr
  intro t
  congr 1
  simpa only [hchar, hmat, map_mul] using
    controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.InverseMoment.mixed_smoothed_eq_reflected_oai.{u_1} := @OAI.SevenEighths.InverseMoment.mixed_smoothed_eq_reflected_oai.{u_1}
