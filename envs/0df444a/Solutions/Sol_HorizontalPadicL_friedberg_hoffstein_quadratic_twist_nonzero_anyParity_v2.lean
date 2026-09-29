-- Prove2me | solution 1 for HorizontalPadicL.friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T19:42:59.352375+00:00
-- url     : https://prove2.me/submissions/55db52bf-ec8a-4d69-98fe-37ef631771f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MTT_HeckeEquivalence
import Mathlib.Data.Nat.Find
import Definitions.Def_KN_HorizontalPadicL
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_nonzero_of_hasMinimalLevel
import Theorems.Thm_MTT_Eigenform_quadratic_centralValue_eq_eulerFactors_mul_of_hasMinimalLevel

set_option autoImplicit false

namespace MTT.Eigenform

variable {N M L k : ℕ} {ι : Qbar →+* ℂ}

theorem sameHeckeSystem_refl (f : Eigenform N k ι) : SameHeckeSystem f f :=
  ⟨1, Nat.zero_lt_one, fun _ _ _ ↦ ⟨rfl, rfl⟩⟩

theorem SameHeckeSystem.symm {f : Eigenform N k ι} {g : Eigenform M k ι}
    (h : SameHeckeSystem f g) : SameHeckeSystem g f := by
  obtain ⟨B, hB, h⟩ := h
  exact ⟨B, hB, fun p hp hpB ↦ ⟨(h p hp hpB).1.symm, (h p hp hpB).2.symm⟩⟩

theorem SameHeckeSystem.trans {f : Eigenform N k ι} {g : Eigenform M k ι}
    {h : Eigenform L k ι} (hfg : SameHeckeSystem f g) (hgh : SameHeckeSystem g h) :
    SameHeckeSystem f h := by
  obtain ⟨B, hB, hfg⟩ := hfg
  obtain ⟨C, hC, hgh⟩ := hgh
  refine ⟨B * C, Nat.mul_pos hB hC, fun p hp hpBC ↦ ?_⟩
  have hpB : ¬ p ∣ B := fun hpB ↦ hpBC (dvd_mul_of_dvd_left hpB C)
  have hpC : ¬ p ∣ C := fun hpC ↦ hpBC (dvd_mul_of_dvd_right hpC B)
  exact ⟨(hfg p hp hpB).1.trans (hgh p hp hpC).1,
    (hfg p hp hpB).2.trans (hgh p hp hpC).2⟩

/-- Every eigenform at a positive level has a representative at a least positive level,
without increasing the level and without changing its prime Hecke system. -/
theorem exists_sameHeckeSystem_hasMinimalLevel (hN : 0 < N) (f : Eigenform N k ι) :
    ∃ M : ℕ, 0 < M ∧ M ≤ N ∧ ∃ g : Eigenform M k ι,
      SameHeckeSystem f g ∧ HasMinimalLevel g := by
  classical
  have hex : ∃ M : ℕ, 0 < M ∧ ∃ g : Eigenform M k ι, SameHeckeSystem f g :=
    ⟨N, hN, f, sameHeckeSystem_refl f⟩
  obtain ⟨hM, g, hfg⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hM, Nat.find_min' hex ⟨hN, f, sameHeckeSystem_refl f⟩,
    g, hfg, ?_⟩
  intro L hL h hgh
  exact Nat.find_min' hex ⟨hL, h, hfg.trans hgh⟩

end MTT.Eigenform

namespace HorizontalPadicL

/-- An algebraic Dirichlet character has complex absolute value at most one. -/
lemma embedded_character_norm_le_one (ι : MTT.Qbar →+* ℂ)
    (η : DirichletCharacterWithLevel) (n : ℕ) : ‖ι (η.2 n)‖ ≤ 1 := by
  let χ : DirichletCharacter ℂ η.1.1 :=
    { toFun := fun x ↦ ι (η.2 x)
      map_one' := by simp
      map_mul' := by intro a b; simp
      map_nonunit' := by intro a ha; simp [η.2.map_nonunit ha] }
  exact χ.norm_le_one n

/-- The local Euler factor at the central point cannot vanish under the standard bound. -/
lemma quadratic_euler_factor_ne_zero {k p : ℕ} (heven : Even k) (hp : p.Prime)
    (ι : MTT.Qbar →+* ℂ) (η : DirichletCharacterWithLevel) (α : ℂ)
    (hα : ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    1 - α * ι (η.2 p) / (p : ℂ) ^ (k / 2) ≠ 0 := by
  have hple : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hple
  have hkdiv : ((k / 2 : ℕ) : ℝ) = (k : ℝ) / 2 := by
    obtain ⟨m, rfl⟩ := heven
    simp [← two_mul]
  have hpow : (p : ℝ) ^ (((k : ℝ) - 1) / 2) < (p : ℝ) ^ (k / 2) := by
    rw [← Real.rpow_natCast, hkdiv]
    apply Real.rpow_lt_rpow_of_exponent_lt hple
    linarith
  have hnorm : ‖α * ι (η.2 p) / (p : ℂ) ^ (k / 2)‖ < 1 := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    apply (div_lt_one (pow_pos hp0 _)).2
    calc
      ‖α‖ * ‖ι (η.2 p)‖ ≤ ‖α‖ * 1 :=
        mul_le_mul_of_nonneg_left (embedded_character_norm_le_one ι η p) (norm_nonneg _)
      _ = ‖α‖ := mul_one _
      _ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := hα
      _ < (p : ℝ) ^ (k / 2) := hpow
  intro hzero
  have hratio : α * ι (η.2 p) / (p : ℂ) ^ (k / 2) = 1 := (sub_eq_zero.mp hzero).symm
  simp [hratio] at hnorm

/-- A finite product of such local Euler factors is nonzero. -/
lemma quadratic_euler_factor_prod_ne_zero {k r : ℕ} (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (η : DirichletCharacterWithLevel)
    (q : Fin r → ℕ) (a : Fin r → ℂ) (hq : ∀ i, (q i).Prime)
    (ha : ∀ i, ‖a i‖ ≤ (q i : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    (∏ i, (1 - a i * ι (η.2 (q i)) / (q i : ℂ) ^ (k / 2))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact quadratic_euler_factor_ne_zero heven (hq i) ι η (a i) (ha i)

end HorizontalPadicL

open HorizontalPadicL

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  obtain ⟨M, hM, _, g, hfg, hg⟩ := f.exists_sameHeckeSystem_hasMinimalLevel hN
  obtain ⟨η, hη, horder, hcop, hnonzero⟩ :=
    g.friedberg_hoffstein_nonzero_of_hasMinimalLevel hM hk heven ι hg (N * d)
      (Nat.mul_pos hN hd)
  have hNd : Nat.Coprime (N * d) η.2.conductor := (Nat.coprime_mul_iff_left.mp hcop).2
  have hNM : Nat.Coprime (N * M) η.2.conductor :=
    Nat.coprime_mul_iff_left.mpr
      ⟨(Nat.coprime_mul_iff_left.mp hNd).1, (Nat.coprime_mul_iff_left.mp hcop).1⟩
  obtain ⟨r, q, a, hqa, hvalue⟩ :=
    f.quadratic_centralValue_eq_eulerFactors_mul_of_hasMinimalLevel
      hN hM hk heven ι g hfg hg η hη horder hNM
  refine ⟨η, hη, horder, hNd, ?_⟩
  rw [hvalue]
  exact mul_ne_zero
    (quadratic_euler_factor_prod_ne_zero heven ι η q a
      (fun i ↦ (hqa i).1) (fun i ↦ (hqa i).2.2)) hnonzero
