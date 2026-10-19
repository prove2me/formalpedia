-- Prove2me | solution 2 for HorizontalPadicL.friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-10-18T18:44:52.798974+00:00
-- url     : https://prove2.me/submissions/dcaf9354-b34e-49de-aed4-36a61c6568b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MTT_HeckeEquivalence
import Mathlib.Data.Nat.Find
import Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_nonzero_of_hasMinimalLevel
import Theorems.Thm_MTT_Eigenform_quadratic_centralValue_ne_zero_iff_of_hasMinimalLevel

/- Source: Solutions/HeckeMinimalRepresentative.lean -/

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

/- Source: Solutions/FriedbergHoffsteinStrictReduction.lean -/

set_option autoImplicit false

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
  exact ⟨η, hη, horder, hNd,
    (f.quadratic_centralValue_ne_zero_iff_of_hasMinimalLevel
      hN hM hk heven ι g hfg hg η hη horder hNM).mpr hnonzero⟩
