-- Prove2me | solution 1 for GrayStability.contact_forms_not_stable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T10:10:50.379312+00:00
-- url     : https://prove2.me/submissions/b1018316-d899-4e74-9bd7-2c8f4610591f

import Theorems.Thm_ContactCalculus_strict_hopf_pullback_intertwines
import Theorems.Thm_FlowCalculus_unit_half_rotation_image_second_plane_zero
import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem solution :
    ¬ ∃ ψ : ℝ → E 4 → E 4, IsIsotopyOf unitSphereEquation ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet unitSphereEquation,
        ∀ v ∈ tangentSpace unitSphereEquation y,
          pullback (ψ t) (hopfFamily t) y v = hopfFamily 0 y v := by
  rintro ⟨ψ, hψ, hα⟩
  have ht : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hs : ContDiff ℝ ∞ (ψ 1) :=
    hψ.1.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hbij, hinj⟩ := hψ.2.2 1 ht
  have hR := ContactCalculus.strict_hopf_pullback_intertwines 1 (by norm_num)
    (ψ 1) hs hbij hinj (hα 1 ht)
  have hzero := FlowCalculus.unit_half_rotation_image_second_plane_zero (ψ 1) hs
    (by norm_num at hR ⊢; exact hR)
  have he : (![0, 0, 1, 0] : E 4) ∈ levelSet unitSphereEquation := by
    change unitSphereEquation _ = 0
    ext i
    norm_num [unitSphereEquation, Fin.sum_univ_succ]
  obtain ⟨y, hy, hye⟩ := hbij.2.2 he
  have hz := (hzero y hy).1
  rw [hye] at hz
  have : (1 : ℝ) = 0 := by simpa using hz
  exact one_ne_zero this
