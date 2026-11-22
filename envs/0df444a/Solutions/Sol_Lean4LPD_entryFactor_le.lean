-- Prove2me | solution 1 for Lean4LPD.entryFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:59.684101+00:00
-- url     : https://prove2.me/submissions/5742b77d-ddc7-4424-bdbf-1ef304c1772f

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Theorems.Thm_Lean4LPD_rungW_nonneg
public import Theorems.Thm_Lean4LPD_epsJump_nonneg
public import Theorems.Thm_Lean4LPD_entryFactor_le_geom

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb : betaOf kh1 c a ≤ 1 / 2) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu * (1 + 2 * betaOf kh1 c a) := by
  set b := betaOf kh1 c a with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; unfold betaOf
    have hw2 : 0 ≤ rungW kh1 c 2 := rungW_nonneg hkh hc (by omega)
    have := Real.exp_pos 1
    positivity
  have hb1 : b < 1 := by linarith
  have hgeom := entryFactor_le_geom hkh hc ha hnu (by rw [← hbdef] at *; linarith)
  have heps : 0 ≤ epsJump kh1 c a nu nu :=
    epsJump_nonneg hkh hc ha nu nu (by omega)
  have hkey : epsJump kh1 c a nu nu / (1 - b)
      ≤ epsJump kh1 c a nu nu * (1 + 2 * b) := by
    rw [div_le_iff₀ (by linarith)]
    have hprod : (0 : ℝ) ≤ epsJump kh1 c a nu nu * (b * (1 - 2 * b)) :=
      mul_nonneg heps (mul_nonneg hb0 (by linarith))
    nlinarith [hprod]
  rw [← hbdef] at hgeom
  linarith [hgeom, hkey]
end Lean4LPD
