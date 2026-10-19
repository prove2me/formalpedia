-- Prove2me | solution 2 for OAI.KervaireScalarPhase.phase_eq_arg_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:45:26.923292+00:00
-- url     : https://prove2.me/submissions/1c78f02d-c3df-4d12-b3c7-4cfed380e1ff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean:L72-L118
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireScalarPhase.phase_eq_arg_one_sub. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Theorems.Thm_OAI_KervaireScalarPhase_exp_two_arg

-- ---- from OAI.GroupTheory.Kervaire.ScalarPhase ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

theorem phase_exp (x : ℝ) :
    phase (Complex.exp (x * Complex.I)) = Int.fract (x / (2 * Real.pi)) := by
  rw [phase, Complex.arg_exp_mul_I]
  apply Int.fract_eq_fract.mpr
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  rw [← sub_div, toIocMod_sub_self]
  simp only [zsmul_eq_mul, Int.cast_neg]
  field_simp

theorem phase_exp_normalized (x : ℝ) :
    phase (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)) = Int.fract x := by
  rw [phase_exp]
  congr 1
  field_simp

/-- Exact scalar phase away from its cut, expressed by the logarithm in the disk. -/
theorem phase_eq_arg_one_sub {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    phase z = 1 / 2 + (1 - z).arg / Real.pi := by
  have hx : 1 - z ≠ 0 := sub_ne_zero.mpr hz'.symm
  have hc : z * star z = 1 := by
    simpa [Complex.normSq_eq_norm_sq, hz] using (Complex.mul_conj z)
  have hre : 0 < (1 - z).re := by
    have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, hz, pow_two] using Complex.normSq_eq_norm_sq z
    have hl : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
    have hne : z.re ≠ 1 := by
      intro h
      have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
      exact hz' (Complex.ext h hi)
    simpa using sub_pos.mpr (lt_of_le_of_ne hl hne)
  let f : ℝ := 1 / 2 + (1 - z).arg / Real.pi
  have hlow : -(Real.pi / 2) < (1-z).arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)
  have hupp : (1-z).arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hf0 : 0 ≤ f := by
    have hh : -(1/2:ℝ) < (1-z).arg / Real.pi :=
      (lt_div_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp [f]
    linarith
  have hf1 : f < 1 := by
    have hh : (1-z).arg / Real.pi < (1/2:ℝ) :=
      (div_lt_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp [f]
    linarith
  have hq : (1 - z) / star (1 - z) = -z := by
    apply (div_eq_iff (star_ne_zero.mpr hx)).mpr
    simp only [star_sub, star_one]
    linear_combination -hc
  have he : Complex.exp ((2 * Real.pi * f : ℝ) * Complex.I) = z := by
    have ha : ((2 * Real.pi * f : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I + ((2 * (1-z).arg : ℝ) : ℂ) * Complex.I := by
      dsimp [f]
      push_cast
      field_simp
    rw [ha, Complex.exp_add, Complex.exp_pi_mul_I, exp_two_arg _ hx, hq]
    ring
  calc
    phase z = phase (Complex.exp ((2 * Real.pi * f : ℝ) * Complex.I)) :=
      congrArg phase he.symm
    _ = Int.fract f := phase_exp_normalized f
    _ = 1 / 2 + (1-z).arg / Real.pi := Int.fract_eq_self.mpr ⟨hf0, hf1⟩

end KervaireScalarPhase

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireScalarPhase.phase_eq_arg_one_sub := @_root_.OAI.KervaireScalarPhase.phase_eq_arg_one_sub
