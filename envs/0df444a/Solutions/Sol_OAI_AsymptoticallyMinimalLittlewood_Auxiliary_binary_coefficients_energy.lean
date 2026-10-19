-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:10:20.428706+00:00
-- url     : https://prove2.me/submissions/50df8989-3aa1-401c-92fc-c514d2d7f68a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean:L432-L450
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_coeff_finite_sum

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI
open UnitAddTorus

lemma parseval_continuous {n : ℕ} (f : C((Fin n → UnitAddCircle), ℂ)) :
    HasSum (fun s ↦ ‖mFourierCoeff f s‖^2) (∫ x, ‖f x‖^2) := by
  have hh := hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with x hx
  rw [hx]

lemma binary_coefficients_energy {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (he : ∀ x, (binary n x : ℂ) = ∑ s ∈ c.support, c s*mFourier s x) :
    (∑ s ∈ c.support, ‖c s‖^2) = energy n := by
  classical
  let f : C((Fin n → UnitAddCircle),ℂ) := ⟨fun x ↦ (binary n x : ℂ), by fun_prop⟩
  have hf : ∀ s, mFourierCoeff f s = c s := by
    intro s
    convert coeff_finite_sum c s using 1
    exact congrArg (fun g ↦ mFourierCoeff g s) (funext he)
  have hh := parseval_continuous f
  simp_rw [hf] at hh
  have he' : (∫ x, ‖f x‖^2) = energy n := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [f, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he'] at hh
  have hs : HasSum (fun s ↦ ‖c s‖^2) (∑ s ∈ c.support, ‖c s‖^2) :=
    hasSum_sum_of_ne_finset_zero (fun s hs ↦ by simp [Finsupp.notMem_support_iff.mp hs])
  exact hs.unique hh

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
open UnitAddTorus
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_coefficients_energy
