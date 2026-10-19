-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:08:48.244617+00:00
-- url     : https://prove2.me/submissions/87a0752b-067e-45ad-8a8b-e97365bdcc36

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean:L394-L412
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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
lemma integral_circle_fourier (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) = if n=0 then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using! hh

lemma integrable_cont {X : Type uX} {E : Type uE} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E} (h : Continuous f) :
    Integrable f μ := h.integrable_of_hasCompactSupport (.of_compactSpace _)

open UnitAddTorus

lemma integral_character {n : ℕ} (s : Fin n → ℤ) :
    (∫ x : Fin n → UnitAddCircle, mFourier s x) = if s=0 then 1 else 0 := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_circle_fourier]
  by_cases hs : s=0
  · simp [hs]
  · rw [ite_eq_right hs]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi

lemma coeff_finite_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (s : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ ∑ t ∈ c.support, c t*mFourier t x) s = c s := by
  classical
  unfold mFourierCoeff
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · have he (t : Fin n → ℤ) :
        (fun x : Fin n → UnitAddCircle ↦ mFourier (-s) x*(c t*mFourier t x)) =
        (fun x ↦ c t*mFourier (t-s) x) := by
      ext x
      rw [sub_eq_add_neg, mFourier_add]
      ring
    simp_rw [he, integral_const_mul, integral_character]
    have hz (t : Fin n → ℤ) : t-s=0 ↔ t=s := sub_eq_zero
    simp_rw [hz, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq' _ _ _ |>.trans (by split_ifs with h <;> simp_all)
  · intro t ht
    apply integrable_cont
    fun_prop

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


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.coeff_finite_sum
