-- Prove2me | solution 1 for GlobalTheory.SplitWeil.fourier_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:01.274153+00:00
-- url     : https://prove2.me/submissions/bb46403b-78b0-4fa5-bceb-ecf02a7578dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_exists_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ c) {s : kˣ} {f : k → ℂ}
    (hs : ∀ t ∈ cball s, ∀ x, f (x + t) = f x) {y : k} (hy : y ∉ cball (c * s⁻¹)) :
    ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = 0 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hy
  have h1 := integral_add_right_eq_self (μ := ν) (fun x => f x * (ψ (x * y) : ℂ)) t
  have h2 : ∀ x, f (x + t) * (ψ ((x + t) * y) : ℂ) = (ψ (t * y) : ℂ) * (f x * (ψ (x * y) : ℂ)) := by
    intro x
    rw [hs t ht, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]
end GlobalTheory.SplitWeil
