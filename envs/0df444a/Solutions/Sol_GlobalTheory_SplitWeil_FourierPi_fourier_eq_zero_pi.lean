-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:01.263177+00:00
-- url     : https://prove2.me/submissions/bcf96ae3-5bca-411b-9053-92a51b9af19a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_exists_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) {s : kˣ}
    {f : (n → k) → ℂ} (hs : ∀ t ∈ box n s, ∀ x, f (x + t) = f x) {y : n → k} (hy : y ∉ box n (c * s⁻¹)) :
    ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball (c * s⁻¹) := by
    by_contra hne
    push Not at hne
    exact hy fun i _ => hne i
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hi
  have hbox : (Pi.single i t : n → k) ∈ box n s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  have h1 := integral_add_right_eq_self (μ := μ) (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) (Pi.single i t)
  have h2 : ∀ x, f (x + Pi.single i t) * (ψ ((x + Pi.single i t) ⬝ᵥ y) : ℂ) =
      (ψ (t * y i) : ℂ) * (f x * (ψ (x ⬝ᵥ y) : ℂ)) := by
    intro x
    rw [hs _ hbox, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y i) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]
end GlobalTheory.SplitWeil.FourierPi
