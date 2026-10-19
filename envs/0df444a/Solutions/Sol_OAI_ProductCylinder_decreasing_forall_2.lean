-- Prove2me | solution 2 for OAI.ProductCylinder.decreasing_forall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:18:03.305602+00:00
-- url     : https://prove2.me/submissions/e9d408cb-5e28-409d-a851-9223189b0fac

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ProductCylinder.lean:L263-L288
-- (upload_full_project.md Phase 4): solution for node OAI.ProductCylinder.decreasing_forall. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Theorems.Thm_OAI_FiniteAssociation_prob_forall

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

theorem prob_eq_real [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : prob p P = (law p).real {ω | P ω} := by
  simpa [prob,mean,Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

theorem extend_mono (J : Finset E) : Monotone (extend J) := by
  intro ξ ζ h e
  by_cases he : e ∈ J
  · simp only [extend, dite_eq_left he]
    exact h ⟨e,he⟩
  · simp only [extend, dite_eq_right he, le_refl]

/-- Harris's finite-family inequality, applied to actual infinite-product cylinder events. -/
theorem decreasing_forall {I : Type uI} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (law p).real (A i)) ≤ (law p).real (⋂ i, A i) := by
  have he (i : I) : (law p).real (A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p (A i) (hA i)]
    rfl
  have hall : (law p).real (⋂ i, A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => ∀ i, extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def]
    have hd : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ ⋂ i, A i ↔ ω ∈ ⋂ i, A i) := by
      intro ω ω' h
      simp only [Set.mem_iInter]
      exact forall_congr' (fun i => hA i ω ω' h)
    rw [probability_determined J p (⋂ i,A i) hd]
    simp only [Set.mem_iInter]
    rfl
  rw [hall]
  simp_rw [he]
  simpa only [Finset.mem_univ,forall_true_left] using
    FiniteAssociation.prob_forall (fun e : J => p e) Finset.univ
      (fun i ξ => extend J ξ ∈ A i) (fun i _ => (hmono i).comp_monotone (extend_mono J))

end ProductCylinder

end OAI

-- ---- platform node ----
open OAI OAI.ProductCylinder
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uE,uI} : type_of% @_root_.OAI.ProductCylinder.decreasing_forall.{uE,uI} := @_root_.OAI.ProductCylinder.decreasing_forall.{uE,uI}
