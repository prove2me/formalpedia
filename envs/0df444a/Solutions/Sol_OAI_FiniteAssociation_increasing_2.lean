-- Prove2me | solution 2 for OAI.FiniteAssociation.increasing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:15:21.862674+00:00
-- url     : https://prove2.me/submissions/040c8c66-cbac-45d6-8e89-1ebe7cfe55c6

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ProductCylinder.lean:L154-L197
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteAssociation.increasing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

theorem extend_mono (b : Bool) : Monotone (fun ω : E → Bool => extend ω b) := by
  intro ω ω' h e
  cases e with
  | none => exact le_rfl
  | some e => exact h e

theorem extend_false_le_true (ω : E → Bool) : extend ω false ≤ extend ω true := by
  intro e
  cases e with
  | none => exact Bool.false_le _
  | some e => exact le_rfl

theorem mean_mono [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {f g : (E → Bool) → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean p f ≤ mean p g :=
  integral_mono Integrable.of_finite Integrable.of_finite h

theorem mean_option [Fintype E] (p : Option E → Set.Icc (0 : ℝ) 1)
    (f : (Option E → Bool) → ℝ) :
    mean p f = (p none : ℝ) * mean (fun e => p (some e)) (fun ω => f (extend ω true)) +
      (1 - (p none : ℝ)) * mean (fun e => p (some e)) (fun ω => f (extend ω false)) := by
  unfold mean law
  rw [← Measure.pi_map_piOptionEquivProd (fun i => bernoulliMeasure true false (p i))]
  rw [integral_map (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm.measurable.aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_prod _ Integrable.of_finite]
  have heq : ∀ ω b, (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm (ω,b) =
      extend ω b := by
    intro ω b
    funext e
    cases e <;> rfl
  simp_rw [heq,integral_bernoulliMeasure,smul_eq_mul]
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, integral_const_mul]

theorem mean_equiv {F : Type uF} [Fintype E] [Fintype F] (e : E ≃ F)
    (p : F → Set.Icc (0 : ℝ) 1) (f : (F → Bool) → ℝ) :
    mean p f = mean (fun a => p (e a)) (fun ω => f (fun b => ω (e.symm b))) := by
  have h := (measurePreserving_piCongrLeft (fun b => bernoulliMeasure true false (p b)) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e).measurableEmbedding f
  have he : ∀ ω, (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e) ω =
      fun b => ω (e.symm b) := by
    intro ω
    funext b
    change Equiv.piCongrLeft (fun _ : F => Bool) e ω b = ω (e.symm b)
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [mean,law,he,Function.comp_def] using h.symm

/-- Finite product positive association for arbitrary real increasing observables. -/
theorem increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h : ∀ (E : Type u) [Fintype E], ∀ (p : E → Set.Icc (0 : ℝ) 1)
      (f g : (E → Bool) → ℝ), Monotone f → Monotone g →
      mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
    apply Fintype.induction_empty_option
    · intro E F _ e ih p f g hf hg
      let _ : Fintype E := Fintype.ofEquiv F e.symm
      simp only [mean_equiv e p]
      apply ih
      · intro ω ω' h
        exact hf (fun b => h (e.symm b))
      · intro ω ω' h
        exact hg (fun b => h (e.symm b))
    · intro p f g _ _
      have heq (f : (PEmpty.{u+1} → Bool) → ℝ) : f = fun _ => f (fun x => x.elim) := by
        funext ω
        exact congrArg f (Subsingleton.elim _ _)
      rw [heq f,heq g]
      simp [mean]
    · intro E _ ih p f g hf hg
      let p' := fun e => p (some e)
      let f₀ := fun ω => f (extend ω false)
      let f₁ := fun ω => f (extend ω true)
      let g₀ := fun ω => g (extend ω false)
      let g₁ := fun ω => g (extend ω true)
      have h₀ := ih p' f₀ g₀ (hf.comp (extend_mono false)) (hg.comp (extend_mono false))
      have h₁ := ih p' f₁ g₁ (hf.comp (extend_mono true)) (hg.comp (extend_mono true))
      have hfm : mean p' f₀ ≤ mean p' f₁ := mean_mono p' (fun ω => hf (extend_false_le_true ω))
      have hgm : mean p' g₀ ≤ mean p' g₁ := mean_mono p' (fun ω => hg (extend_false_le_true ω))
      have hq0 : 0 ≤ (p none : ℝ) := (p none).2.1
      have hq1 : 0 ≤ 1 - (p none : ℝ) := sub_nonneg.mpr (p none).2.2
      have hc : 0 ≤ (p none : ℝ) * (1 - (p none : ℝ)) *
          (mean p' f₁ - mean p' f₀) * (mean p' g₁ - mean p' g₀) := by positivity
      have hsum := add_le_add (mul_le_mul_of_nonneg_left h₁ hq0) (mul_le_mul_of_nonneg_left h₀ hq1)
      simp only [mean_option]
      change ((p none : ℝ) * mean p' f₁ + (1 - (p none : ℝ)) * mean p' f₀) *
        ((p none : ℝ) * mean p' g₁ + (1 - (p none : ℝ)) * mean p' g₀) ≤
        (p none : ℝ) * mean p' (fun ω => f₁ ω * g₁ ω) +
        (1 - (p none : ℝ)) * mean p' (fun ω => f₀ ω * g₀ ω)
      nlinarith
  exact h E p f g hf hg

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- platform node ----
open OAI OAI.FiniteAssociation
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{u} : type_of% @_root_.OAI.FiniteAssociation.increasing.{u} := @_root_.OAI.FiniteAssociation.increasing.{u}
