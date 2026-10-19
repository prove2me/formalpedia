-- Prove2me | solution 1 for OAI.HyperedgeComparison.independent_of_disjoint_bits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:35:30.101005+00:00
-- url     : https://prove2.me/submissions/c85f6235-dbcd-475b-b816-c0a8de172fd9

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
variable [Fintype E]
theorem hc_indep_disjoint_bits {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  have hI : iIndepFun (fun (e : E) (ω : E → Bool) => ω e) (law p) := by
    unfold law
    exact iIndepFun_pi (X := fun _ (b : Bool) => b) (fun _ => measurable_id.aemeasurable)
  have h2 := hI.indepFun_finset J Jᶜ disjoint_compl_right (fun e => measurable_pi_apply e)
  let F : (J → Bool) → ℝ := fun ξ => f (fun e => if h : e ∈ J then ξ ⟨e, h⟩ else false)
  let G : ((Jᶜ : Finset E) → Bool) → ℝ :=
    fun ξ => g (fun e => if h : e ∈ Jᶜ then ξ ⟨e, h⟩ else false)
  have hF : f = F ∘ (fun ω (i : J) => ω i) := by
    funext ω
    exact (hf _ _ (fun e he => by simp [he])).symm
  have hG : g = G ∘ (fun ω (i : (Jᶜ : Finset E)) => ω i) := by
    funext ω
    refine (hg _ _ (fun e he => ?_)).symm
    have : e ∈ Jᶜ := Finset.mem_compl.mpr he
    simp [this]
  rw [hF, hG]
  exact h2.comp (Measurable.of_discrete) (Measurable.of_discrete)

theorem solution (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  exact hc_indep_disjoint_bits p J f g hf hg

