-- Prove2me | solution 1 for OAI.Solenoidal.periodic_transport_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:05:51.595739+00:00
-- url     : https://prove2.me/submissions/a037040c-4d33-497b-b2ab-e2acdd42b8e6

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/ClassicalRegularity.lean:L195-L212
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.periodic_transport_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Theorems.Thm_OAI_Solenoidal_periodic_integral_divergence_zero_C1

-- ---- from OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity ----
namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem scalarPartial_mul {g h : Space → ℝ}
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (x : Space) (j : Fin 3) :
    fderiv ℝ (g * h) x (basis j) =
      g x * fderiv ℝ h x (basis j) + h x * fderiv ℝ g x (basis j) := by
  rw [fderiv_mul (hg x) (hh x)]
  rfl

theorem TorusC1.mul {g h : Space → ℝ} (hg : TorusC1 g) (hh : TorusC1 h) :
    TorusC1 (g * h) := by
  refine ⟨hg.differentiable.mul hh.differentiable, ?_, ?_⟩
  · intro j
    simp only [scalarPartial_mul hg.differentiable hh.differentiable]
    exact (hg.differentiable.continuous.fun_mul (hh.continuous_partial j)).add
      (hh.differentiable.continuous.fun_mul (hg.continuous_partial j))
  · intro x k
    simp only [Pi.mul_apply, hg.periodic, hh.periodic]

theorem fderiv_component {g : Space → Space} (hg : Differentiable ℝ g)
    (k : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => g y k) x v = fderiv ℝ g x v k := by
  rw [fderiv_pi (φ := fun j y => g y j) (fun j =>
    (differentiable_apply j).fun_comp hg |>.differentiableAt)]
  rfl

theorem TorusC1.component {g : Space → Space} (hg : TorusC1 g) (k : Fin 3) :
    TorusC1 (fun x => g x k) := by
  refine ⟨(differentiable_apply k).fun_comp hg.differentiable, ?_, ?_⟩
  · intro j
    simp only [fderiv_component hg.differentiable]
    exact (continuous_apply k).comp (hg.continuous_partial j)
  · intro x l
    rw [hg.periodic]

theorem fderiv_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (x d : Space) :
    fderiv ℝ g x d = ∑ j : Fin 3, d j • fderiv ℝ g x (basis j) := by
  have hd : d = ∑ j : Fin 3, d j • basis j := by
    ext k
    fin_cases k <;> simp [basis, Fin.sum_univ_succ]
  conv_lhs => rw [hd]
  simp only [map_sum, map_smul]

theorem periodic_transport_zero {q : Space → ℝ} {v : Space → Space}
    (hq : TorusC1 q) (hv : TorusC1 v)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ v x (basis j) j = 0) :
    (∫ x in fundamentalCell, fderiv ℝ q x (v x)) = 0 := by
  have hz := periodic_integral_divergence_zero_C1
    (fun j x => q x * v x j) (fun j => hq.mul (hv.component j))
  have he (x : Space) :
      (∑ j, fderiv ℝ (fun y => q y * v y j) x (basis j)) =
        fderiv ℝ q x (v x) := by
    have hmul (j : Fin 3) : fderiv ℝ (fun y => q y * v y j) x (basis j) =
        q x * fderiv ℝ (fun y => v y j) x (basis j) +
          v x j * fderiv ℝ q x (basis j) :=
      scalarPartial_mul hq.differentiable (hv.component j).differentiable x j
    simp only [hmul, fderiv_component hv.differentiable, Finset.sum_add_distrib,
      ← Finset.mul_sum, hdiv, mul_zero, zero_add]
    rw [fderiv_apply_eq_sum]
    rfl
  simpa only [he] using hz

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.periodic_transport_zero := @_root_.OAI.Solenoidal.periodic_transport_zero
