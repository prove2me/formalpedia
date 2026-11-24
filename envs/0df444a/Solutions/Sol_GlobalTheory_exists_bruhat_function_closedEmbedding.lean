-- Prove2me | solution 1 for GlobalTheory.exists_bruhat_function_closedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:03.945521+00:00
-- url     : https://prove2.me/submissions/6bbb113b-d780-434f-be77-58474c6fe6ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionOfClosedEmbedding
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
import Theorems.Thm_GlobalTheory_exists_bruhat_function_closed_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1
end GlobalTheory
