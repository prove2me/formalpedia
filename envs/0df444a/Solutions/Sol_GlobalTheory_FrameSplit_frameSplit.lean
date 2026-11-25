-- Prove2me | solution 1 for GlobalTheory.FrameSplit.frameSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:58.871893+00:00
-- url     : https://prove2.me/submissions/1b407b3f-686f-4db9-ab02-10e47d70d27f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeOfSection
import Theorems.Thm_GlobalTheory_FrameSplit_lintegral_le_of_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FrameSplit
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FrameSplit
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by
  intro r X R
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  refine lintegral_le_of_section (volume : Measure (Frame X.Ψ r)) (volume : Measure (V (nd X)))
    (fun y => WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
      ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2)
    ?_ ?_
    (fun z τ a c => if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0)
    ?_ _ ?_ ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fun_prop
  · intro x y
    ext j
    simp
  · intro z
    ext j
    have h := ((Fintype.equivFin (Ent X)).symm j).2.2
    simp only [dif_pos h]
    exact congrArg (fun k => z k) ((Fintype.equivFin (Ent X)).apply_symm_apply j)
  · apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop
  · intro z x
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    refine forall_congr' fun τ => forall_congr' fun a => forall_congr' fun c =>
      forall_congr' fun h => ?_
    rw [dif_neg h, zero_add]
  · intro C
    refine ⟨max (max C R) 0, fun x hx hC => ?_⟩
    have h0 : 0 ≤ max (max C R) 0 := le_max_right _ _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun c => ?_
    by_cases h : c < a
    · have := (PiLp.norm_apply_le _ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).trans hC
      have h' : ‖x τ a c‖ ≤ C := by
        have e := (Fintype.equivFin (Ent X)).symm_apply_apply ⟨τ, ⟨(a, c), h⟩⟩
        simp only at this
        erw [e] at this
        exact this
      exact h'.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hx τ a c h).trans ((le_max_right _ _).trans (le_max_left _ _))
end GlobalTheory.FrameSplit
