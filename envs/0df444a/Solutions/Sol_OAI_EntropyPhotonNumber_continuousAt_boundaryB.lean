-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.continuousAt_boundaryB
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:03:24.167297+00:00
-- url     : https://prove2.me/submissions/6b773ff7-021a-40b2-b295-d9087c2cb5ea

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Functions.lean:L1255-L1270
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.continuousAt_boundaryB. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_closedSineQuadrant

-- ---- from OAI.InformationTheory.PhotonNumber.Functions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

open Set Filter Topology

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric

namespace EntropyPhotonNumber

open Set Filter Topology
theorem continuousOn_closedSineInverse : ContinuousOn closedSineInverse closedSineQuadrant := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : closedSineQuadrant.domRestrict closedSineInverse =
      fun w : closedSineQuadrant => (closedSineHomeomorph.symm w).val := by
    funext w
    simp only [domRestrict_apply, closedSineInverse, dite_eq_left w.property]
  rw [he]
  exact continuous_subtype_val.comp closedSineHomeomorph.symm.continuous

theorem continuousAt_ccot {z : ℂ} (hz : csinc z ≠ 0) : ContinuousAt ccot z :=
  Complex.continuous_cos.continuousAt.div continuous_csinc.continuousAt hz

theorem continuous_upperReflect : Continuous upperReflect := by
  have he : upperReflect = fun s : ℂ => (s.re : ℂ) + ((|s.im| : ℝ) : ℂ) * I := by
    funext s
    apply Complex.ext <;> simp [upperReflect]
  rw [he]
  fun_prop

theorem continuousAt_reflectedRoot {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (fun z => (Complex.sqrt (upperReflect z))⁻¹) s := by
  have hm : (Complex.sqrt (upperReflect s))⁻¹ ∈ closedSineQuadrant :=
    inv_sqrt_mem_closedSineQuadrant hs (abs_nonneg _)
  have hn : Complex.sqrt (upperReflect s) ≠ 0 := by
    intro he
    have hp := hm.1
    simp only [he, inv_zero, Complex.zero_re, lt_self_iff_false] at hp
  have hc : ContinuousAt Complex.sqrt (upperReflect s) :=
    Complex.continuousAt_sqrt (Or.inl hs.le)
  exact (hc.comp continuous_upperReflect.continuousAt).inv₀ hn

theorem continuousAt_boundaryB {x : ℝ} (hx : 0 < x) : ContinuousAt boundaryB (x : ℂ) := by
  let U : Set ℂ := {s | 0 < s.re}
  let r : ℂ → ℂ := fun s => (Complex.sqrt (upperReflect s))⁻¹
  have hmaps : MapsTo r U closedSineQuadrant := fun s hs =>
    inv_sqrt_mem_closedSineQuadrant hs (abs_nonneg _)
  have hr : ContinuousOn r U := fun s hs => (continuousAt_reflectedRoot hs).continuousWithinAt
  have ht : ContinuousAt (closedSineInverse ∘ r) (x : ℂ) :=
    (continuousOn_closedSineInverse.comp hr hmaps).continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
  have hm : r (x : ℂ) ∈ closedSineQuadrant := hmaps hx
  have hn : csinc (closedSineInverse (r (x : ℂ))) ≠ 0 := by
    rw [csinc_closedSineInverse hm]
    intro he
    have hp := hm.1
    simp only [he, Complex.zero_re, lt_self_iff_false] at hp
  exact (continuousAt_ccot hn).comp (f := closedSineInverse ∘ r) ht

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.continuousAt_boundaryB := @_root_.OAI.EntropyPhotonNumber.continuousAt_boundaryB
