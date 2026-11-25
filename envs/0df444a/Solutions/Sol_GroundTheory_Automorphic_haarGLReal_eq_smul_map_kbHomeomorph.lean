-- Prove2me | solution 1 for GroundTheory.Automorphic.haarGLReal_eq_smul_map_kbHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:47.065679+00:00
-- url     : https://prove2.me/submissions/b1618bfc-22b4-4f8e-a513-5c0bfd51db48

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Theorems.Thm_GroundTheory_Automorphic_kbInvHomeomorph_equivariant
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace GroundTheory.Automorphic
theorem _root_.solution (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLReal μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by
  set H := haarGLReal μ₀ with hHdef
  set f := kbInvHomeomorph (n := n)
  set ν := Measure.map f H with hνdef
  have hν : ν.IsMulLeftInvariant := ⟨fun q => by
    rw [hνdef, Measure.map_map (measurable_const_mul q) f.measurable]
    have e1 : (fun x => q * x) ∘ f =
        f ∘ (fun g => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) :=
      funext fun g => (kbInvHomeomorph_equivariant q g).symm
    have e2 : (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) =
        (fun g => g * ((q.2 : GL n ℝ))⁻¹) ∘ (fun g => Unitary.toUnits q.1 * g) := rfl
    have hmT : Measurable (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) := by
      rw [e2]; exact (measurable_mul_const _).comp (measurable_const_mul _)
    rw [e1, ← Measure.map_map f.measurable hmT, e2,
      ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]⟩
  have hνc : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map H f
  obtain ⟨c, key⟩ : ∃ c : ℝ≥0, ν = c • μK.prod μB :=
    ⟨_, isMulLeftInvariant_eq_smul ν (μK.prod μB)⟩
  have hH : H = Measure.map f.symm ν := by
    rw [hνdef, Measure.map_map f.symm.measurable f.measurable]
    simp
  refine ⟨c, ?_, ?_⟩
  · intro hc
    rw [hc, zero_smul] at key
    have h0 : H Set.univ = 0 := by rw [hH, key, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]
    exact (IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h0
  · rw [hH, key, Measure.map_smul]
    congr 1
    have e3 : ⇑f.symm = kbHomeomorph ∘ Prod.map id (fun b : upperPosSubgroup n ℝ => b⁻¹) := by
      funext p; rfl
    rw [e3, ← Measure.map_map kbHomeomorph.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, Measure.inv_def]
end GroundTheory.Automorphic
