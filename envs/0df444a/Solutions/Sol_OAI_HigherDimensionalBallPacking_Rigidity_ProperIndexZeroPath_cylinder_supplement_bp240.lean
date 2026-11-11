-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.cylinder_supplement_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:21.14496+00:00
-- url     : https://prove2.me/submissions/4690aa27-7678-47bf-8b9e-6ce1c157c304

import Mathlib
import Definitions.Def_OAIQ240Bp017
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_indexZero_finite_stabilizer_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma local_indexZero_supplement {Z : Type*} [TopologicalSpace Z]
    {D : Z → X →L[ℝ] Y} (hD : Continuous D) {z : Z} (hDz : IsIndexZeroFredholm (D z)) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ V : Set Z,IsOpen V ∧ z∈V ∧ ∀ v∈V,Surjective ((D v).coprod E.subtypeL) := by
  obtain ⟨E,hE,P,hP⟩ := indexZero_finite_stabilizer_bp240 hDz
  let V := {v : Z | (D v+E.subtypeL.comp P).IsInvertible}
  have hVo : IsOpen V :=
    (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := X) (F := Y)).preimage (hD.add continuous_const)
  refine ⟨E,hE,V,hVo,hP,?_⟩
  intro v hv y
  obtain ⟨x,hx⟩ := hv.surjective y
  exact ⟨(x,P x),hx⟩

theorem compact_indexZero_supplement {Z : Type*} [TopologicalSpace Z]
    {D : Z → X →L[ℝ] Y} (hD : Continuous D) {K : Set Z} (hK : IsCompact K)
    (hDK : ∀ z∈K,IsIndexZeroFredholm (D z)) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ V : Set Z,IsOpen V ∧ K⊆V ∧ ∀ v∈V,Surjective ((D v).coprod E.subtypeL) := by
  classical
  choose E hE V hVo hVz hVS using fun z : K => local_indexZero_supplement hD (hDK z.val z.property)
  let (z : K) : FiniteDimensional ℝ (E z) := hE z
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hVo (by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hVz ⟨z,hz⟩⟩)
  let W := s.sup E
  refine ⟨W,inferInstance,⋃ z∈s,V z,isOpen_biUnion (fun z hz => hVo z),hs,?_⟩
  intro v hv y
  obtain ⟨z,hzs,hvz⟩ := mem_iUnion₂.mp hv
  obtain ⟨⟨x,e⟩,hxe⟩ := hVS z v hvz y
  have hEW : E z≤W := Finset.le_sup hzs
  refine ⟨(x,⟨(e:Y),hEW e.property⟩),?_⟩
  exact hxe

omit [CompleteSpace X] [CompleteSpace Y] in
lemma pathSpatialDerivative_continuous [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) :
    Continuous (pathSpatialDerivative F) :=
  ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous).clm_comp continuous_const

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma ProperIndexZeroPath.cylinder_supplement_bp240_oai {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL) := by
  let Z := {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let K := Prod.snd '' Z
  have hK : IsCompact K := h.zeroSet_compact.image continuous_snd
  have hKU : K⊆U := by rintro _ ⟨v,hv,rfl⟩; exact hv.2.1
  obtain ⟨E,hE,V,hVo,hKV,hVs⟩ := compact_indexZero_supplement
    (pathSpatialDerivative_continuous h.smooth) (isCompact_Icc.prod hK) (by
      intro v hv
      rw [pathSpatialDerivative_eq h.smooth]
      exact h.fredholm v.1 hv.1 v.2 (hKU hv.2))
  exact ⟨K,hK,hKU,(fun t ht x hx hz => ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩),E,hE,V,hVo,hKV,hVs⟩


end
open scoped Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.cylinder_supplement_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.cylinder_supplement_bp240_oai.{u_1, u_2}
