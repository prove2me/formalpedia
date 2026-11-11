-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:12:16.501929+00:00
-- url     : https://prove2.me/submissions/c3ca44bd-49fd-46ce-9f3c-0e9da4662dff

import Mathlib
import Definitions.Def_OAIQ239Tc003

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricTensor
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma christoffel_symm (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v : V) :
    christoffel G u v = christoffel G v u := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG w u v]
  ring

lemma christoffel_metric (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v w : V) :
    ⟪christoffel G u v,w⟫ + ⟪v,christoffel G u w⟫ = G u v w := by
  rw [real_inner_comm (y := v)]
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG u w v, hG w u v, hG v u w]
  ring

lemma coordinateJet_hasFDerivAt (G : MetricDerivative (V := V)) (z : V) :
    HasFDerivAt (coordinateJet G)
      (ContinuousLinearMap.id ℝ V - (1/2 : ℝ) •
        (christoffel G z + (christoffel G).flip z)) z := by
  convert! (hasFDerivAt_id z).sub
    (((christoffel G).hasFDerivAt.clm_apply (hasFDerivAt_id z)).const_smul (1/2 : ℝ)) using 1
  all_goals try with_reducible_and_instances rfl

lemma coordinateJet_hasFDerivAt_normal (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (z : V) :
    HasFDerivAt (coordinateJet G) (normalJacobian G z) z := by
  convert coordinateJet_hasFDerivAt G z using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [normalJacobian, sub_apply, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [christoffel_symm G hG v z]
  module

lemma normalJacobian_apply_hasFDerivAt (G : MetricDerivative (V := V)) (z v : V) :
    HasFDerivAt (fun y => normalJacobian G y v) (-(christoffel G).flip v) z := by
  exact ((christoffel G).flip v).hasFDerivAt.const_sub v

lemma pullbackMetric_scalar_hasFDerivAt_zero_oai (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hg0 : g 0 = innerSL ℝ) (hG : ∀ u v w, G u v w = G u w v) (v w : V) :
    HasFDerivAt (fun z => pullbackMetric g G z v w) (0 : V →L[ℝ] ℝ) 0 := by
  have hφ : HasFDerivAt (coordinateJet G) (ContinuousLinearMap.id ℝ V) 0 := by
    simpa using coordinateJet_hasFDerivAt_normal G hG 0
  have hg' : HasFDerivAt g G (coordinateJet G 0) := by simpa using hg
  have hgc := HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := V)
    (G := MetricTensor (V := V)) (f := coordinateJet G) (f' := ContinuousLinearMap.id ℝ V)
    (g := g) (g' := G) (0 : V) hg' hφ
  simp only [ContinuousLinearMap.comp_id] at hgc
  have h := (hgc.clm_apply (normalJacobian_apply_hasFDerivAt G 0 v)).clm_apply
    (normalJacobian_apply_hasFDerivAt G 0 w)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  simp only [Function.comp_apply, coordinateJet_zero, normalJacobian_zero, ContinuousLinearMap.id_apply,
    hg0, ContinuousLinearMap.comp_apply, add_apply, neg_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  change 0 = ⟪v, -christoffel G u w⟫ + (⟪-christoffel G u v,w⟫ + G u v w)
  simp only [inner_neg_left, inner_neg_right]
  have hm := christoffel_metric G hG u v w
  linarith

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero_oai.{u_1}
