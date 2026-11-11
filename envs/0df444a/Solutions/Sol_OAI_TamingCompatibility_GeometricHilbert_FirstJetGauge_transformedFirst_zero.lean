-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:15:33.146637+00:00
-- url     : https://prove2.me/submissions/b51985e4-286f-46d3-add0-cb4ff0316168

import Mathlib
import Definitions.Def_OAIQ239Tc007

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_hasFDerivAt_zero (A : V →L[ℝ] End (W := W)) :
    HasFDerivAt (gauge A) A 0 := by
  have he : HasFDerivAt (NormedSpace.exp : End (W := W) → End (W := W)) (ContinuousLinearMap.id ℝ _) (A 0) := by
    simpa using! (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := End (W := W)))
  simpa [gauge] using! he.comp 0 A.hasFDerivAt

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FirstJetGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [CompleteSpace W] in
lemma halfJet_direction [DecidableEq ι] (q : ι → V →L[ℝ] ℝ) (e : ι → V)
    (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0) (b : ι → End (W := W)) (j : ι) :
    halfJet q b (e j) = (1/2:ℝ) • b j := by
  simp [halfJet, hqe]

lemma transformedFirst_zero_oai [DecidableEq ι]
    (q : ι → V →L[ℝ] ℝ) (e : ι → V)
    (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0)
    (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (ha : ∀ i j, a i j 0 = if i=j then 1 else 0) (j : ι) :
    transformedFirst a b (OrthogonalJets.gauge (halfJet q (fun i => b i 0))) e j 0 = 0 := by
  have hd := (OrthogonalJets.gauge_hasFDerivAt_zero (halfJet q (fun i => b i 0))).fderiv
  simp only [transformedFirst, OrthogonalJets.gauge_zero, hd, halfJet_direction q e hqe]
  have he : (∑ i, (a i j 0+a j i 0) • ((1/2:ℝ) • b i 0)) = b j 0 := by
    rw [Finset.sum_eq_single j]
    · simp only [ha, ite_true, if_true, smul_smul]
      norm_num
    · intro i _ hij
      simp [ha, hij, Ne.symm hij]
    · simp
  rw [he]
  simp [ContinuousLinearMap.one_def]

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

theorem solution.{u_1, u_2, u_4} : type_of% @OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero_oai.{u_1, u_2, u_4} := @OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero_oai.{u_1, u_2, u_4}
