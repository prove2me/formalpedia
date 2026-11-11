-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:11:55.061421+00:00
-- url     : https://prove2.me/submissions/359029de-5fe5-4d92-bc32-1266a3594512

import Mathlib
import Definitions.Def_OAIQ239Tc003

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

lemma fderiv_adjoint (P : V → End (W := W)) {x : V}
    (hP : DifferentiableAt ℝ P x) (v : V) :
    fderiv ℝ (fun y => (P y).adjoint) x v = (fderiv ℝ P x v).adjoint := by
  have h := (adjointCLM.hasFDerivAt.comp x hP.hasFDerivAt).fderiv
  exact congrArg (fun f : V →L[ℝ] End (W := W) => f v) h

lemma squareFirst_skew (P' : ι → ι → End (W := W)) (a : ι → W →L[ℝ] Q)
    (b : W →L[ℝ] Q) (ρ : ℝ) (j : ι)
    (hP : ∀ i, (P' i j).adjoint = - P' i j) :
    (squareFirst P' a b ρ j).adjoint = - squareFirst P' a b ρ j := by
  simp [squareFirst, map_add, map_sub, map_smul, map_sum, hP,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  abel

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_WeightedPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open Filter
open scoped ContDiff Topology
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma weighted_principal_jet_skew_local (P : ι → ι → V → End (W := W))
    (g : ι → ι → V → ℝ) (ρ : V → ℝ) (x v : V) (i j : ι)
    (hP : ∀ i j, DifferentiableAt ℝ (P i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hstar : (fun y => (P i j y).adjoint) =ᶠ[𝓝 x] P j i)
    (hscalar : (fun y => P i j y + P j i y) =ᶠ[𝓝 x]
      (fun y => (2*(ρ y*g i j y)) • ContinuousLinearMap.id ℝ W))
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : fderiv ℝ (g i j) x = 0) :
    (fderiv ℝ (P i j) x v).adjoint = - fderiv ℝ (P i j) x v := by
  have hadj : fderiv ℝ (P j i) x v = (fderiv ℝ (P i j) x v).adjoint := by
    rw [← fderiv_adjoint (P i j) (hP i j) v,hstar.fderiv_eq]
  have hder := ((hρ.hasFDerivAt.mul (hg i j).hasFDerivAt).const_smul (2:ℝ)).smul_const
    (ContinuousLinearMap.id ℝ W)
  have hsum := ((hP i j).hasFDerivAt.add (hP j i).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => P i j y + P j i y) x = _ at hsum
  rw [hscalar.fderiv_eq] at hsum
  have hderEq : fderiv ℝ (fun y => (2*(ρ y*g i j y)) • ContinuousLinearMap.id ℝ W) x =
      ((2:ℝ) • (ρ x • fderiv ℝ (g i j) x + g i j x • fderiv ℝ ρ x)).smulRight
        (ContinuousLinearMap.id ℝ W) := by
    simpa only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using hder.fderiv
  rw [hderEq] at hsum
  have hv := congrArg (fun f : V →L[ℝ] End (W := W) => f v) hsum
  simp [hρ0,hg0] at hv
  rw [hadj] at hv
  exact eq_neg_of_add_eq_zero_right hv.symm

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma weightedPrincipal_adjoint (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ) (i j : ι) (x : V) :
    (weightedPrincipal a ρ i j x).adjoint = weightedPrincipal a ρ j i x := by
  simp [weightedPrincipal,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma weightedPrincipal_differentiableAt (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ)
    {x : V} (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x) (i j : ι) :
    DifferentiableAt ℝ (weightedPrincipal a ρ i j) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact ((S.differentiableAt.comp x (hρ.smul (ha i))).clm_comp (ha j))

variable [Fintype ι]

lemma actualSquareFirst_skew_oai (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → V → ℝ) (x : V)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
    (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hscalar : ∀ i j, (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z)
      =ᶠ[𝓝 x] (fun z => (2*(ρ z*g i j z)) • ContinuousLinearMap.id ℝ W))
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : ∀ i j, fderiv ℝ (g i j) x = 0) (j : ι) :
    (actualSquareFirst e a b ρ j x).adjoint = -actualSquareFirst e a b ρ j x := by
  apply squareFirst_skew
  intro i
  exact weighted_principal_jet_skew_local (weightedPrincipal a ρ) g ρ x (e i) i j
    (weightedPrincipal_differentiableAt a ρ ha hρ) hρ hg
    (Filter.Eventually.of_forall (weightedPrincipal_adjoint a ρ i j))
    (hscalar i j) hρ0 (hg0 i j)

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew_oai.{u_1, u_2, u_3, u_4} := @OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew_oai.{u_1, u_2, u_3, u_4}
