-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:19:17.23476+00:00
-- url     : https://prove2.me/submissions/c72055ec-5324-4ae6-b3d0-55758c403ad9

import Mathlib
import Definitions.Def_OAIQ239Tc008

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_OperatorCalculus
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [Fintype ι] [CompleteSpace W] [CompleteSpace Q] in
lemma derivative_apply (A : V → W →L[ℝ] Q) (u : V → W) {x : V}
    (hA : DifferentiableAt ℝ A x) (hu : DifferentiableAt ℝ u x) (v : V) :
    fderiv ℝ (fun y => A y (u y)) x v =
      (fderiv ℝ A x v) (u x) + A x (fderiv ℝ u x v) := by
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm] using
    congrArg (fun C : V →L[ℝ] Q => C v) (hA.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv

omit [Fintype ι] [CompleteSpace W] in
lemma derivative_sum (f : ι → V → W) (s : Finset ι) {x : V}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (v : V) :
    fderiv ℝ (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, fderiv ℝ (f i) x v := by
  simpa only [sum_apply] using congrArg (fun C : V →L[ℝ] W => C v)
    (HasFDerivAt.fun_sum (fun i hi => (hf i hi).hasFDerivAt)).fderiv

lemma square_expansion (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (u : V → W) {x : V}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ x) (hρx : ρ x ≠ 0) (hu : ContDiffAt ℝ 2 u x) :
    weightedAdjoint e a b ρ (differential e a b u) x =
      -(∑ i, ∑ j, (a i x).adjoint (a j x
        (fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)))) +
      (∑ j, firstMatrix e a b ρ j x (fderiv ℝ u x (e j))) +
      zeroMatrix e a b ρ x (u x) := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hu' : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hdu (j : ι) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e j)) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hc (i : ι) : DifferentiableAt ℝ (fun y => (ρ y • a i y).adjoint) x :=
    S.differentiableAt.comp x (hρ.smul (ha i))
  have hm (i j : ι) : DifferentiableAt ℝ (principalMatrix a ρ i j) x :=
    (hc i).clm_comp (ha j)
  have hl (i : ι) : DifferentiableAt ℝ (lowerMatrix a b ρ i) x := (hc i).clm_comp hb
  have he (i : ι) : (fun y => (ρ y • a i y).adjoint (differential e a b u y)) =
      (fun y => (∑ j, principalMatrix a ρ i j y (fderiv ℝ u y (e j))) + lowerMatrix a b ρ i y (u y)) := by
    funext y
    simp only [differential,map_add,map_sum,principalMatrix,lowerMatrix,ContinuousLinearMap.comp_apply]
  have hde (i : ι) : fderiv ℝ (fun y => (ρ y • a i y).adjoint (differential e a b u y)) x (e i) =
      (∑ j, ((fderiv ℝ (principalMatrix a ρ i j) x (e i)) (fderiv ℝ u x (e j)) +
        principalMatrix a ρ i j x (fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)))) +
      (fderiv ℝ (lowerMatrix a b ρ i) x (e i)) (u x) + lowerMatrix a b ρ i x (fderiv ℝ u x (e i)) := by
    rw [he i, fderiv_fun_add (DifferentiableAt.fun_sum (u := Finset.univ) fun j _ => (hm i j).clm_apply (hdu j))
      ((hl i).clm_apply hu')]
    simp only [add_apply]
    rw [derivative_sum _ _ (fun j _ => (hm i j).clm_apply (hdu j)),derivative_apply _ _ (hl i) hu']
    simp_rw [derivative_apply _ _ (hm i _) (hdu _)]
    abel
  rw [weightedAdjoint]
  simp_rw [hde]
  have hp (i j : ι) (v : W) : -(ρ x)⁻¹ • principalMatrix a ρ i j x v =
      -(a i x).adjoint (a j x v) := by
    simp only [principalMatrix,ContinuousLinearMap.comp_apply,map_smul,smul_apply,
      smul_smul,neg_mul,inv_mul_cancel₀ hρx,neg_smul,one_smul]
  have hlow (i : ι) (v : W) : -(ρ x)⁻¹ • lowerMatrix a b ρ i x v =
      -(a i x).adjoint (b x v) := by
    simp only [lowerMatrix,ContinuousLinearMap.comp_apply,map_smul,smul_apply,
      smul_smul,neg_mul,inv_mul_cancel₀ hρx,neg_smul,one_smul]
  simp only [differential,firstMatrix,zeroMatrix,map_add,map_sum,add_apply,
    sub_apply,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    smul_add,Finset.smul_sum,hp,hlow,Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun i j => -(ρ x)⁻¹ • (fderiv ℝ (principalMatrix a ρ i j) x (e i)) (fderiv ℝ u x (e j)))]
  abel

omit [Fintype ι] [CompleteSpace W] in
lemma second_eq (u : V → W) {x : V} (hu : ContDiffAt ℝ 2 u x) (v w : V) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = fderiv ℝ (fderiv ℝ u) x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add] using
    congrArg (fun C : V →L[ℝ] W => C v)
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv

omit [Fintype ι] [CompleteSpace W] in
lemma second_symm (u : V → W) {x : V} (hu : ContDiffAt ℝ 2 u x) (v w : V) :
    fderiv ℝ (fun y => fderiv ℝ u y w) x v = fderiv ℝ (fun y => fderiv ℝ u y v) x w := by
  rw [second_eq u hu,second_eq u hu]
  exact (hu.isSymmSndFDerivAt (by norm_num)).eq v w

lemma scalar_principal (e : ι → V) (a : ι → W →L[ℝ] Q) (g : ι → ι → ℝ)
    (hp : ∀ i j, (a i).adjoint ∘L a j + (a j).adjoint ∘L a i =
      (2*g i j) • ContinuousLinearMap.id ℝ W)
    (u : V → W) {x : V} (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, ∑ j, (a i).adjoint (a j
      (fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)))) =
    ∑ i, ∑ j, g i j • fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i) := by
  let H : ι → ι → W := fun i j => fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)
  have hH : ∀ i j, H i j = H j i := fun i j => second_symm u hu (e i) (e j)
  change (∑ i, ∑ j, (a i).adjoint (a j (H i j))) = ∑ i, ∑ j, g i j • H i j
  apply smul_right_injective W (two_ne_zero : (2 : ℝ) ≠ 0)
  dsimp only
  rw [two_smul ℝ]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  simp_rw [←Finset.sum_add_distrib]
  calc
    (∑ i, ∑ j, ((a i).adjoint (a j (H i j)) + (a j).adjoint (a i (H j i)))) =
        ∑ i, ∑ j, (2*g i j) • H i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hH j i]
      exact congrArg (fun A : W →L[ℝ] W => A (H i j)) (hp i j)
    _ = (2:ℝ) • ∑ i, ∑ j, g i j • H i j := by simp [Finset.smul_sum,mul_smul]

lemma square_scalar_expansion (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → ℝ) (u : V → W) {x : V}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ x) (hρx : ρ x ≠ 0) (hu : ContDiffAt ℝ 2 u x)
    (hp : ∀ i j, (a i x).adjoint ∘L a j x + (a j x).adjoint ∘L a i x =
      (2*g i j) • ContinuousLinearMap.id ℝ W) :
    weightedAdjoint e a b ρ (differential e a b u) x =
      -(∑ i, ∑ j, g i j • fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)) +
      (∑ j, firstMatrix e a b ρ j x (fderiv ℝ u x (e j))) + zeroMatrix e a b ρ x (u x) := by
  rw [square_expansion e a b ρ u ha hb hρ hρx hu,scalar_principal e (fun i => a i x) g hp u hu]

omit [Fintype ι] [CompleteSpace W] in
lemma gauge_second (U : V → W →L[ℝ] W) (u : V → W)
    (hU : ContDiff ℝ 2 U) (hu : ContDiff ℝ 2 u) (x v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => U z (u z)) y w) x v =
      (fderiv ℝ (fun y => fderiv ℝ U y w) x v) (u x) +
      (fderiv ℝ U x w) (fderiv ℝ u x v) + (fderiv ℝ U x v) (fderiv ℝ u x w) +
      U x (fderiv ℝ (fun y => fderiv ℝ u y w) x v) := by
  have hU' : ∀ y, DifferentiableAt ℝ U y := hU.differentiable (by norm_num)
  have hu' : ∀ y, DifferentiableAt ℝ u y := hu.differentiable (by norm_num)
  have hDU : DifferentiableAt ℝ (fun y => fderiv ℝ U y w) x :=
    (((hU.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
    (((hu.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  simp_rw [derivative_apply U u (hU' _) (hu' _)]
  rw [fderiv_fun_add (hDU.clm_apply (hu' x)) ((hU' x).clm_apply hdu)]
  simp only [add_apply]
  rw [derivative_apply _ _ hDU (hu' x),derivative_apply _ _ (hU' x) hdu]
  abel

lemma gauge_transform (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c U : V → W →L[ℝ] W) (u : V → W)
    (hU : ContDiff ℝ 2 U) (hu : ContDiff ℝ 2 u) (x : V)
    (horth : (U x).adjoint ∘L U x = ContinuousLinearMap.id ℝ W) :
    (U x).adjoint (secondOrder e a b c (fun z => U z (u z)) x) =
      secondOrder e a (gaugeFirst e a b U) (gaugeZero e a b c U) u x := by
  have hcancel (v : W) : (U x).adjoint (U x v) = v :=
    congrArg (fun A : W →L[ℝ] W => A v) horth
  have hder (j : ι) := derivative_apply U u (hU.differentiable (by norm_num) x)
    (hu.differentiable (by norm_num) x) (e j)
  simp only [secondOrder,gauge_second U u hU hu,hder,gaugeFirst,gaugeZero,
    ContinuousLinearMap.comp_apply,add_apply,sub_apply,sum_apply,smul_apply,
    map_add,map_sub,map_sum,map_smul,map_neg,hcancel,smul_add,
    add_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => a j i x • (U x).adjoint
    ((fderiv ℝ U x (e j)) (fderiv ℝ u x (e i))))]
  abel

lemma gauge_formal_square (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → V → ℝ)
    (U : V → W →L[ℝ] W) (u : V → W) (hU : ContDiff ℝ 2 U) (hu : ContDiff ℝ 2 u)
    {x : V} (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ x) (hρx : ρ x ≠ 0)
    (hp : ∀ i j, (a i x).adjoint ∘L a j x + (a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ W)
    (horth : (U x).adjoint ∘L U x = ContinuousLinearMap.id ℝ W) :
    (U x).adjoint (weightedAdjoint e a b ρ (differential e a b (fun y => U y (u y))) x) =
      secondOrder e g (gaugeFirst e g (firstMatrix e a b ρ) U)
        (gaugeZero e g (firstMatrix e a b ρ) (zeroMatrix e a b ρ) U) u x := by
  rw [square_scalar_expansion e a b ρ (fun i j => g i j x) (fun y => U y (u y))
    ha hb hρ hρx (hU.clm_apply hu).contDiffAt hp]
  exact gauge_transform e g (firstMatrix e a b ρ) (zeroMatrix e a b ρ) U u hU hu x horth

end TamingCompatibility.GeometricHilbert.OperatorCalculus


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_FlatHeat
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

lemma heat_contDiff (t : ℝ) : ContDiff ℝ ∞ (heat t) := by
  exact contDiff_const.mul (((contDiff_id.norm_sq (𝕜 := ℝ)).neg.div_const (4*t)).exp)

lemma heat_hasDerivAt_time {t : ℝ} (ht : 0 < t) (z : V) :
    HasDerivAt (fun s => heat s z) ((-2/t+‖z‖^2/(4*t^2))*heat t z) t := by
  have hc : HasDerivAt (fun s : ℝ => 4*Real.pi*s) (4*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4*Real.pi)
  have hi := (hc.inv (by positivity)).pow 2
  have hd := (hasDerivAt_const t (-‖z‖^2)).div
    ((hasDerivAt_id t).const_mul 4) (by positivity)
  have h := hi.mul hd.exp
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [heat, Pi.inv_apply, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, id_eq]
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring_nf
  field_simp [ne_of_gt ht, Real.pi_ne_zero]

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat
open scoped ContDiff
variable {W Q : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma actual_cutoff_residual_oai (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (g : Fin 4 → Fin 4 → V → ℝ) (U : V → W →L[ℝ] W)
    (hU : ContDiff ℝ ∞ U) (horth : ∀ z, (U z).adjoint ∘L U z = ContinuousLinearMap.id ℝ W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {z : V} (ha : ∀ i, DifferentiableAt ℝ (a i) z) (hb : DifferentiableAt ℝ b z)
    (hρ : DifferentiableAt ℝ ρ z) (hρz : ρ z ≠ 0)
    (hp : ∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
      (2*g i j z) • ContinuousLinearMap.id ℝ W) {t : ℝ} (ht : 0 < t) (u : W) :
    (U z).adjoint (deriv (fun s => U z (χ z • modelSection s u z)) t +
      weightedAdjoint (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ
        (differential (EuclideanSpace.basisFun (Fin 4) ℝ) a b
          (fun y => U y (χ y • modelSection t u y))) z) =
      deriv (fun s => χ z • modelSection s u z) t +
        secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g
          (gaugeFirst (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (gaugeZero (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ)
            (zeroMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (fun y => χ y • modelSection t u y) z := by
  have hU2 : ContDiff ℝ 2 U := hU.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hm0 : ContDiff ℝ ∞ (fun y : V => χ y • modelSection t u y) :=
    hχ.smul ((heat_contDiff t).smul contDiff_const)
  have hm : ContDiff ℝ 2 (fun y => χ y • modelSection t u y) :=
    hm0.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hd := ((heat_hasDerivAt_time ht z).smul_const u).const_smul (χ z)
  have htime : deriv (fun s => U z (χ z • modelSection s u z)) t =
      U z (deriv (fun s => χ z • modelSection s u z) t) :=
    ((U z).hasFDerivAt.comp_hasDerivAt t hd).deriv.trans (congrArg (U z) hd.deriv.symm)
  have hcancel (v : W) : (U z).adjoint (U z v) = v :=
    congrArg (fun C : W →L[ℝ] W => C v) (horth z)
  rw [map_add,htime,hcancel]
  congr 1
  exact gauge_formal_square _ a b ρ g U _ hU2 hm ha hb hρ hρz hp (horth z)

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.actual_cutoff_residual_oai.{u_1, u_2}
