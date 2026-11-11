-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:18:53.396207+00:00
-- url     : https://prove2.me/submissions/b4488538-b0d3-48b4-96cb-57bb4241ab4e

import Mathlib
import Definitions.Def_OAIQ239Tc008

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

lemma heat_hasFDerivAt (t : ℝ) (z : V) :
    HasFDerivAt (heat t) ((-heat t z/(2*t)) • innerSL ℝ z) z := by
  have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.mul_const (4*t)⁻¹).exp).const_mul
    ((4*Real.pi*t)⁻¹^2))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp only [heat, smul_apply, neg_apply,
    smul_eq_mul, innerSL_apply_apply, Pi.neg_apply]
  ring_nf

lemma heat_fderiv (t : ℝ) (z w : V) :
    fderiv ℝ (heat t) z w = -heat t z/(2*t) * ⟪z,w⟫ := by
  rw [(heat_hasFDerivAt t z).fderiv]
  rfl

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

lemma heat_directional_hasFDerivAt (t : ℝ) (z v : V) :
    HasFDerivAt (fun y => fderiv ℝ (heat t) y v)
      ((heat t z * ⟪z,v⟫/(4*t^2)) • innerSL ℝ z -
        (heat t z/(2*t)) • innerSL ℝ v) z := by
  have hlin : HasFDerivAt (fun y : V => ⟪y,v⟫) (innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt (x := z) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    exact real_inner_comm v y
  have h := ((heat_hasFDerivAt t z).neg.mul_const (2*t)⁻¹).mul hlin
  have he : (fun y => fderiv ℝ (heat t) y v) =
      (fun y => -heat t y*(2*t)⁻¹ * ⟪y,v⟫) := by
    funext y
    rw [heat_fderiv]
    ring
  rw [he]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  simp only [sub_apply, smul_apply, innerSL_apply_apply, add_apply, neg_apply,
    smul_eq_mul, Pi.neg_apply]
  ring

lemma heat_hessian (t : ℝ) (z u v : V) :
    fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u =
      heat t z * (⟪z,u⟫*⟪z,v⟫/(4*t^2) - ⟪u,v⟫/(2*t)) := by
  rw [(heat_directional_hasFDerivAt t z v).fderiv]
  simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (y := v)]
  ring

lemma heat_equation {t : ℝ} (ht : 0 < t) (z : V) :
    deriv (fun s => heat s z) t = laplacian (heat t) z := by
  rw [(heat_hasDerivAt_time ht z).deriv]
  unfold laplacian
  simp only [heat_hessian, OrthonormalBasis.inner_eq_one, ← pow_two]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
    (EuclideanSpace.basisFun (Fin 4) ℝ).sum_sq_inner_left z]
  norm_num
  ring

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_End
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open scoped ContDiff RealInnerProductSpace
open FlatHeat (V heat)
open Filter Set
open scoped Topology
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma modelSection_fderiv (t : ℝ) (u : W) (z v : V) :
    fderiv ℝ (modelSection t u) z v = fderiv ℝ (heat t) z v • u := by
  have h := ((FlatHeat.heat_hasFDerivAt t z).smul_const u).fderiv
  simpa only [modelSection, ContinuousLinearMap.smulRight_apply,
    (FlatHeat.heat_hasFDerivAt t z).fderiv] using!
    congrArg (fun f : V →L[ℝ] W => f v) h

lemma modelSection_hessian (t : ℝ) (u : W) (z v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (modelSection t u) y v) z w =
      (fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z w) • u := by
  simp_rw [modelSection_fderiv]
  have h := ((FlatHeat.heat_directional_hasFDerivAt t z v).smul_const u).fderiv
  simpa only [ContinuousLinearMap.smulRight_apply,
    (FlatHeat.heat_directional_hasFDerivAt t z v).fderiv] using
    congrArg (fun f : V →L[ℝ] W => f w) h

lemma modelSection_time {t : ℝ} (ht : 0 < t) (u : W) (z : V) :
    deriv (fun s => modelSection s u z) t = FlatHeat.laplacian (heat t) z • u := by
  have h := ((FlatHeat.heat_hasDerivAt_time ht z).smul_const u).deriv
  rw [← FlatHeat.heat_equation ht z, (FlatHeat.heat_hasDerivAt_time ht z).deriv]
  exact h

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [Fintype ι] in
lemma scalar_second (χ : V → ℝ) (u : V → W)
    (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • u z) y w) x v =
      (fderiv ℝ (fun y => fderiv ℝ χ y w) x v) • u x +
      (fderiv ℝ χ x w) • fderiv ℝ u x v + (fderiv ℝ χ x v) • fderiv ℝ u x w +
      χ x • fderiv ℝ (fun y => fderiv ℝ u y w) x v := by
  have hχ' : ∀ y, DifferentiableAt ℝ χ y := hχ.differentiable (by norm_num)
  have hu' : ∀ y, DifferentiableAt ℝ u y := hu.differentiable (by norm_num)
  have hdχ : DifferentiableAt ℝ (fun y => fderiv ℝ χ y w) x :=
    (((hχ.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
    (((hu.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  simp_rw [fderiv_fun_smul (hχ' _) (hu' _)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  have h₁ : DifferentiableAt ℝ (fun y => χ y • fderiv ℝ u y w) x := (hχ' x).smul hdu
  have h₂ : DifferentiableAt ℝ (fun y => fderiv ℝ χ y w • u y) x := hdχ.smul (hu' x)
  rw [fderiv_fun_add h₁ h₂]
  rw [fderiv_fun_smul (hχ' x) hdu,fderiv_fun_smul hdχ (hu' x)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  abel

lemma secondOrder_scalar_product (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (u : V → W) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : V) :
    secondOrder e a b c (fun z => χ z • u z) x =
      χ x • secondOrder e a b c u x -
        (∑ i, ∑ j, a i j x •
          ((fderiv ℝ (fun y => fderiv ℝ χ y (e j)) x (e i)) • u x +
          (fderiv ℝ χ x (e j)) • fderiv ℝ u x (e i) +
          (fderiv ℝ χ x (e i)) • fderiv ℝ u x (e j))) +
        ∑ i, (fderiv ℝ χ x (e i)) • b i x (u x) := by
  simp only [secondOrder, scalar_second χ u hχ hu,
    fderiv_fun_smul (hχ.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x),
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,map_smul,map_add,
    smul_add,Finset.sum_add_distrib,smul_neg,Finset.smul_sum]
  simp only [smul_comm (χ x)]
  abel

end TamingCompatibility.GeometricHilbert.OperatorCalculus

namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma secondOrder_cutoff (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (u : V → W) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : V) :
    secondOrder e a b c (fun z => χ z • u z) x =
      secondOrder e (fun i j z => χ z * a i j z)
        (cutoffFirst e a b χ) (cutoffZero e a b c χ) u x := by
  rw [secondOrder_scalar_product e a b c χ u hχ hu]
  simp only [secondOrder,cutoffFirst,cutoffZero,sub_apply,add_apply,smul_apply,sum_apply,
    ContinuousLinearMap.id_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    smul_add,smul_neg,Finset.smul_sum,Finset.sum_smul,mul_smul,add_smul]
  rw [Finset.sum_comm (f := fun i j => a j i x • (fderiv ℝ χ x (e j) • fderiv ℝ u x (e i)))]
  simp only [smul_comm (χ x)]
  abel

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma cutoff_gaussian_residual_oai (a : Fin 4 → Fin 4 → V → ℝ)
    (b : Fin 4 → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
    deriv (fun s => χ z • modelSection s u z) t +
      secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) a b c
        (fun y => χ y • modelSection t u y) z =
      residual (fun y i j => cutoffPrincipal a χ i j y)
        (fun y j => cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) a b χ j y)
        (cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) a b c χ) t z u := by
  let e := EuclideanSpace.basisFun (Fin 4) ℝ
  have hm : ContDiff ℝ ∞ (modelSection t u) := (heat_contDiff t).smul contDiff_const
  have htime : deriv (fun s => χ z • modelSection s u z) t =
      χ z • deriv (fun s => modelSection s u z) t := by
    have hd := ((heat_hasDerivAt_time ht z).smul_const u)
    exact (hd.const_smul (χ z)).deriv.trans (congrArg (fun v : W => χ z • v) hd.deriv.symm)
  rw [htime,secondOrder_cutoff e a b c χ (modelSection t u)
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (hm.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))]
  rw [modelSection_time ht]
  simp only [secondOrder]
  simp_rw [modelSection_hessian,modelSection_fderiv]
  simp only [modelSection,map_smul]
  have he (i j : Fin 4) : euclideanPrincipal i j - cutoffPrincipal a χ i j z =
      χ z * (euclideanPrincipal i j-a i j z) := by unfold cutoffPrincipal; ring
  simp only [residual,he]
  simp [euclideanPrincipal,FlatHeat.laplacian,e,
    sub_smul,mul_smul,Finset.sum_smul,Finset.smul_sum,
    smul_sub,apply_ite,Finset.sum_sub_distrib,smul_comm (χ z)]
  abel

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoff_gaussian_residual_oai.{u_1}
