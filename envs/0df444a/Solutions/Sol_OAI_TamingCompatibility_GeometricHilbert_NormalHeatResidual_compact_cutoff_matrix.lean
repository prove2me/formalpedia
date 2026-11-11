-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:18:52.371684+00:00
-- url     : https://prove2.me/submissions/ea28079a-e58c-42b2-b976-c4053da64479

import Mathlib
import Definitions.Def_OAIQ239Tc008
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_cutoff_gaussian_residual

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

lemma heat_nonneg (t : ℝ) (z : V) : 0 ≤ heat t z := by
  unfold heat
  positivity

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

lemma gaussian_weight_absorption {t : ℝ} (ht : 0 < t) (z : V) (n : ℕ) :
    ‖z‖^(2*n) * heat t z ≤ 4 * (8*t)^n * (n.factorial : ℝ) * heat (2*t) z := by
  let a : ℝ := ‖z‖^2/(8*t)
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have h := Real.pow_div_factorial_le_exp a ha n
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have h1 : a^n * Real.exp (-a) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ ((n.factorial : ℝ) * Real.exp a) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right (by nlinarith [(div_le_iff₀ hf).mp h]) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; simp
  have hz : ‖z‖^(2*n) = (8*t)^n*a^n := by
    rw [← mul_pow, pow_mul]
    congr 1
    dsimp [a]
    field_simp
  have hH : heat t z = 4 * heat (2*t) z * Real.exp (-a) := by
    have hp : (4*Real.pi*t)⁻¹^2 = 4*(4*Real.pi*(2*t))⁻¹^2 := by field_simp <;> ring
    have he : -‖z‖^2/(4*t) = -a + -a := by dsimp [a] <;> ring
    have he2 : -‖z‖^2/(4*(2*t)) = -a := by dsimp [a] <;> ring
    unfold heat
    rw [hp, he, he2, Real.exp_add]
    ring
  have hp := heat_nonneg (2*t) z
  rw [hz, hH]
  calc
    _ = (4*(8*t)^n*heat (2*t) z) * (a^n*Real.exp (-a)) := by ring
    _ ≤ (4*(8*t)^n*heat (2*t) z) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma heat_gradient_bound {t : ℝ} (ht : 0 < t) (z v : V) :
    |fderiv ℝ (heat t) z v| ≤ heat t z * (‖z‖*‖v‖/(2*t)) := by
  rw [heat_fderiv, abs_mul, abs_div, abs_neg, abs_of_nonneg (heat_nonneg t z),
    abs_of_pos (show 0 < 2*t by positivity)]
  calc
    _ ≤ (heat t z/(2*t)) * (‖z‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z v)
        (div_nonneg (heat_nonneg t z) (by positivity))
    _ = _ := by ring

lemma heat_hessian_bound {t : ℝ} (ht : 0 < t) (z u v : V) :
    |fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u| ≤
      heat t z * (‖z‖^2/(4*t^2) + 1/(2*t)) * ‖u‖*‖v‖ := by
  rw [heat_hessian, abs_mul, abs_of_nonneg (heat_nonneg t z)]
  have h1 : |⟪z,u⟫*⟪z,v⟫/(4*t^2)| ≤ ‖z‖^2*‖u‖*‖v‖/(4*t^2) := by
    rw [abs_div, abs_mul, abs_of_pos (show 0 < 4*t^2 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (‖z‖*‖u‖)*(‖z‖*‖v‖) :=
        mul_le_mul (abs_real_inner_le_norm z u) (abs_real_inner_le_norm z v)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |⟪u,v⟫/(2*t)| ≤ ‖u‖*‖v‖/(2*t) := by
    rw [abs_div, abs_of_pos (show 0 < 2*t by positivity)]
    exact div_le_div_of_nonneg_right (abs_real_inner_le_norm u v) (by positivity)
  calc
    _ ≤ heat t z * (|⟪z,u⟫*⟪z,v⟫/(4*t^2)| + |⟪u,v⟫/(2*t)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (heat_nonneg t z)
    _ ≤ heat t z * (‖z‖^2*‖u‖*‖v‖/(4*t^2) + ‖u‖*‖v‖/(2*t)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (heat_nonneg t z)
    _ = _ := by ring

lemma normal_jet_gradient_bound {t : ℝ} (ht : 0 < t) (z v : V) :
    ‖z‖ * |fderiv ℝ (heat t) z v| ≤ 16 * heat (2*t) z * ‖v‖ := by
  have h := gaussian_weight_absorption ht z 1
  norm_num only [Nat.factorial_one, Nat.mul_one, pow_one, mul_one] at h
  calc
    _ ≤ ‖z‖ * (heat t z * (‖z‖*‖v‖/(2*t))) :=
      mul_le_mul_of_nonneg_left (heat_gradient_bound ht z v) (norm_nonneg _)
    _ = (‖z‖^2 * heat t z) * (‖v‖/(2*t)) := by ring
    _ ≤ (4*(8*t)*heat (2*t) z) * (‖v‖/(2*t)) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by field_simp <;> ring

lemma normal_jet_hessian_bound {t : ℝ} (ht : 0 < t) (z u v : V) :
    ‖z‖^2 * |fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u| ≤
      144 * heat (2*t) z * ‖u‖*‖v‖ := by
  have h1 := gaussian_weight_absorption ht z 1
  have h2 := gaussian_weight_absorption ht z 2
  norm_num only [Nat.factorial_one, Nat.mul_one, pow_one, mul_one] at h1
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at h2
  calc
    _ ≤ ‖z‖^2 * (heat t z * (‖z‖^2/(4*t^2) + 1/(2*t)) * ‖u‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (heat_hessian_bound ht z u v) (sq_nonneg _)
    _ = ((‖z‖^4*heat t z)/(4*t^2) + (‖z‖^2*heat t z)/(2*t)) * ‖u‖*‖v‖ := by ring
    _ ≤ ((4*(8*t)^2*2*heat (2*t) z)/(4*t^2) +
        (4*(8*t)*heat (2*t) z)/(2*t)) * ‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact add_le_add (div_le_div_of_nonneg_right h2 (by positivity))
        (div_le_div_of_nonneg_right h1 (by positivity))
    _ = _ := by field_simp <;> ring

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

lemma residual_bound (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) {Ca Cb Cc t : ℝ} (ht : 0 < t)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (z : V)
    (ha : ∀ i j, |a z i j - euclideanPrincipal i j| ≤ Ca*‖z‖^2)
    (hb : ∀ i, ‖b z i‖ ≤ Cb*‖z‖) (hc : ‖c z‖ ≤ Cc) :
    ‖residual a b c t z‖ ≤ (2304*Ca + 64*Cb + 4*Cc)*heat (2*t) z := by
  have hH := FlatHeat.heat_nonneg (2*t) z
  have ha' (i j : Fin 4) : ‖((euclideanPrincipal i j - a z i j) *
      fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
        (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W‖ ≤
      144*Ca*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_sub_comm]
    calc
      _ ≤ (Ca*‖z‖^2) * |fderiv ℝ (fun y => fderiv ℝ (heat t) y
          (EuclideanSpace.basisFun (Fin 4) ℝ j)) z (EuclideanSpace.basisFun (Fin 4) ℝ i)| * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ha i j) (abs_nonneg _))
          ContinuousLinearMap.norm_id_le (norm_nonneg _) (by positivity)
      _ = Ca * (‖z‖^2 * |fderiv ℝ (fun y => fderiv ℝ (heat t) y
          (EuclideanSpace.basisFun (Fin 4) ℝ j)) z (EuclideanSpace.basisFun (Fin 4) ℝ i)|) := by ring
      _ ≤ Ca*(144*heat (2*t) z) := mul_le_mul_of_nonneg_left
        (by simpa using (FlatHeat.normal_jet_hessian_bound ht z
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ j))) hCa
      _ = _ := by ring
  have hb' (i : Fin 4) : ‖(fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i‖ ≤
      16*Cb*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)| * (Cb*‖z‖) :=
        mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
      _ = Cb*(‖z‖ * |fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)|) := by ring
      _ ≤ Cb*(16*heat (2*t) z) := mul_le_mul_of_nonneg_left
        (by simpa using (FlatHeat.normal_jet_gradient_bound ht z
          (EuclideanSpace.basisFun (Fin 4) ℝ i))) hCb
      _ = _ := by ring
  have hc' : ‖heat t z • c z‖ ≤ 4*Cc*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (FlatHeat.heat_nonneg t z)]
    have h := FlatHeat.gaussian_weight_absorption ht z 0
    norm_num only [Nat.mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, mul_one] at h
    calc
      _ ≤ (4*heat (2*t) z)*Cc := mul_le_mul h hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold residual
  calc
    _ ≤ ‖∑ i, ∑ j, ((euclideanPrincipal i j - a z i j) *
        fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W‖ +
        ‖∑ i, (fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i‖ +
        ‖heat t z • c z‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4, 144*Ca*heat (2*t) z) +
        (∑ i : Fin 4, 16*Cb*heat (2*t) z) + 4*Cc*heat (2*t) z := by
      apply add_le_add _ hc'
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ha' i j))
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb' i)
    _ = _ := by simp <;> ring

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
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W A B : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma linear_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x hx)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,hu⟩).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [←dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr)
    (show z ∈ closedBall 0 r by simpa using hz)

lemma quadratic_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x)
    (hzero : ∀ p ∈ K, dpos F (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 := by
  obtain ⟨C,hC,hb⟩ := linear_bound_on_tube (dpos F) K hK hr
    (fun x hx => dpos_contDiffAt F x (hF x hx))
  have hlin (p : P) (hp : p ∈ K) (z : V) (hz : ‖z‖ ≤ r) :
      ‖dpos F (p,z)‖ ≤ C*‖z‖ := by simpa [hzero p hp] using hb p hp z hz
  refine ⟨C,hC,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : ‖u‖ ≤ r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,by simpa using hu⟩).differentiableAt (by simp)
  have hder (u : V) (hu : u ∈ closedBall (0 : V) ‖z‖) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ C*‖z‖ := by
    have hu' : ‖u‖ ≤ ‖z‖ := by simpa using hu
    rw [←dpos_eq_at F p u (hd u (hu'.trans hz))]
    exact (hlin p hp u (hu'.trans hz)).trans (mul_le_mul_of_nonneg_left hu' hC)
  have hh := (convex_closedBall (0 : V) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u ((by simpa using hu : ‖u‖ ≤ ‖z‖).trans hz)).comp u
      ((differentiableAt_const p).prodMk differentiableAt_id)) hder
    (show (0 : V) ∈ closedBall 0 ‖z‖ by simp)
    (show z ∈ closedBall 0 ‖z‖ by simp)
  simpa [pow_two,mul_assoc] using hh

omit [NormedSpace ℝ W] in
lemma normal_bounds_on_tube (F : P × V → A) (G : P × V → B) (H : P × V → W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x)
    (hG : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ G x)
    (hH : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContinuousAt H x)
    (hF0 : ∀ p ∈ K, dpos F (p,0) = 0) (hG0 : ∀ p ∈ K, G (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 ∧ ‖G (p,z)‖ ≤ C*‖z‖ ∧ ‖H (p,z)‖ ≤ C := by
  obtain ⟨Ca,hCa,hba⟩ := quadratic_bound_on_tube F K hK hr hF hF0
  obtain ⟨Cb,hCb,hbb⟩ := linear_bound_on_tube G K hK hr hG
  obtain ⟨Cc,hbc⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn
    (fun x hx => (hH x hx).continuousWithinAt)
  refine ⟨Ca+Cb+max Cc 0,by positivity,fun p hp z hz => ⟨?_,?_,?_⟩⟩
  · exact (hba p hp z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_max_right Cc 0] : Ca ≤ Ca+Cb+max Cc 0) (sq_nonneg _))
  · have hh : ‖G (p,z)‖ ≤ Cb*‖z‖ := by simpa [hG0 p hp] using hbb p hp z hz
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_right Cc 0] : Cb ≤ Ca+Cb+max Cc 0) (norm_nonneg _))
  · exact (hbc (p,z) ⟨hp,by simpa using hz⟩).trans (by linarith [le_max_left Cc 0])

end TamingCompatibility.GeometricHilbert.UniformJets

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma principal_smooth (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V} (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) :
    ContDiffAt ℝ ∞ (principal a χ) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact contDiffAt_const.add ((hχ.contDiffAt.comp x contDiffAt_snd).mul ((ha i j).sub contDiffAt_const))

lemma first_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) :
    ContDiffAt ℝ ∞ (first a b χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply contDiffAt_pi.mpr
  intro j
  exact ((hχ.contDiffAt.comp x contDiffAt_snd).smul (hb j)).sub
    ((ContDiffAt.sum (fun i _ => ((ha i j).add (ha j i)).mul
      ((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const))).smul contDiffAt_const)

lemma zero_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) : ContDiffAt ℝ ∞ (zero a b c χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdd (j : Fin 4) : ContDiff ℝ ∞ (fderiv ℝ (fun y => fderiv ℝ χ y
      (EuclideanSpace.basisFun (Fin 4) ℝ j))) :=
    (hd.clm_apply contDiff_const).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (((hχ.contDiffAt.comp x contDiffAt_snd).smul hc).sub
    ((ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => (ha i j).mul
      (((hdd j).contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const)))).smul contDiffAt_const)).add
    (ContDiffAt.sum (fun i _ => (((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const).smul (hb i))))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma principal_center (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : χ =ᶠ[𝓝 (0 : V)] 1) (q : P) : principal a χ (q,0) = fun i j => a i j (q,0) := by
  funext i j
  simp [principal,cutoffPrincipal,hχ.eq_of_nhds]

lemma principal_dpos_zero (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) (q : P)
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) (q,0))
    (hder : ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0) :
    dpos (principal a χ) (q,0) = 0 := by
  have he : (fun z => principal a χ (q,z)) =ᶠ[𝓝 (0 : V)] (fun z i j => a i j (q,z)) := by
    filter_upwards [hχ0] with z hz
    funext i j
    simp [principal,cutoffPrincipal,hz]
  rw [dpos_eq_at _ _ _ ((principal_smooth a χ hχ ha).differentiableAt (by simp)),he.fderiv_eq]
  have hd (i j : Fin 4) : DifferentiableAt ℝ (fun z => a i j (q,z)) 0 :=
    ((ha i j).comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_pi (fun i => differentiableAt_pi.mpr (hd i))]
  ext v i j
  simp only [ContinuousLinearMap.pi_apply,zero_apply,Pi.zero_apply]
  rw [fderiv_pi (hd i)]
  simp only [ContinuousLinearMap.pi_apply,hder,zero_apply]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma first_center (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : χ =ᶠ[𝓝 (0 : V)] 1) (q : P) : first a b χ (q,0) = fun j => b j (q,0) := by
  have hd : fderiv ℝ χ 0 = 0 := by simpa using hχ.fderiv_eq (𝕜 := ℝ)
  funext j
  simp [first,cutoffFirst,hχ.eq_of_nhds,hd]

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

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
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma compact_cutoff_residual (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
    (hb : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
    (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
    (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
    (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t → ∀ u : W,
      ‖deriv (fun s => χ z • modelSection s u z) t +
        secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j y => a i j (q,y))
          (fun j y => b j (q,y)) (fun y => c (q,y)) (fun y => χ y • modelSection t u y) z‖ ≤
        (C*heat (2*t) z)*‖u‖ := by
  have hp (q : P) (hq : q ∈ K) : (q,0) ∈ K ×ˢ closedBall (0 : V) r := ⟨hq,by simpa using hr⟩
  have hF0 (q : P) (hq : q ∈ K) : dpos (principal a χ) (q,0) = 0 :=
    principal_dpos_zero a χ hχ hχ0 q (ha _ (hp q hq)) (hda0 q hq)
  have hG0 (q : P) (hq : q ∈ K) : first a b χ (q,0) = 0 := by
    rw [first_center a b χ hχ0 q]
    funext j
    exact hb0 q hq j
  obtain ⟨C,hC,hbounds⟩ := normal_bounds_on_tube (principal a χ) (first a b χ) (zero a b c χ)
    K hK hr (fun x hx => principal_smooth a χ hχ (ha x hx))
    (fun x hx => first_smooth a b χ hχ (ha x hx) (hb x hx))
    (fun x hx => (zero_smooth a b c χ hχ (ha x hx) (hb x hx) (hc x hx)).continuousAt) hF0 hG0
  refine ⟨2304*C+64*C+4*C,by positivity,fun q hq z hz t ht u => ?_⟩
  rw [cutoff_gaussian_residual _ _ _ χ hχ ht z u]
  have hba (i j : Fin 4) : |principal a χ (q,z) i j - euclideanPrincipal i j| ≤ C*‖z‖^2 := by
    have hp0 : principal a χ (q,0) i j = euclideanPrincipal i j := by
      rw [principal_center a χ hχ0 q]
      exact ha0 q hq i j
    have hn := ((norm_le_pi_norm ((principal a χ (q,z)-principal a χ (q,0)) i) j).trans
      (norm_le_pi_norm (principal a χ (q,z)-principal a χ (q,0)) i)).trans (hbounds q hq z hz).1
    simpa only [Pi.sub_apply,Real.norm_eq_abs,hp0] using hn
  have hbb (j : Fin 4) : ‖first a b χ (q,z) j‖ ≤ C*‖z‖ :=
    (norm_le_pi_norm (first a b χ (q,z)) j).trans (hbounds q hq z hz).2.1
  have hh := residual_bound (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
    (fun y => zero a b c χ (q,y)) ht hC hC z hba hbb (hbounds q hq z hz).2.2
  exact (ContinuousLinearMap.le_opNorm _ u).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg u))

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma compact_cutoff_matrix_oai (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
    (hb : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
    (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
    (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
    (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
      ‖residual (fun y => CutoffFamilies.principal a χ (q,y))
        (fun y => CutoffFamilies.first a b χ (q,y))
        (fun y => CutoffFamilies.zero a b c χ (q,y)) t z‖ ≤ C*heat (2*t) z := by
  obtain ⟨C,hC,hb⟩ := CutoffFamilies.compact_cutoff_residual a b c K hK hr ha hb hc ha0 hda0 hb0 χ hχ hχ0
  refine ⟨C,hC,fun q hq z hz t ht => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (heat_nonneg _ _))
  intro u
  have hh := hb q hq z hz t ht u
  rw [cutoff_gaussian_residual _ _ _ χ hχ ht] at hh
  exact hh

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix_oai.{u_1, u_2}
