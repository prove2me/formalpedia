-- Prove2me | solution 1 for OAI.ElasticityConic.chart_comparison_trivial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:13:09.200106+00:00
-- url     : https://prove2.me/submissions/cba1e2cf-1265-4d27-906d-a8ba82a6886d

import Mathlib
import Definitions.Def_OAIQ6El003
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open scoped BigOperators

lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixD_eval (θ : Fin 3 → ℂ) (G : Matrix n n Smooth) (x : X) (i j : n) :
    matrixEval x (matrixD θ G) i j=∑ r,θ r*fderiv ℝ (G i j : X → ℂ) x (ElasticityParameter.basis r) := by
  simp only [matrixEval_apply,matrixD,thetaDerivation_apply,direction,smooth_sum_eval,
    Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul]
  rfl

end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Two-chart proof of precisely the holomorphic-conic rigidity step. The
analytic construction of the comparison from DN equality is NOT assumed in
the main target and is still missing. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix
namespace ElasticityRigidity

/-- Two-chart Liouville argument for degree-zero entries. -/
lemma sphere_function_constant {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : ContinuousAt g 0) (hglue : ∀ z : ℂ, z ≠ 0 → f z = g z⁻¹) :
    ∀ z, f z = f 0 := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hlim : Tendsto f (cocompact ℂ) (𝓝 (g 0)) := by
    apply (hg.tendsto.comp hi).congr'
    filter_upwards [show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 by
      simpa only [Metric.cobounded_eq_cocompact] using Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (hglue z hz).symm
  intro z
  exact (hf.apply_eq_of_tendsto_cocompact z hlim).trans
    (hf.apply_eq_of_tendsto_cocompact 0 hlim).symm

/-- The negative-degree transition forces every holomorphic section to vanish. -/
lemma negative_section_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : ContinuousAt g 0) (hglue : ∀ z : ℂ, z ≠ 0 → f z = z⁻¹ * g z⁻¹) :
    ∀ z, f z = 0 := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hlim : Tendsto f (cocompact ℂ) (𝓝 0) := by
    have hh := hi.mul (hg.tendsto.comp hi)
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 by
      simpa only [Metric.cobounded_eq_cocompact] using Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (hglue z hz).symm
  exact fun z => hf.apply_eq_of_tendsto_cocompact z hlim

lemma diagonal_degree_zero {G₀ Ginf : X → ℂ → Mat}
    (hG : HolomorphicComparison G₀ Ginf) (x : X) (i j : Fin 3)
    (hij : (i = 2 ↔ j = 2)) : ∀ z, G₀ x z i j = G₀ x 0 i j := by
  apply sphere_function_constant (hG.1 x i j) (hG.2.1 x i j).continuous.continuousAt
  intro z hz
  have he := hG.2.2 x z hz i j
  by_cases hi : i = 2
  · have hj := hij.mp hi
    simpa [hi, hj] using he
  · have hj : j ≠ 2 := fun hj => hi (hij.mpr hj)
    simpa [hi, hj, mul_comm, mul_left_comm, mul_assoc, hz] using he

lemma upperright_zero {G₀ Ginf : X → ℂ → Mat}
    (hG : HolomorphicComparison G₀ Ginf) (x : X) (i : Fin 3) (hi : i ≠ 2) :
    ∀ z, G₀ x z i 2 = 0 := by
  apply negative_section_zero (hG.1 x i 2) (hG.2.1 x i 2).continuous.continuousAt
  intro z hz
  simpa [hi] using hG.2.2 x z hz i 2

lemma D_zero (z : ℂ) (x : X) : D z (fun _ => 0) x = 0 := by
  simp [D]

lemma top_blocks_scalar {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂) :
    ∀ x z i j, i ≠ 2 → j ≠ 2 →
      G₀ x z i j = if i = j then G₀ x 0 2 2 else 0 := by
  have hu (i : Fin 3) (hi : i ≠ 2) (z : ℂ) : (fun x => G₀ x z i 2) = fun _ => 0 := by
    funext x
    exact upperright_zero hG x i hi z
  have hc (x : X) (z : ℂ) (i j : Fin 3) (hh : i = 2 ↔ j = 2) :=
    diagonal_degree_zero hG x i j hh z
  have hr0 (x : X) (z : ℂ) :
      G₀ x 0 2 2 - (G₀ x 0 0 0 + G₀ x 0 0 1 * z) = 0 := by
    have ht := hT x z 0 2
    rw [hu 0 (by decide) z, D_zero] at ht
    simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG x 0 (by decide) z] at ht
    rw [hc x z 2 2 Iff.rfl, hc x z 0 0 Iff.rfl,
      hc x z 0 1 (by decide)] at ht
    exact ht.symm
  have hr1 (x : X) (z : ℂ) :
      z * G₀ x 0 2 2 - (G₀ x 0 1 0 + G₀ x 0 1 1 * z) = 0 := by
    have ht := hT x z 1 2
    rw [hu 1 (by decide) z, D_zero] at ht
    simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG x 1 (by decide) z] at ht
    rw [hc x z 2 2 Iff.rfl, hc x z 1 0 (by decide),
      hc x z 1 1 Iff.rfl] at ht
    exact ht.symm
  intro x z i j hi hj
  have h00 : G₀ x 0 0 0 = G₀ x 0 2 2 := by
    have hh := hr0 x 0
    simp only [mul_zero, add_zero, sub_eq_zero] at hh
    exact hh.symm
  have h01 : G₀ x 0 0 1 = 0 := by linear_combination -(hr0 x 1) - h00
  have h10 : G₀ x 0 1 0 = 0 := by simpa using hr1 x 0
  have h11 : G₀ x 0 1 1 = G₀ x 0 2 2 := by linear_combination -(hr1 x 1) - h10
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · simpa using (hc x z 0 0 Iff.rfl).trans h00
  · simpa using (hc x z 0 1 (by decide)).trans h01
  · simpa using (hc x z 1 0 (by decide)).trans h10
  · simpa using (hc x z 1 1 Iff.rfl).trans h11

lemma comparison_scalar_and_dir_zero {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂) :
    (∀ x z, G₀ x z = G₀ x 0 2 2 • (1 : Mat)) ∧
      ∀ x z, D z (fun y => G₀ y 0 2 2) x = 0 := by
  let f : X → ℂ := fun y => G₀ y 0 2 2
  have heq00 (z : ℂ) : (fun y => G₀ y z 0 0) = f := by
    funext y
    exact top_blocks_scalar hG hT y z 0 0 (by decide) (by decide)
  have heq11 (z : ℂ) : (fun y => G₀ y z 1 1) = f := by
    funext y
    exact top_blocks_scalar hG hT y z 1 1 (by decide) (by decide)
  have heq01 (z : ℂ) : (fun y => G₀ y z 0 1) = fun _ => 0 := by
    funext y
    exact top_blocks_scalar hG hT y z 0 1 (by decide) (by decide)
  have h21 (x : X) (z : ℂ) : G₀ x z 2 1 = 0 := by
    have ht := hT x z 0 1
    rw [heq01 z, D_zero] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG] using ht.symm
  have hd (x : X) (z : ℂ) : D z f x = 0 := by
    have ht := hT x z 1 1
    rw [heq11 z] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG, h21 x z] using ht
  have h20 (x : X) (z : ℂ) : G₀ x z 2 0 = 0 := by
    have ht := hT x z 0 0
    rw [heq00 z, hd] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG] using ht.symm
  refine ⟨?_, hd⟩
  intro x z
  ext i j
  by_cases hi : i = 2
  · subst i
    fin_cases j
    · simpa using h20 x z
    · simpa using h21 x z
    · simpa using diagonal_degree_zero hG x 2 2 Iff.rfl z
  · by_cases hj : j = 2
    · subst j
      simpa [Matrix.one_apply, hi] using upperright_zero hG x i hi z
    · simpa [Matrix.one_apply, smul_eq_mul, mul_ite] using
        top_blocks_scalar hG hT x z i j hi hj

lemma fderiv_zero_of_chart_dirs (f : X → ℂ) (x : X)
    (hf : ∀ z, D z f x = 0) : fderiv ℝ f x = 0 := by
  have h0 := hf 0
  have h1 := hf 1
  have hm := hf (-1)
  simp [D, θ, Fin.sum_univ_succ] at h0 h1 hm
  have h2 : fderiv ℝ f x (e 2) = 0 := by linear_combination (h1 - hm) / 4
  have hi : Complex.I * fderiv ℝ f x (e 1) = 0 := by linear_combination (h1 + hm) / 4
  have h₁ := (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  have h₀ : fderiv ℝ f x (e 0) = 0 := by simpa [h₁] using h0
  have hL : (fderiv ℝ f x).toLinearMap = (0 : X →ₗ[ℝ] ℂ) := by
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    fin_cases i <;> simpa [e] using (by assumption)
  exact DFunLike.coe_injective (congrArg (fun L : X →ₗ[ℝ] ℂ => (L : X → ℂ)) hL)

/-- Exact comparison rigidity in the two charts of the projective null conic.
The exterior identity assumption is used only at a single exterior point. -/
theorem comparison_identity {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂)
    (hs : ∀ z i j, Differentiable ℝ (fun x => G₀ x z i j))
    {x₀ : X} (hext : G₀ x₀ 0 = 1) :
    (∀ x z, G₀ x z = 1) ∧ (∀ x w, Ginf x w = 1) := by
  obtain ⟨hscalar, hd⟩ := comparison_scalar_and_dir_zero hG hT
  have hf' (x : X) : fderiv ℝ (fun y => G₀ y 0 2 2) x = 0 :=
    fderiv_zero_of_chart_dirs _ x (hd x)
  have hf (x : X) : G₀ x 0 2 2 = 1 := by
    have he := is_const_of_fderiv_eq_zero (hs 0 2 2) hf' x x₀
    simpa [hext] using he
  have hzero (x : X) (z : ℂ) : G₀ x z = 1 := by simpa [hf x] using hscalar x z
  refine ⟨hzero, ?_⟩
  intro x w
  have hout (w : ℂ) (hw : w ≠ 0) (i j : Fin 3) : Ginf x w i j = (1 : Mat) i j := by
    have he := hG.2.2 x w⁻¹ (inv_ne_zero hw) i j
    rw [hzero] at he
    simp only [inv_inv] at he
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 2
      · simpa [hi] using he.symm
      · calc
          Ginf x w i i = w * Ginf x w i i * w⁻¹ := by field_simp
          _ = (1 : Mat) i i := by simpa [hi] using he.symm
    · have hl : (if i = 2 then (1 : ℂ) else w) ≠ 0 := by
        by_cases hi : i = 2 <;> simp [hi, hw]
      have hr : (if j = 2 then (1 : ℂ) else w⁻¹) ≠ 0 := by
        by_cases hj : j = 2 <;> simp [hj, hw]
      have hz : (if i = 2 then (1 : ℂ) else w) * Ginf x w i j *
          (if j = 2 then (1 : ℂ) else w⁻¹) = 0 := by
        simpa [Matrix.one_apply, hij] using he.symm
      have hz' := (mul_eq_zero.mp hz).resolve_right hr
      have hz'' := (mul_eq_zero.mp hz').resolve_left hl
      simpa [Matrix.one_apply, hij] using hz''
  ext i j
  have hfun : (fun w : ℂ => Ginf x w i j) = fun _ => (1 : Mat) i j := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (hG.2.1 x i j).continuous continuous_const
    intro z hz
    exact hout z hz i j
  exact congrFun hfun w

end ElasticityRigidity

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

lemma chart_transition_scalar (z a : ℂ) (i j : Fin 3) :
    (chartDiagonal z i)⁻¹*chartDiagonal z j*a=
      (if i=2 then (1 : ℂ) else z⁻¹)*a*(if j=2 then (1 : ℂ) else z) := by
  simp only [chartDiagonal]
  split_ifs <;> ring

lemma chartTheta_false (z : ℂ) : chartTheta false z=ElasticityRigidity.θ z := by
  ext i
  fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,ElasticityRigidity.θ]

/-- The abstract conic rigidity calculation, separated from the lengthy
physical coefficient formulas. All analytic matching properties are supplied
below by proved supported uniqueness and regularity, not by inverse hypotheses. -/
theorem chart_comparison_trivial_oai (T : Bool → ℂ → Fin 2 → Smooth)
    (Q : Bool → ℂ → Fin 2 → Fin 3 → Smooth)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hG : ∀ b i j,JointHolomorphic (fun y : X × ℂ => (G b y.2 i j : X → ℂ) y.1))
    (hglue : ∀ z : ℂ,z≠0 → G false z=diagonalGauge (chartDiagonal z) (G true z⁻¹))
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      chartMatrix b z (T b z 1) (Q b z 1)*G b z-G b z*chartMatrix b z (T b z 0) (Q b z 0))
    (x₀ : X) (hbase : matrixEval x₀ (G false 0)=1) : ∀ b z,G b z=1 := by
  let M := fun b z q => chartMatrix b z (T b z q) (Q b z q)
  let F := fun b x z => matrixEval x (G b z)
  have hH : ElasticityRigidity.HolomorphicComparison (F false) (F true) := by
    refine ⟨fun x i j => (hG false i j).holo x,fun x i j => (hG true i j).holo x,?_⟩
    intro x z hz i j
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) Smooth => (A i j : X → ℂ) x)
      (hglue z hz)
    change (G false z i j : X → ℂ) x=((chartDiagonal z i)⁻¹*chartDiagonal z j)*(G true z⁻¹ i j : X → ℂ) x at hh
    change (G false z i j : X → ℂ) x=_
    exact hh.trans (chart_transition_scalar z ((G true z⁻¹ i j : X → ℂ) x) i j)
  let τ := fun q x z => (T false z q : X → ℂ) x
  let β := fun q x z (i : Fin 2) => (M false z q 2 i.castSucc : X → ℂ) x
  have hM (q x z) : ElasticityRigidity.M (β q) (τ q) x z=matrixEval x (M false z q) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ElasticityRigidity.M,β,τ,M,chartMatrix,chartZ₀,chartZ₁]
  have hT : ElasticityRigidity.Transport (F false) (β 0) (β 1) (τ 0) (τ 1) := by
    intro x z i j
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) Smooth => matrixEval x A i j) (he false z)
    rw [matrixD_eval] at hh
    simp only [map_sub,map_mul] at hh
    rw [hM,hM]
    simpa only [chartTheta_false,ElasticityRigidity.D,ElasticityRigidity.e,
      ElasticityParameter.basis,F,matrixEval_apply] using hh
  have hsp (z i j) : Differentiable ℝ (fun x => F false x z i j) :=
    (show ContDiff ℝ (⊤ : ℕ∞) (G false z i j : X → ℂ) from (G false z i j).property).differentiable (by simp)
  have hId := ElasticityRigidity.comparison_identity hH hT hsp hbase
  intro b z
  ext i j x
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A i j)
    (show F b x z=1 by cases b; exact hId.1 x z; exact hId.2 x z)
  change matrixEval x (G b z) i j=matrixEval x 1 i j
  rw [map_one]
  exact hh

end ElasticityConic

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityConic.chart_comparison_trivial_oai := @OAI.ElasticityConic.chart_comparison_trivial_oai
