-- Prove2me | solution 1 for OAI.ElasticityConic.physical_conic_connections_equal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:15:00.603831+00:00
-- url     : https://prove2.me/submissions/a9dc1863-faf1-458b-b34e-f48ec52f5cce

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityAugmented_supported_matrix_holomorphic
import Theorems.Thm_OAI_ElasticityAugmented_supported_matrix_unique
import Theorems.Thm_OAI_ElasticityConic_chart_comparison_trivial

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
lemma restrict_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f : Smooth) :
    restrictSmooth U (direction coord θ f)=direction (localCoord hU) θ (restrictSmooth U f) := by
  simp only [direction,map_sum,map_smul,localCoord_restrict]
end ElasticityAugmented

end
end

end OAI
end

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

lemma smoothInv_apply (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (x : X) :
    (smoothInv f hf : X → ℂ) x=((f : X → ℂ) x)⁻¹ := rfl
lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

namespace ElasticityConic

lemma theta_null (z₀ z₁ : ℂ) : null (theta z₀ z₁) := by
  simp only [null, dot3, theta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (z₀ ^ 2 + z₁ ^ 2) ^ 2 * Complex.I_sq

lemma theta_ne_zero {z₀ z₁ : ℂ} (hz : z₀ ≠ 0 ∨ z₁ ≠ 0) : theta z₀ z₁ ≠ 0 := by
  intro h
  have ha := congrFun h 0
  have hb := congrFun h 1
  simp [theta] at ha hb
  have hb' : z₀ ^ 2 + z₁ ^ 2 = 0 := hb
  have hc : z₀ ^ 2 = 0 := by linear_combination (ha + hb') / 2
  have hd : z₁ ^ 2 = 0 := by linear_combination (hb' - ha) / 2
  exact hz.elim (fun hz₀ => hz₀ ((pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)).mp hc)) (fun hz₁ => hz₁ ((pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)).mp hd))

end ElasticityConic

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
end
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
lemma eqOn_coord {U : Set X} (hU : IsOpen U) (f g : Smooth)
    (he : EqOn (f : X → ℂ) g U) (i : Fin 3) :
    EqOn (coord i f : X → ℂ) (coord i g) U := by
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [← localCoord_restrict hU,← localCoord_restrict hU,(restrictSmooth_eq_iff U f g).mpr he]
lemma eqOn_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f g : Smooth)
    (he : EqOn (f : X → ℂ) g U) :
    EqOn (direction (A := Smooth) coord θ f : X → ℂ) (direction (A := Smooth) coord θ g) U := by
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_direction hU,restrict_direction hU,(restrictSmooth_eq_iff U f g).mpr he]
lemma eqOn_logarithmicGrad {U : Set X} (hU : IsOpen U) (r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (he : EqOn (r₀ : X → ℂ) r₁ U) (i : Fin 3) :
    EqOn (logarithmicGrad r₀ hr₀ i : X → ℂ) (logarithmicGrad r₁ hr₁ i) U := by
  intro x hx
  change 2*((r₀ : X → ℂ) x)⁻¹*(coord i r₀ : X → ℂ) x=
    2*((r₁ : X → ℂ) x)⁻¹*(coord i r₁ : X → ℂ) x
  rw [he hx,eqOn_coord hU r₀ r₁ he i hx]
lemma eqOn_transport {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (k₀ k₁ r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (hk₀ : ∀ x,(k₀ : X → ℂ) x≠0) (hk₁ : ∀ x,(k₁ : X → ℂ) x≠0)
    (hl₀ : ∀ x,((k₀+r₀*r₀ : Smooth) : X → ℂ) x≠0)
    (hl₁ : ∀ x,((k₁+r₁*r₁ : Smooth) : X → ℂ) x≠0)
    (hk : EqOn (k₀ : X → ℂ) k₁ U) (hr : EqOn (r₀ : X → ℂ) r₁ U) :
    EqOn (transportT θ k₀ r₀ hk₀ hl₀ : X → ℂ) (transportT θ k₁ r₁ hk₁ hl₁) U ∧
    ∀ i,EqOn (transportQ θ k₀ r₀ hr₀ hk₀ hl₀ i : X → ℂ)
      (transportQ θ k₁ r₁ hr₁ hk₁ hl₁ i) U := by
  have hl : EqOn ((k₀+r₀*r₀ : Smooth) : X → ℂ) (k₁+r₁*r₁ : Smooth) U := by
    intro x hx
    change (k₀ : X → ℂ) x+(r₀ : X → ℂ) x*(r₀ : X → ℂ) x=_
    rw [hk hx,hr hx]
    rfl
  have hγ : EqOn (thetaGamma θ r₀ hr₀ : X → ℂ) (thetaGamma θ r₁ hr₁) U := by
    intro x hx
    simp only [thetaGamma,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx])
  constructor
  · intro x hx
    simp only [transportT,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
    rw [hk hx,hl hx,eqOn_direction hU θ k₀ k₁ hk hx,
      eqOn_direction hU θ (k₀+r₀*r₀) (k₁+r₁*r₁) hl hx]
  · intro i x hx
    simp only [transportQ,Subalgebra.coe_smul,Subalgebra.coe_sub,Subalgebra.coe_mul,
      Pi.smul_apply,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
    rw [hr hx,hk hx,hl hx,hγ hx,eqOn_direction hU θ k₀ k₁ hk hx,
      eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx,
      eqOn_direction hU θ _ _ (eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i) hx]
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
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityFrame

lemma chartTheta_ne_zero (b : Bool) (z : ℂ) : chartTheta b z≠0 := by
  cases b
  · exact theta_ne_zero (Or.inl one_ne_zero)
  · exact theta_ne_zero (Or.inr one_ne_zero)
lemma chartTheta_null (b : Bool) (z : ℂ) : ∑ i,chartTheta b z i*chartTheta b z i=0 :=
  theta_null _ _
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n] in
lemma matrixD_one (θ : Fin 3 → ℂ) : matrixD θ (1 : Matrix n n Smooth)=0 := by
  ext i j
  simp only [matrixD,Matrix.one_apply,Matrix.zero_apply]
  split_ifs <;> simp

end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma supported_matrix_eq_one {K : Set X} (G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K)
    (x : X) (hx : x∉K) : matrixEval x G=1 := by
  ext i j
  have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs i j hh))
  change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0 at hz
  have he : ((1 : Matrix n n Smooth) i j : X → ℂ) x=(1 : Matrix n n ℂ) i j := by
    have hh := congrArg (fun A : Matrix n n ℂ => A i j) (map_one (matrixEval (n := n) x))
    exact hh
  rw [he] at hz
  exact sub_eq_zero.mp hz

end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Holomorphy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

namespace JointHolomorphic
lemma fixed (f : Smooth) : JointHolomorphic (fun q : X × ℂ => (f : X → ℂ) q.1) :=
  ⟨(show ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) from f.property).comp contDiff_fst,fun x => differentiable_const ((f : X → ℂ) x)⟩
lemma param (f : ℂ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hh : Differentiable ℂ f) :
    JointHolomorphic (fun q : X × ℂ => f q.2) := ⟨hf.comp contDiff_snd,fun _ => hh⟩
lemma const (c : ℂ) : JointHolomorphic (fun _ : X × ℂ => c) :=
  ⟨contDiff_const,fun _ => differentiable_const _⟩
lemma add {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q+g q) := ⟨hf.smooth.add hg.smooth,fun x => (hf.holo x).add (hg.holo x)⟩
lemma sub {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q-g q) := ⟨hf.smooth.sub hg.smooth,fun x => (hf.holo x).sub (hg.holo x)⟩
lemma mul {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q*g q) := ⟨hf.smooth.mul hg.smooth,fun x => (hf.holo x).mul (hg.holo x)⟩
lemma pow {f : X × ℂ → ℂ} (hf : JointHolomorphic f) (n : ℕ) :
    JointHolomorphic (fun q => f q^n) := ⟨hf.smooth.pow n,fun x => (hf.holo x).pow n⟩
lemma sum {ι : Type*} [Fintype ι] {f : ι → X × ℂ → ℂ} (hf : ∀ i,JointHolomorphic (f i)) :
    JointHolomorphic (fun q => ∑ i,f i q) :=
  ⟨ContDiff.sum (fun i _ => (hf i).smooth),fun x => Differentiable.fun_sum (fun i _ => (hf i).holo x)⟩
end JointHolomorphic

lemma chartZ₀_regular (b : Bool) : JointHolomorphic (fun q : X × ℂ => chartZ₀ b q.2) := by
  cases b
  · exact JointHolomorphic.const 1
  · exact JointHolomorphic.param id contDiff_id differentiable_id
lemma chartZ₁_regular (b : Bool) : JointHolomorphic (fun q : X × ℂ => chartZ₁ b q.2) := by
  cases b
  · exact JointHolomorphic.param id contDiff_id differentiable_id
  · exact JointHolomorphic.const 1
lemma chartTheta_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => chartTheta b q.2 i) := by
  fin_cases i
  · exact (chartZ₀_regular b).pow 2 |>.sub ((chartZ₁_regular b).pow 2)
  · exact (JointHolomorphic.const Complex.I).mul (((chartZ₀_regular b).pow 2).add ((chartZ₁_regular b).pow 2))
  · exact ((JointHolomorphic.const 2).mul (chartZ₀_regular b)).mul (chartZ₁_regular b)
lemma h₁_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => h₁ (chartZ₀ b q.2) (chartZ₁ b q.2) i) := by
  fin_cases i
  · exact chartZ₀_regular b
  · exact (JointHolomorphic.const Complex.I).mul (chartZ₀_regular b)
  · exact chartZ₁_regular b
lemma h₂_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => h₂ (chartZ₀ b q.2) (chartZ₁ b q.2) i) := by
  fin_cases i
  · simpa [h₂] using (JointHolomorphic.const (-1)).mul (chartZ₁_regular b)
  · exact (JointHolomorphic.const Complex.I).mul (chartZ₁_regular b)
  · exact chartZ₀_regular b
lemma direction_regular (b : Bool) (f : Smooth) :
    JointHolomorphic (fun q : X × ℂ => (direction (A := Smooth) coord (chartTheta b q.2) f : X → ℂ) q.1) := by
  have hh := JointHolomorphic.sum (fun i => (chartTheta_regular b i).mul (JointHolomorphic.fixed (coord i f)))
  simpa only [direction,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul] using hh
lemma thetaGamma_regular (b : Bool) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) :
    JointHolomorphic (fun q : X × ℂ => (thetaGamma (chartTheta b q.2) r hr : X → ℂ) q.1) := by
  have hh := JointHolomorphic.sum (fun i => (chartTheta_regular b i).mul (JointHolomorphic.fixed (logarithmicGrad r hr i)))
  simpa only [thetaGamma,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul] using hh
lemma transportT_regular (b : Bool) (k r : Smooth) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    JointHolomorphic (fun q : X × ℂ => (transportT (chartTheta b q.2) k r hk hl : X → ℂ) q.1) :=
  ((JointHolomorphic.fixed (smoothInv k hk)).mul (direction_regular b k)).sub
    ((JointHolomorphic.fixed (smoothInv (k+r*r) hl)).mul (direction_regular b (k+r*r)))
lemma transportQ_regular (b : Bool) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (i : Fin 3) :
    JointHolomorphic (fun q : X × ℂ => (transportQ (chartTheta b q.2) k r hr hk hl i : X → ℂ) q.1) :=
  (JointHolomorphic.const (1/2)).mul
    ((((JointHolomorphic.fixed (r*r*smoothInv (k+r*r) hl*smoothInv k hk)).mul (direction_regular b k)).sub
      ((JointHolomorphic.const (1/2)).mul (thetaGamma_regular b r hr))).mul
        (JointHolomorphic.fixed (logarithmicGrad r hr i)) |>.sub
      ((JointHolomorphic.fixed (r*r*smoothInv (k+r*r) hl)).mul (direction_regular b (logarithmicGrad r hr i))))

/-- These are the literal chart coefficients, jointly smooth and holomorphic
in the normalized conic direction, with the physical point fixed. -/
lemma chartMatrix_regular (b : Bool) (T : ℂ → Smooth) (Q : ℂ → Fin 3 → Smooth)
    (hT : JointHolomorphic (fun q : X × ℂ => (T q.2 : X → ℂ) q.1))
    (hQ : ∀ i,JointHolomorphic (fun q : X × ℂ => (Q q.2 i : X → ℂ) q.1)) (i j : Fin 3) :
    JointHolomorphic (fun q : X × ℂ => (chartMatrix b q.2 (T q.2) (Q q.2) i j : X → ℂ) q.1) := by
  fin_cases i <;> fin_cases j
  all_goals try first | exact JointHolomorphic.const 0 | exact hT
  · simpa [chartMatrix,smooth_sum_eval] using chartZ₀_regular b
  · simpa [chartMatrix,smooth_sum_eval] using chartZ₁_regular b
  · have hh := JointHolomorphic.sum (fun k => (h₁_regular b k).mul (hQ k))
    simpa [chartMatrix,smooth_sum_eval] using hh
  · have hh := JointHolomorphic.sum (fun k => (h₂_regular b k).mul (hQ k))
    simpa [chartMatrix,smooth_sum_eval] using hh
end ElasticityConic

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
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma diagonalGauge_mul (d : n → ℂ) (hd : ∀ i,d i≠0) (A B : Matrix n n Smooth) :
    diagonalGauge d (A*B)=diagonalGauge d A*diagonalGauge d B := by
  funext i j
  simp only [diagonalGauge,Matrix.mul_apply,Finset.smul_sum,smul_mul_smul_comm]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  field_simp [hd k]
omit [Fintype n] [DecidableEq n] in
lemma diagonalGauge_sub (d : n → ℂ) (A B : Matrix n n Smooth) :
    diagonalGauge d (A-B)=diagonalGauge d A-diagonalGauge d B := by
  funext i j
  exact smul_sub _ _ _
omit [Fintype n] in
lemma diagonalGauge_one (d : n → ℂ) (hd : ∀ i,d i≠0) :
    diagonalGauge d (1 : Matrix n n Smooth)=1 := by
  funext i j
  simp only [diagonalGauge,Matrix.one_apply]
  split_ifs with h
  · subst j; simp [hd i]
  · simp only [smul_zero]
omit [Fintype n] [DecidableEq n] in
lemma matrixD_diagonalGauge (θ : Fin 3 → ℂ) (d : n → ℂ) (G : Matrix n n Smooth) :
    matrixD θ (diagonalGauge d G)=diagonalGauge d (matrixD θ G) := by
  funext i j
  exact (thetaDerivation θ).map_smul _ _
omit [Fintype n] [DecidableEq n] in
lemma matrixD_direction_smul (θ : Fin 3 → ℂ) (c : ℂ) (G : Matrix n n Smooth) :
    matrixD (c • θ) G=c • matrixD θ G := by
  funext i j
  change thetaDerivation (c • θ) (G i j)=c • thetaDerivation θ (G i j)
  simp only [thetaDerivation_apply,direction,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
omit [DecidableEq n] in
lemma diagonalGauge_equation (θ : Fin 3 → ℂ) (c : ℂ) (d : n → ℂ) (hd : ∀ i,d i≠0)
    (M₀ M₁ G : Matrix n n Smooth) (he : matrixD θ G=M₁*G-G*M₀) :
    matrixD (c • θ) (diagonalGauge d G)=
      (c • diagonalGauge d M₁)*diagonalGauge d G-diagonalGauge d G*(c • diagonalGauge d M₀) := by
  rw [matrixD_direction_smul,matrixD_diagonalGauge,he,diagonalGauge_sub,
    diagonalGauge_mul d hd,diagonalGauge_mul d hd,smul_sub,smul_mul_assoc,mul_smul_comm]
omit [Fintype n] in
lemma diagonalGauge_supported {K : Set X} (hK : IsClosed K) (d : n → ℂ) (hd : ∀ i,d i≠0)
    (G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K) :
    ∀ i j,tsupport ((diagonalGauge d G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K := by
  intro i j
  apply closure_minimal _ hK
  intro x hx
  by_contra hnx
  apply hx
  have hz := image_eq_zero_of_notMem_tsupport (fun hh => hnx (hs i j hh))
  change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0 at hz
  have he := sub_eq_zero.mp hz
  have ho := congrArg (fun A : Matrix n n Smooth => (A i j : X → ℂ) x) (diagonalGauge_one d hd)
  change ((d i)⁻¹*d j)*(G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0
  rw [he]
  exact sub_eq_zero.mpr ho
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
lemma direction_theta_smul (θ : Fin 3 → ℂ) (c : ℂ) (f : Smooth) :
    direction (A := Smooth) coord (c • θ) f=c • direction (A := Smooth) coord θ f := by
  simp only [direction,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
lemma thetaGamma_smul (θ : Fin 3 → ℂ) (c : ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) :
    thetaGamma (c • θ) r hr=c • thetaGamma θ r hr := by
  simp only [thetaGamma,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
lemma transportT_smul (θ : Fin 3 → ℂ) (c : ℂ) (k r : Smooth)
    (hk : ∀ x,(k : X → ℂ) x≠0) (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportT (c • θ) k r hk hl=c • transportT θ k r hk hl := by
  simp only [transportT,direction_theta_smul,mul_smul_comm,smul_sub]
lemma transportQ_smul (θ : Fin 3 → ℂ) (c : ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportQ (c • θ) k r hr hk hl=c • transportQ θ k r hr hk hl := by
  funext i
  apply Subtype.ext
  funext x
  simp only [transportQ,direction_theta_smul,thetaGamma_smul,Pi.smul_apply,
    Subalgebra.coe_smul,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,smul_eq_mul]
  ring
end ElasticityAugmented
namespace ElasticityConic
open ElasticityAugmented

lemma chartDiagonal_ne_zero {z : ℂ} (hz : z≠0) (i : Fin 3) : chartDiagonal z i≠0 := by
  simp only [chartDiagonal]
  split_ifs <;> first | exact one_ne_zero | exact hz
lemma chartTheta_transition {z : ℂ} (hz : z≠0) : chartTheta false z=z^2 • chartTheta true z⁻¹ := by
  ext i
  fin_cases i <;> simp [chartTheta,theta,chartZ₀,chartZ₁,smul_eq_mul] <;> field_simp

lemma chartMatrix_transition {z : ℂ} (hz : z≠0) (T : Smooth) (Q : Fin 3 → Smooth) :
    chartMatrix false z (z^2 • T) (z^2 • Q)=
      z^2 • diagonalGauge (chartDiagonal z) (chartMatrix true z⁻¹ T Q) := by
  ext i j x
  fin_cases i <;> fin_cases j <;>
    simp [chartMatrix,diagonalGauge,chartDiagonal,chartZ₀,chartZ₁,h₁,h₂,
      Fin.sum_univ_three,smul_eq_mul] <;> field_simp

lemma physical_chart_transition {z : ℂ} (hz : z≠0) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    chartMatrix false z (transportT (chartTheta false z) k r hk hl) (transportQ (chartTheta false z) k r hr hk hl)=
      z^2 • diagonalGauge (chartDiagonal z)
        (chartMatrix true z⁻¹ (transportT (chartTheta true z⁻¹) k r hk hl) (transportQ (chartTheta true z⁻¹) k r hr hk hl)) := by
  rw [chartTheta_transition hz,transportT_smul,transportQ_smul]
  exact chartMatrix_transition hz _ _

/-- The projective conic transition law is forced by supported uniqueness;
comparisons constructed using unrelated weak subsequences glue exactly. -/
theorem supported_chart_glue (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      chartMatrix b z (transportT (chartTheta b z) (k 1) (r 1) (hk 1) (hl 1))
        (transportQ (chartTheta b z) (k 1) (r 1) (hr 1) (hk 1) (hl 1))*G b z-
      G b z*chartMatrix b z (transportT (chartTheta b z) (k 0) (r 0) (hk 0) (hl 0))
        (transportQ (chartTheta b z) (k 0) (r 0) (hr 0) (hk 0) (hl 0)))
    (z : ℂ) (hz : z≠0) : G false z=diagonalGauge (chartDiagonal z) (G true z⁻¹) := by
  let M := fun b z q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hl q))
    (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q))
  have ht (q : Fin 2) : M false z q=z^2 • diagonalGauge (chartDiagonal z) (M true z⁻¹ q) :=
    physical_chart_transition hz (k q) (r q) (hr q) (hk q) (hl q)
  have hE := diagonalGauge_equation (chartTheta true z⁻¹) (z^2) (chartDiagonal z)
    (chartDiagonal_ne_zero hz) (M true z⁻¹ 0) (M true z⁻¹ 1) (G true z⁻¹) (he true z⁻¹)
  rw [← chartTheta_transition hz,← ht 0,← ht 1] at hE
  have hS := diagonalGauge_supported hK.isClosed (chartDiagonal z) (chartDiagonal_ne_zero hz) (G true z⁻¹) (hs true z⁻¹)
  apply supported_matrix_unique (chartTheta false z) (chartTheta_null false z) (chartTheta_ne_zero false z)
    (M false z 0) (M false z 1) (G false z) (diagonalGauge (chartDiagonal z) (G true z⁻¹)) (he false z) hE
  intro i j
  have hc0 : HasCompactSupport ((G false z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hs false z i j)
  have hc1 : HasCompactSupport ((diagonalGauge (chartDiagonal z) (G true z⁻¹) i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hS i j)
  have hc := hc0.sub hc1
  have heq : (G false z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j)-
      (diagonalGauge (chartDiagonal z) (G true z⁻¹) i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j)=
      G false z i j-diagonalGauge (chartDiagonal z) (G true z⁻¹) i j := by abel
  simpa only [← Subalgebra.coe_sub,heq] using hc
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

lemma physicalChartMatrix_regular (b : Bool) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (i j : Fin 3) :
    JointHolomorphic (fun y : X × ℂ => (physicalChartMatrix b y.2 k r hr hk hl i j : X → ℂ) y.1) := by
  apply chartMatrix_regular b (fun z => transportT (chartTheta b z) k r hk hl)
    (fun z => transportQ (chartTheta b z) k r hr hk hl)
  · exact transportT_regular b k r hk hl
  · exact transportQ_regular b k r hr hk hl

lemma physicalChartMatrix_eqOn (b : Bool) (z : ℂ) (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {O : Set X} (hO : IsOpen O) (hek : EqOn (k 0 : X → ℂ) (k 1) O)
    (her : EqOn (r 0 : X → ℂ) (r 1) O) {x : X} (hx : x∈O) :
    matrixEval x (physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0))=
      matrixEval x (physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)) := by
  have hh := eqOn_transport hO (chartTheta b z) (k 0) (k 1) (r 0) (r 1)
    (hr 0) (hr 1) (hk 0) (hk 1) (hl 0) (hl 1) hek her
  ext i j
  have ht := hh.1 hx
  have hq : ∀ i,(transportQ (chartTheta b z) (k 0) (r 0) (hr 0) (hk 0) (hl 0) i : X → ℂ) x=
    (transportQ (chartTheta b z) (k 1) (r 1) (hr 1) (hk 1) (hl 1) i : X → ℂ) x := fun i => hh.2 i hx
  fin_cases i <;> fin_cases j <;> simp [physicalChartMatrix,matrixEval_apply,chartMatrix,smooth_sum_eval,ht,hq]

lemma chartTheta_smooth (b : Bool) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => chartTheta b z i) := by
  cases b <;> fin_cases i <;> dsimp [chartTheta,chartZ₀,chartZ₁,theta] <;> fun_prop

/-- Rigidity of the genuine two-chart physical connection. The entire analytic
matching input is only separately smooth supported transport; joint smoothness,
holomorphy and transition compatibility are conclusions of the transport equations, never additional properties imposed upon CGO weak limits. -/
theorem supported_physical_holomorphic (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1)
    (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
      G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
    ∀ b i j,JointHolomorphic (fun y : X × ℂ => (G b y.2 i j : X → ℂ) y.1) := by
  let T := fun b z q => transportT (chartTheta b z) (k q) (r q) (hk q) (hl q)
  let Q := fun b z q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q)
  let M := fun b z q => chartMatrix b z (T b z q) (Q b z q)
  have hMr (b : Bool) (q : Fin 2) (i j : Fin 3) : JointHolomorphic (fun y : X × ℂ => (M b y.2 q i j : X → ℂ) y.1) :=
    physicalChartMatrix_regular b (k q) (r q) (hr q) (hk q) (hl q) i j
  have hMe (b z x) (hx : x∉K) : matrixEval x (M b z 0)=matrixEval x (M b z 1) :=
    physicalChartMatrix_eqOn b z k r hr hk hl hK.isClosed.isOpen_compl hexk hexr hx
  have hGr (b : Bool) := supported_matrix_holomorphic (fun i z => chartTheta b z i)
    (chartTheta_smooth b)
    (fun i => (chartTheta_regular b i).holo 0)
    (chartTheta_null b) (chartTheta_ne_zero b) (fun z => M b z 0) (fun z => M b z 1) (G b)
    (hMr b 0) (hMr b 1) hK χ hχ hχ1 (hs b) (hMe b) (he b)
  exact hGr

theorem physical_conic_connections_equal_oai (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1) (x₀ : X) (hx₀ : x₀∉K)
    (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
      G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
    ∀ b z,physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1) := by
  let T := fun b z q => transportT (chartTheta b z) (k q) (r q) (hk q) (hl q)
  let Q := fun b z q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q)
  have hGr := supported_physical_holomorphic k r hr hk hl hK χ hχ hχ1 hexk hexr G hs he
  have hId : ∀ b z,G b z=1 := chart_comparison_trivial T Q G hGr
    (supported_chart_glue k r hr hk hl hK G hs he) he x₀
    (supported_matrix_eq_one (G false 0) (hs false 0) x₀ hx₀)
  intro b z
  have hh := he b z
  rw [hId b z,matrixD_one,mul_one,one_mul] at hh
  exact (sub_eq_zero.mp hh.symm).symm
end ElasticityConic

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityConic.physical_conic_connections_equal_oai := @OAI.ElasticityConic.physical_conic_connections_equal_oai
