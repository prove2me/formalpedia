-- Prove2me | solution 1 for OAI.Elasticity.dn_conic_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:59:39.664034+00:00
-- url     : https://prove2.me/submissions/cccbc718-3c12-4a2c-b0d5-a87413a0f9f3

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_Elasticity_dn_common_normal_frame

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
lemma smoothInv_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) : smoothInv f hf*f=1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)
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
omit [DecidableEq n] in
lemma matrixD_mul (θ : Fin 3 → ℂ) (A B : Matrix n n Smooth) :
    matrixD θ (A*B)=matrixD θ A*B+A*matrixD θ B := by
  ext i j
  simp only [matrixD,Matrix.mul_apply,Matrix.add_apply,map_sum,Derivation.leibniz,
    smul_eq_mul,Finset.sum_add_distrib]
  simp only [mul_comm,add_comm]
omit [Fintype n] in
lemma matrixD_one (θ : Fin 3 → ℂ) : matrixD θ (1 : Matrix n n Smooth)=0 := by
  ext i j
  simp only [matrixD,Matrix.one_apply,Matrix.zero_apply]
  split_ifs <;> simp

lemma smoothMatrix_isUnit (A : Matrix n n Smooth) (hA : ∀ x,IsUnit (matrixEval x A)) :
    IsUnit A.det := by
  have hd (x : X) : (A.det : X → ℂ) x≠0 := by
    have he := (smoothEval x).map_det A
    change (A.det : X → ℂ) x=(matrixEval x A).det at he
    rw [he]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hA x)).ne_zero
  exact isUnit_iff_exists_inv'.mpr ⟨smoothInv A.det hd,smoothInv_mul A.det hd⟩

/-- Smooth comparison from actual columns; only the original frame needs
invertibility. Equations are initially local and preserve their real domain. -/
theorem smooth_matrix_comparison {B K : Set X} (hK : IsClosed K)
    (θ : Fin 3 → ℂ) (M₀ M₁ Y₀ Y₁ : Matrix n n Smooth)
    (hY : ∀ x,IsUnit (matrixEval x Y₀))
    (he₀ : ∀ x∈B,matrixEval x (matrixD θ Y₀)=matrixEval x (M₀*Y₀))
    (he₁ : ∀ x∈B,matrixEval x (matrixD θ Y₁)=matrixEval x (M₁*Y₁))
    (hs : ∀ x∉K,matrixEval x Y₁=matrixEval x Y₀) :
    ∃ G : Matrix n n Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K) ∧
      (∀ x∈B,matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀)) := by
  let G := Y₁*Y₀⁻¹
  have hd := smoothMatrix_isUnit Y₀ hY
  have hG : G*Y₀=Y₁ := by dsimp [G]; rw [mul_assoc,Matrix.nonsing_inv_mul _ hd,mul_one]
  have hDG : matrixD θ G*Y₀+G*matrixD θ Y₀=matrixD θ Y₁ := by
    rw [← matrixD_mul,hG]
  refine ⟨G,?_,?_⟩
  · intro i j
    apply closure_minimal _ hK
    intro x hx
    by_contra hn
    have he : matrixEval x G=1 := by
      dsimp [G]
      rw [map_mul,hs x hn,← map_mul,Matrix.mul_nonsing_inv _ hd,map_one]
    apply hx
    change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0
    have hentry := congrArg (fun A : Matrix n n ℂ => A i j) he
    change matrixEval x G i j-matrixEval x 1 i j=0
    rw [map_one,hentry,sub_self]
  · intro x hx
    have he := congrArg (matrixEval x) hDG
    simp only [map_add,map_mul] at he
    rw [he₀ x hx,he₁ x hx] at he
    simp only [map_mul] at he
    have hGX := congrArg (matrixEval x) hG
    simp only [map_mul] at hGX
    have hh : (matrixEval x (matrixD θ G)-matrixEval x (M₁*G-G*M₀))*matrixEval x Y₀=0 := by
      simp only [map_sub,map_mul]
      calc
        _ = matrixEval x (matrixD θ G)*matrixEval x Y₀+
            matrixEval x G*(matrixEval x M₀*matrixEval x Y₀)-
            matrixEval x M₁*(matrixEval x G*matrixEval x Y₀) := by noncomm_ring
        _ = 0 := by rw [he,hGX,sub_self]
    have hinv := congrArg (fun A : Matrix n n ℂ => A*matrixEval x (Y₀⁻¹)) hh
    rw [mul_assoc,← map_mul,Matrix.mul_nonsing_inv _ hd,map_one,mul_one,zero_mul] at hinv
    exact sub_eq_zero.mp hinv
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

lemma chartCoord_apply (b : Bool) (z : ℂ) (p : Fin 3 → Smooth) (s : Smooth) (x : X) (i : Fin 3) :
    ((chartCoord b z p s i : Smooth) : X → ℂ) x=chartCoord b z (fun j => (p j : X → ℂ) x) ((s : X → ℂ) x) i := by
  cases b <;> fin_cases i <;> rfl
lemma chartCoord_deriv (θ : Fin 3 → ℂ) (b : Bool) (z : ℂ) (p : Fin 3 → Smooth) (s : Smooth) (i : Fin 3) :
    thetaDerivation θ (chartCoord b z p s i)=
      chartCoord b z (fun j => thetaDerivation θ (p j)) (thetaDerivation θ s) i := by
  cases b <;> fin_cases i <;>
    simp [chartCoord,map_sub,map_add]
lemma chartCoord_2 {A : Type*} [AddCommGroup A] [Module ℂ A]
    (b : Bool) (z : ℂ) (p : Fin 3 → A) (s : A) : chartCoord b z p s 2=s := by
  cases b <;> rfl
lemma chartCoord_top (b : Bool) (z s t : ℂ) (i : Fin 3) (hi : i≠2) :
    chartCoord b z (fun j => chartTheta b z j*s) t i=
      (if i=0 then chartZ₀ b z else chartZ₁ b z)*s := by
  have hc : i=0 ∨ i=1 := by omega
  cases b <;> rcases hc with rfl | rfl <;>
    simp [chartCoord,chartTheta,theta,chartZ₀,chartZ₁,smul_eq_mul]
  · linear_combination -(1+z^2)*s*Complex.I_sq/2
  · linear_combination z*(1+z^2)*s*Complex.I_sq/2
  · linear_combination z*(z^2+1)*s*Complex.I_sq/2
  · linear_combination -(z^2+1)*s*Complex.I_sq/2

/-- The chart connection is exactly the physical normal transport, rather
than a freely chosen augmented comparison equation. -/
lemma chart_transport_at (b : Bool) (z : ℂ) (T : Smooth) (Q p : Fin 3 → Smooth) (s : Smooth) (x : X)
    (hn : ElasticityFrame.normal (chartTheta b z) ((fun i => (p i : X → ℂ) x),(s : X → ℂ) x)=0)
    (hp : ∀ i,(direction (A := Smooth) coord (chartTheta b z) (p i) : X → ℂ) x=
      chartTheta b z i*(s : X → ℂ) x)
    (hs : (direction (A := Smooth) coord (chartTheta b z) s : X → ℂ) x=
      ((T*s+∑ i,Q i*p i : Smooth) : X → ℂ) x) (i : Fin 3) :
    (thetaDerivation (chartTheta b z) (chartCoord b z p s i) : X → ℂ) x=
      (matrixEval x (chartMatrix b z T Q)*ᵥ(fun j => ((chartCoord b z p s j : Smooth) : X → ℂ) x)) i := by
  rw [chartCoord_deriv,chartCoord_apply]
  simp only [thetaDerivation_apply,hp,hs]
  by_cases hi : i=2
  · subst i
    rw [chartCoord_2]
    have hd := congrArg Prod.fst (chartVector_coord b z
      ((fun j => (p j : X → ℂ) x),(s : X → ℂ) x) hn)
    have hdp (j : Fin 3) : (p j : X → ℂ) x=
        chartCoord b z (fun k => (p k : X → ℂ) x) ((s : X → ℂ) x) 0*h₁ (chartZ₀ b z) (chartZ₁ b z) j+
        chartCoord b z (fun k => (p k : X → ℂ) x) ((s : X → ℂ) x) 1*h₂ (chartZ₀ b z) (chartZ₁ b z) j := by
      exact (congrFun hd j).symm
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,chartMatrix,matrixEval_apply,
      Matrix.of_apply,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,
      Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_smul,Pi.add_apply,Pi.mul_apply,Pi.smul_apply,
      smul_eq_mul,chartCoord_apply,chartCoord_2]
    rw [hdp 0,hdp 1,hdp 2]
    ring
  · rw [chartCoord_top b z _ _ i hi]
    have hc : i=0 ∨ i=1 := by omega
    rcases hc with rfl | rfl <;>
      simp [Matrix.mulVec,dotProduct,chartMatrix,Fin.sum_univ_three,chartCoord_2]
end ElasticityConic

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

lemma globalize_matrix_comparison {B K : Set X} (hK : IsClosed K) (hKB : K⊆B)
    (θ : Fin 3 → ℂ) (M₀ M₁ G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ x∈B,matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀))
    (hM : ∀ x∉K,matrixEval x M₀=matrixEval x M₁) :
    matrixD θ G=M₁*G-G*M₀ := by
  ext i j x
  by_cases hx : x∈B
  · exact congrArg (fun A : Matrix n n ℂ => A i j) (he x hx)
  · have hn : x∉K := fun hh => hx (hKB hh)
    have hG := supported_matrix_eq_one G hs x hn
    have hD : matrixEval x (matrixD θ G)=0 := by
      ext a b
      have hh := eqOn_direction hK.isOpen_compl θ (G a b) ((1 : Matrix n n Smooth) a b)
        (fun y hy => (congrArg (fun A : Matrix n n ℂ => A a b) (supported_matrix_eq_one G hs y hy)).trans
          (congrArg (fun A : Matrix n n ℂ => A a b) (map_one (matrixEval (n := n) y))).symm) hn
      change (thetaDerivation θ (G a b) : X → ℂ) x=(thetaDerivation θ ((1 : Matrix n n Smooth) a b) : X → ℂ) x at hh
      rw [show thetaDerivation θ ((1 : Matrix n n Smooth) a b)=0 from congrFun (congrFun (matrixD_one (n := n) θ) a) b] at hh
      exact hh
    have hh : matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀) := by
      simp only [map_sub,map_mul,hD,hG,mul_one,one_mul,hM x hn,sub_self]
    exact congrArg (fun A : Matrix n n ℂ => A i j) hh

end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

/-- Convert the actual physical rank-three fiber basis to a chart matrix;
there is no assumption that the transferred columns are a basis. -/
theorem chart_frame_comparison {U K : Set X} (hK : IsClosed K) (hKU : K⊆U)
    (b : Bool) (z : ℂ) (T : Fin 2 → Smooth) (Q : Fin 2 → Fin 3 → Smooth)
    (p : Fin 2 → Fin 3 → Fin 3 → Smooth) (s : Fin 2 → Fin 3 → Smooth)
    (B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber (chartTheta b z)))
    (hn : ∀ q ν,normal (chartTheta b z) (p q ν)=0)
    (he : ∀ q ν x,x∈U →
      (∀ i,(direction (A := Smooth) coord (chartTheta b z) (p q ν i) : X → ℂ) x=
        chartTheta b z i*(s q ν : X → ℂ) x) ∧
      (direction (A := Smooth) coord (chartTheta b z) (s q ν) : X → ℂ) x=
        ((T q*s q ν+∑ i,Q q i*p q ν i : Smooth) : X → ℂ) x)
    (hs : ∀ ν x,x∉K → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
      (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x)
    (hB : ∀ ν x,((B x ν : ElasticityFrame.Fiber (chartTheta b z)) : ElasticityFrame.Amp)=
      ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x))
    (hT : ∀ x∉K,(T 0 : X → ℂ) x=(T 1 : X → ℂ) x)
    (hQ : ∀ i x,x∉K → (Q 0 i : X → ℂ) x=(Q 1 i : X → ℂ) x) :
    ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K) ∧
      matrixD (chartTheta b z) G=chartMatrix b z (T 1) (Q 1)*G-G*chartMatrix b z (T 0) (Q 0) := by
  let Y : Fin 2 → Matrix (Fin 3) (Fin 3) Smooth := fun q i ν => chartCoord b z (p q ν) (s q ν) i
  have hunit (x : X) : IsUnit (matrixEval x (Y 0)) := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    let C := (B x).map (conicChart b z).symm
    have hCb : (C : Fin 3 → Fin 3 → ℂ)=(fun ν => (matrixEval x (Y 0)).col ν) := by
      funext ν i
      change chartCoord b z (B x ν).val.1 (B x ν).val.2 i=_
      rw [hB]
      exact (chartCoord_apply b z (p 0 ν) (s 0 ν) x i).symm
    change LinearIndependent ℂ (fun ν => (matrixEval x (Y 0)).col ν)
    exact hCb ▸ C.linearIndependent
  have hEq (q x) (hx : x∈U) :
      matrixEval x (matrixD (chartTheta b z) (Y q))=
        matrixEval x (chartMatrix b z (T q) (Q q)*Y q) := by
    ext i ν
    have hn' : ElasticityFrame.normal (chartTheta b z)
        ((fun i => (p q ν i : X → ℂ) x),(s q ν : X → ℂ) x)=0 := by
      have hh := congrArg (fun f : Smooth => (f : X → ℂ) x) (hn q ν)
      change (∑ i,chartTheta b z i*(p q ν i : X → ℂ) x)=0
      simpa only [normal,dotProduct,smooth_sum_eval,
        Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul,Subalgebra.coe_zero,Pi.zero_apply] using hh
    have hh := chart_transport_at b z (T q) (Q q) (p q ν) (s q ν) x hn' (he q ν x hx).1 (he q ν x hx).2 i
    rw [map_mul]
    exact hh
  have hext (x : X) (hx : x∉K) : matrixEval x (Y 1)=matrixEval x (Y 0) := by
    ext i ν
    change ((chartCoord b z (p 1 ν) (s 1 ν) i : Smooth) : X → ℂ) x=
      ((chartCoord b z (p 0 ν) (s 0 ν) i : Smooth) : X → ℂ) x
    rw [chartCoord_apply,chartCoord_apply,(hs ν x hx).2,funext ((hs ν x hx).1)]
  obtain ⟨G,hGs,hGe⟩ := smooth_matrix_comparison hK (chartTheta b z)
    (chartMatrix b z (T 0) (Q 0)) (chartMatrix b z (T 1) (Q 1)) (Y 0) (Y 1)
    hunit (hEq 0) (hEq 1) hext
  refine ⟨G,hGs,globalize_matrix_comparison hK hKU (chartTheta b z) _ _ G hGs hGe ?_⟩
  intro x hx
  ext i j
  change ((chartMatrix b z (T 0) (Q 0) i j : Smooth) : X → ℂ) x=
    ((chartMatrix b z (T 1) (Q 1) i j : Smooth) : X → ℂ) x
  have hq : ∀ k,(Q 0 k : X → ℂ) x=(Q 1 k : X → ℂ) x := fun k => hQ k x hx
  fin_cases i <;> fin_cases j <;> simp [chartMatrix,smooth_sum_eval,hq,hT x hx]
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace Elasticity
open ElasticityAugmented ElasticityCGO ElasticityConic
open ElasticityCoeffBounds (ExteriorConstant)

/-- Supported global commutator comparison on EACH conic chart, constructed
from equality of the physical DN map on the original domain. -/
theorem dn_conic_comparison_oai {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) (b : Bool) (z : ℂ) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∀ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∀ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    let M := fun q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
      (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
    ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆closure Ω) ∧
      matrixD (chartTheta b z) G=M 1*G-G*M 0 := by
  intro k r hr hk hL M
  obtain ⟨hk',hL',p,s,B,hn,hE,hs,hB⟩ := dn_common_normal_frame hΩ hOB r₀ hr₀ hK (chartTheta b z)
    (chartTheta_null b z) (chartTheta_ne_zero b z) lam m hl hm hp hcll hclm he hDN
  have hkE : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
    intro y hy
    have hy' : y∉Ω := fun hyΩ => hy (subset_closure hyΩ)
    change (lam 0 y : ℂ)+(m 0 y : ℂ)=(lam 1 y : ℂ)+(m 1 y : ℂ)
    rw [(he y hy').1,(he y hy').2]
  have hrE : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
    intro y hy
    change (Real.sqrt (m 0 y) : ℂ)=(Real.sqrt (m 1 y) : ℂ)
    rw [(he y (fun hyΩ => hy (subset_closure hyΩ))).2]
  have hMQ := eqOn_transport isClosed_closure.isOpen_compl (chartTheta b z) (k 0) (k 1) (r 0) (r 1)
    (hr 0) (hr 1) (hk 0) (hk 1) (hL 0) (hL 1) hkE hrE
  exact chart_frame_comparison isClosed_closure (hK.trans (Metric.closedBall_subset_ball (by linarith))) b z
    (fun q => transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
    (fun q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
    p s B hn hE hs hB (fun x hx => hMQ.1 hx) (fun i x hx => hMQ.2 i hx)
end Elasticity

end
end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.dn_conic_comparison_oai := @OAI.Elasticity.dn_conic_comparison_oai
