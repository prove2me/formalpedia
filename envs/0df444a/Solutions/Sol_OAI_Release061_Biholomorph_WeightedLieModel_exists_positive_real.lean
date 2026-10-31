-- Prove2me | solution 1 for OAI.Release061.Biholomorph.WeightedLieModel.exists_positive_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:53:39.179016+00:00
-- url     : https://prove2.me/submissions/e930a3db-3738-442c-b40f-7a4f83514fec

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FieldSecondJet
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology

open Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 omit [CompleteSpace E] in
 theorem hasFDerivAt_centeredLinear (A : E →L[ℂ] E) (p x : E) :
    HasFDerivAt (fun y => A (y-p)) A x := by
  convert A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p) using 1 <;> rfl

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_eq (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V =
      fun x => (fderiv ℂ V x) (A (x-p))-A (V x) := by
  funext x
  rw [VectorField.lieBracket,(hasFDerivAt_centeredLinear A p x).fderiv]

 theorem fderiv_lieBracket_centeredLinear (A : E →L[ℂ] E) (p : E)
    {V : E → E} {x : E} (hV : AnalyticAt ℂ V x) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) x=
      (fderiv ℂ V x).comp A+(fderiv ℂ (fderiv ℂ V) x).flip (A (x-p))-
        A.comp (fderiv ℂ V x) := by
  rw [lieBracket_centeredLinear_eq]
  have hd := (hV.fderiv.differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_centeredLinear A p x)).sub
    (A.hasFDerivAt.comp x hV.differentiableAt.hasFDerivAt)
  exact hd.fderiv

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_zeroJet (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V p= -A (V p) := by
  rw [lieBracket_centeredLinear_eq]
  simp

 theorem lieBracket_centeredLinear_firstJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) p=
      (fderiv ℂ V p).comp A-A.comp (fderiv ℂ V p) := by
  rw [fderiv_lieBracket_centeredLinear A p hV]
  simp

 theorem lieBracket_centeredLinear_secondJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) (u v : E) :
    (fderiv ℂ (fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V)) p) u v=
      (fderiv ℂ (fderiv ℂ V) p) u (A v)+
      (fderiv ℂ (fderiv ℂ V) p) v (A u)-A ((fderiv ℂ (fderiv ℂ V) p) u v) := by
  let R : E → E →L[ℂ] E →L[ℂ] E := fun x => (fderiv ℂ (fderiv ℂ V) x).flip
  have hR : DifferentiableAt ℂ R p := by
    have hL : Differentiable ℂ (fun B : E →L[ℂ] E →L[ℂ] E => B.flip) := by
      exact LinearIsometryEquiv.differentiable (𝕜 := ℂ) (E := E →L[ℂ] E →L[ℂ] E)
        (F := E →L[ℂ] E →L[ℂ] E) (ContinuousLinearMap.flipₗᵢ ℂ E E E)
    exact DifferentiableAt.comp (𝕜 := ℂ) (F := E →L[ℂ] E →L[ℂ] E)
      (G := E →L[ℂ] E →L[ℂ] E) p (hL _) hV.fderiv.fderiv.differentiableAt
  have he : fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) =ᶠ[𝓝 p]
      fun x => (fderiv ℂ V x).comp A+R x (A (x-p))-A.comp (fderiv ℂ V x) := by
    filter_upwards [hV.eventually_analyticAt] with x hx
    exact fderiv_lieBracket_centeredLinear A p hx
  rw [he.fderiv_eq]
  have h1 := hV.fderiv.differentiableAt.hasFDerivAt.clm_comp (hasFDerivAt_const A p)
  have h2 := hR.hasFDerivAt.clm_apply (hasFDerivAt_centeredLinear A p p)
  have h3 := (hasFDerivAt_const A p).clm_comp hV.fderiv.differentiableAt.hasFDerivAt
  have hd := (h1.add h2).sub h3
  change (fderiv ℂ (((fun x => (fderiv ℂ V x).comp A)+fun x => R x (A (x-p)))-
    fun x => A.comp (fderiv ℂ V x)) p) u v=_
  rw [hd.fderiv]
  simp only [R, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  simp only [sub_self, map_zero, zero_apply, zero_add, add_zero]
end

open Filter Topology

open Filter Topology

open Polynomial

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticSecondJetCoordinates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
namespace LinearMap
open scoped _root_.LinearMap
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (e : V →ₗ[K] (ι → K)) (w : ι → K)
    (he : ∀ x i, e (A x) i=w i*e x i)
include he

 theorem diagonal_coordinate_pow (n : ℕ) (x : V) (i : ι) :
    e ((A^n) x) i=(w i)^n*e x i := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ',Module.End.mul_apply,he,hn,pow_succ']
    ring

 theorem diagonal_coordinate_aeval (p : K[X]) (x : V) (i : ι) :
    e ((aeval A p) x) i=p.eval (w i)*e x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,LinearMap.add_apply,Pi.add_apply,eval_add,hp,hq,add_mul]
  | monomial n a =>
    simp only [aeval_monomial,eval_monomial,Module.End.mul_apply,
      Module.algebraMap_end_apply,map_smul,Pi.smul_apply,smul_eq_mul,
      diagonal_coordinate_pow A e w he,mul_assoc]

 theorem diagonal_faithful_aeval_eq_zero (hinj : Function.Injective e)
    (s : Finset K) (hw : ∀ i, w i∈s) :
    aeval A (∏ a∈s, (X-C a))=0 := by
  classical
  ext x
  apply hinj
  funext i
  rw [diagonal_coordinate_aeval A e w he]
  have hz : (∏ a∈s, (X-C a)).eval (w i)=0 := by
    simp only [eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (hw i) (sub_self (w i))
  simp [hz]

 theorem diagonal_faithful_isSemisimple (hinj : Function.Injective e)
    (s : Finset K) (hw : ∀ i, w i∈s) : A.IsSemisimple := by
  classical
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree)
  exact diagonal_faithful_aeval_eq_zero A e w he hinj s hw

 theorem diagonal_faithful_eigenvalue_mem (hinj : Function.Injective e)
    {μ : K} (hμ : A.HasEigenvalue μ) : ∃ i, w i=μ := by
  classical
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hμ
  rw [Module.End.mem_eigenspace_iff] at hx
  by_contra! h
  apply hx0
  apply hinj
  funext i
  have hh := he x i
  rw [hx,map_smul,Pi.smul_apply,smul_eq_mul] at hh
  have hi : e x i=0 := by
    have hz : (μ-w i)*e x i=0 := by rw [sub_mul,hh,sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (h i).symm)
  simpa using hi

end LinearMap

open Filter Topology

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (b : Module.Basis ι ℂ E)

 theorem analyticSecondJetCoordinates_eq_zero_iff (X : V) :
    analyticSecondJetCoordinates F p hF b X=0 ↔ ZeroSecondJet (F X) p := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inl i)
    · apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro j
      apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inr (.inl (i,j)))
    · apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro j
      apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro k
      apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inr (.inr (i,j,k)))
  · rintro ⟨h0,h1,h2⟩
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet,h0,h1,h2]

 theorem analyticSecondJetCoordinates_injective
    (hjet : ∀ X, ZeroSecondJet (F X) p → X=0) :
    Function.Injective (analyticSecondJetCoordinates F p hF b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  exact hjet X ((analyticSecondJetCoordinates_eq_zero_iff F p hF b X).mp hX)

 omit [CompleteSpace E] in
 theorem basis_coordinate_diagonal (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (x : E) (i : ι) :
    b.repr (A x) i=w i*b.repr x i := by
  classical
  have he : (b.coord i).comp A.toLinearMap=w i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hA,map_smul,
      LinearMap.smul_apply,Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      smul_eq_mul]
    split_ifs with h
    · subst j; rfl
    · simp
  exact LinearMap.congr_fun he x

 theorem analyticSecondJetCoordinates_euler (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (B : Module.End ℂ V)
    (hB : ∀ X, F (B X) =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun y => A (y-p)) (F X)) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (B X) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b X j := by
  intro X j
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · change b.repr (F (B X) p) i=(-w i)*b.repr (F X p) i
    rw [(hB X).eq_of_nhds,lieBracket_centeredLinear_zeroJet,map_neg,Finsupp.neg_apply,
      basis_coordinate_diagonal b A w hA,neg_mul]
  · change b.repr (fderiv ℂ (F (B X)) p (b j)) i=(w j-w i)*b.repr (fderiv ℂ (F X) p (b j)) i
    rw [(hB X).fderiv_eq,lieBracket_centeredLinear_firstJet A p (hF X)]
    simp only [sub_apply,ContinuousLinearMap.comp_apply,hA,map_smul,
      map_sub,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    ring
  · change b.repr (fderiv ℂ (fderiv ℂ (F (B X))) p (b j) (b k)) i=
      (w j+w k-w i)*b.repr (fderiv ℂ (fderiv ℂ (F X)) p (b j) (b k)) i
    rw [(hB X).fderiv.fderiv_eq,lieBracket_centeredLinear_secondJet A p (hF X),hA,hA]
    simp only [map_smul,map_add,map_sub,Finsupp.add_apply,
      Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    rw [((hF X).contDiffAt.isSymmSndFDerivAt_of_omega) (b k) (b j)]
    ring

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexTensorNormalForm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology

open scoped TensorProduct
open Set Filter Topology

theorem complex_tensor_normalForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Z : ℂ ⊗[ℝ] V) : ∃ X Y : V, Z=1 ⊗ₜ[ℝ] X+Complex.I ⊗ₜ[ℝ] Y := by
  induction Z using OAI.tensorInductionOn with
  | tmul z X =>
    refine ⟨z.re • X,z.im • X,?_⟩
    rw [TensorProduct.tmul_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul',TensorProduct.smul_tmul',←TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul]
  | add Z W hZ hW =>
    obtain ⟨X,Y,rfl⟩ := hZ
    obtain ⟨X',Y',rfl⟩ := hW
    exact ⟨X+X',Y+Y',by simp only [TensorProduct.tmul_add]; abel⟩

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ImagPartLieReal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Complexification
section Linear
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem normalForm (Z : ℂ ⊗[ℝ] V) : Z=ofReal (realPart Z)+Complex.I • ofReal (imagPart Z) := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [TensorProduct.smul_tmul']

@[ext] theorem ext {Z W : ℂ ⊗[ℝ] V} (hr : realPart Z=realPart W)
    (hi : imagPart Z=imagPart W) : Z=W := by
  rw [normalForm Z,normalForm W,hr,hi]

@[simp] theorem realPart_I_smul (Z : ℂ ⊗[ℝ] V) : realPart (Complex.I • Z) = -imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']
@[simp] theorem imagPart_I_smul (Z : ℂ ⊗[ℝ] V) : imagPart (Complex.I • Z) = realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']

@[simp] theorem realPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    realPart ((c : ℂ) • Z)=c • realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_re]
@[simp] theorem imagPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    imagPart ((c : ℂ) • Z)=c • imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_im]

end Linear
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]

@[simp] theorem realPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    realPart ⁅ofReal X,Z⁆=⁅X,realPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]
@[simp] theorem imagPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    imagPart ⁅ofReal X,Z⁆=⁅X,imagPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]

 theorem realPart_eigen (E : V) (μ : ℝ) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : ⁅E,realPart Z⁆=μ • realPart Z := by
  simpa only [realPart_lie_ofReal,realPart_real_smul] using congrArg realPart hZ
 theorem imagPart_eigen (E : V) (μ : ℝ) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : ⁅E,imagPart Z⁆=μ • imagPart Z := by
  simpa only [imagPart_lie_ofReal,imagPart_real_smul] using congrArg imagPart hZ

 theorem eigen_eq_zero_of_imaginary_bracket (E H : V) (μ : ℝ)
    (h : ∀ Z : ℂ ⊗[ℝ] V, ⁅ofReal E,Z⁆=(μ : ℂ) • Z →
      ⁅ofReal H,Z⁆=Complex.I • Z) {Z : ℂ ⊗[ℝ] V}
    (hZ : ⁅ofReal E,Z⁆=(μ : ℂ) • Z) : Z=0 := by
  have hz (X : V) (hX : ⁅E,X⁆=μ • X) : X=0 := by
    have he : ⁅ofReal E,ofReal X⁆=(μ : ℂ) • ofReal X := by
      rw [←ofReal_lie,hX,map_smul]
      exact (IsScalarTower.algebraMap_smul ℂ μ (ofReal X)).symm
    have hh := congrArg imagPart (h (ofReal X) he)
    simpa using hh.symm
  have hr := hz (realPart Z) (realPart_eigen E μ hZ)
  have hi := hz (imagPart Z) (imagPart_eigen E μ hZ)
  rw [normalForm Z,hr,hi,map_zero,smul_zero,add_zero]
end Complexification

open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Geometry
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
namespace LieFieldJets
variable {G E ι : Type*} [LieRing G] [LieAlgebra ℂ G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : G →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (hjet : ∀ X, ZeroSecondJet (F X) p → X=0)
    (hlie : ∀ X Y, F ⁅X,Y⁆=VectorField.lieBracket ℂ (F X) (F Y))
    (b : Module.Basis ι ℂ E)

include hlie
 omit [CompleteSpace E] in
 theorem centered_bracket (L : G) (A : E →L[ℂ] E)
    (hL : F L =ᶠ[𝓝 p] fun x => A (x-p)) (X : G) :
    F ⁅L,X⁆ =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun x => A (x-p)) (F X) := by
  rw [hlie]
  filter_upwards [hL.eventually_nhds] with x hx
  have he : F L =ᶠ[𝓝 x] fun y => A (y-p) := hx
  simp only [VectorField.lieBracket,he.eq_of_nhds,he.fderiv_eq]

 theorem conjugated_diagonal (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (c ⁅L,X⁆) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b (c X) j := by
  intro X j
  rw [c.map_lie]
  exact analyticSecondJetCoordinates_euler F p hF b A w hA
    (LieAlgebra.ad ℂ G (c L))
    (fun X => centered_bracket F p hlie (c L) A hL X) (c X) j

include hF hjet
 theorem conjugated_ad_semisimple (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (s : Finset ℂ) (hs : ∀ j, secondJetWeight w j∈s) :
    (LieAlgebra.ad ℂ G L).IsSemisimple := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  apply LinearMap.diagonal_faithful_isSemisimple (LieAlgebra.ad ℂ G L) J (secondJetWeight w)
    (conjugated_diagonal F p hF hlie b c L A hL w hA)
    ((analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective) s hs

 theorem conjugated_ad_eigenvalue (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) {μ : ℂ}
    (hμ : (LieAlgebra.ad ℂ G L).HasEigenvalue μ) : ∃ j, secondJetWeight w j=μ := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  exact LinearMap.diagonal_faithful_eigenvalue_mem (LieAlgebra.ad ℂ G L) J (secondJetWeight w)
    (conjugated_diagonal F p hF hlie b c L A hL w hA)
    ((analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective) hμ

 theorem conjugated_second_ad_relation (c : G ≃ₗ⁅ℂ⁆ G) (L H : G)
    (A B : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p))
    (hH : F (c H) =ᶠ[𝓝 p] fun x => B (x-p))
    (w v : ι → ℂ) (hA : ∀ i, A (b i)=w i • b i) (hB : ∀ i, B (b i)=v i • b i)
    (μ ν : ℂ) (hweight : ∀ j, secondJetWeight w j=μ → secondJetWeight v j=ν)
    (X : G) (hX : ⁅L,X⁆=μ • X) : ⁅H,X⁆=ν • X := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  have hi : Function.Injective J :=
    (analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective
  apply hi
  ext j
  have he := conjugated_diagonal F p hF hlie b c L A hL w hA X j
  have hh := conjugated_diagonal F p hF hlie b c H B hH v hB X j
  change J ⁅L,X⁆ j=secondJetWeight w j*J X j at he
  change J ⁅H,X⁆ j=secondJetWeight v j*J X j at hh
  simp only [hX,map_smul,Pi.smul_apply,smul_eq_mul] at he
  change J ⁅H,X⁆ j=J (ν • X) j
  rw [hh,map_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hw : secondJetWeight w j=μ
  · rw [hweight j hw]
  · have hz : J X j=0 := by
      have hz : (secondJetWeight w j-μ)*J X j=0 := by rw [sub_mul,←he,sub_self]
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw)
    simp [hz]
end LieFieldJets

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InnerExp
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology

open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

variable [LieAlgebra ℚ L]

 theorem innerExp_apply_of_square_zero (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hX : ⁅T,⁅T,X⁆⁆=0) : innerExp T hT c X=X+c • ⁅T,X⁆ := by
  let A := c • LieAlgebra.ad ℂ L T
  have hn : IsNilpotent A := hT.smul c
  have hs : (A^2) • X=0 := by
    change A (A X)=0
    simp [A,hX]
  change IsNilpotent.exp A X=_
  have he := IsNilpotent.exp_smul_eq_sum hs hn
  change IsNilpotent.exp A X= _ at he
  rw [he]
  simp [Finset.sum_range_succ,A,Module.End.smul_def]

 theorem innerExp_euler (T E : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (hTE : ⁅T,E⁆=T) (c : ℂ) : innerExp T hT c E=E+c • T := by
  rw [innerExp_apply_of_square_zero T hT c E (by rw [hTE,lie_self]),hTE]

 theorem innerExp_fixed (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hTX : ⁅T,X⁆=0) : innerExp T hT c X=X := by
  rw [innerExp_apply_of_square_zero T hT c X (by rw [hTX,lie_zero]),hTX,smul_zero,add_zero]

end LieAlgebra

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelRotationWeight
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
namespace Biholomorph

 theorem flatWeightedEuler_basis (r k : ℕ) (i : ModelIndex r k) :
    flatWeightedEuler r k (modelBasis r k i)=modelEulerWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatWeightedEuler,modelEulerWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem flatTangentialInfinitesimal_basis (r k : ℕ) (i : ModelIndex r k) :
    flatTangentialInfinitesimal r k (modelBasis r k i)=modelRotationWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatTangentialInfinitesimal,modelRotationWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem secondJet_modelEulerWeight_mem {r k : ℕ} (j : SecondJetIndex (ModelIndex r k)) :
    secondJetWeight modelEulerWeight j∈({-1,-(1/2),0,1/2,1,3/2} : Finset ℂ) := by
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · cases i <;> norm_num [secondJetWeight,modelEulerWeight]
  · cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight]
  · cases i <;> cases j <;> cases k <;> norm_num [secondJetWeight,modelEulerWeight]

 theorem modelEuler_extreme_rotation {r k : ℕ} (j : SecondJetIndex (ModelIndex r k))
    (hj : secondJetWeight modelEulerWeight j=(3/2 : ℂ)) :
    secondJetWeight modelRotationWeight j=-Complex.I := by
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · cases i <;> norm_num [secondJetWeight,modelEulerWeight] at hj
  · cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight] at hj
  · cases i <;> cases j <;> cases k <;>
      norm_num [secondJetWeight,modelEulerWeight] at hj
    norm_num [secondJetWeight,modelRotationWeight]

 theorem flatTangentialInfinitesimal_normal {r k : ℕ} (a : Fin k → ℝ) :
    flatTangentialInfinitesimal r k (flatNormalVector r k a)=0 := by
  simp [flatTangentialInfinitesimal,flatNormalVector]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EulerSpectrum
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph

namespace WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

theorem translation_rotation : ⁅M.T,M.H⁆=0 := by
  apply M.eq_of_germ
  apply (M.lie_germ M.translation_germ M.rotation_germ).trans
  filter_upwards [] with x
  rw [VectorField.lieBracket,(flatTangentialInfinitesimal r k).fderiv,fderiv_const_apply]
  simp only [zero_apply,sub_zero,flatTangentialInfinitesimal_normal,map_zero,Pi.zero_apply]

attribute [local instance] OAI.Release061.Biholomorph.WeightedLieModel.complexificationRatLieAlgebra
theorem center_euler : M.center M.E=M.E-Complex.I • M.T := by
  rw [center,LieAlgebra.innerExp_euler _ _ _ M.translation_euler]
  simp [sub_eq_add_neg]

theorem center_rotation : M.center M.H=M.H :=
  LieAlgebra.innerExp_fixed _ _ _ _ M.translation_rotation

theorem centered_euler_germ : M.field (M.center M.E) =ᶠ[𝓝 M.point]
    fun x => flatWeightedEuler r k (x-M.point) := by
  rw [M.center_euler,map_sub,map_smul]
  filter_upwards [M.euler_germ,M.translation_germ] with x hx hy
  simp only [Pi.sub_apply,Pi.smul_apply,hx,hy,map_sub,map_smul,point,flatWeightedEuler_normal]

theorem centered_rotation_germ : M.field (M.center M.H) =ᶠ[𝓝 M.point]
    fun x => flatTangentialInfinitesimal r k (x-M.point) := by
  rw [M.center_rotation]
  filter_upwards [M.rotation_germ] with x hx
  simp only [hx,map_sub,map_smul,point,flatTangentialInfinitesimal_normal,smul_zero,sub_zero]

theorem euler_semisimple : (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).IsSemisimple := by
  exact LieFieldJets.conjugated_ad_semisimple M.field M.point M.analytic M.jet_injective M.lie
    (modelBasis r k) M.center M.E (flatWeightedEuler r k) M.centered_euler_germ modelEulerWeight
    (flatWeightedEuler_basis r k) _ secondJet_modelEulerWeight_mem

theorem euler_extreme_rotation (X : ℂ ⊗[ℝ] G) (hX : ⁅M.E,X⁆=(3/2 : ℂ) • X) :
    ⁅M.H,X⁆= -Complex.I • X := by
  exact LieFieldJets.conjugated_second_ad_relation M.field M.point M.analytic M.jet_injective M.lie
    (modelBasis r k) M.center M.E M.H (flatWeightedEuler r k) (flatTangentialInfinitesimal r k)
    M.centered_euler_germ M.centered_rotation_germ modelEulerWeight modelRotationWeight
    (flatWeightedEuler_basis r k) (flatTangentialInfinitesimal_basis r k) (3/2) (-Complex.I)
    modelEuler_extreme_rotation X hX

theorem euler_extreme_zero (X : ℂ ⊗[ℝ] G) (hX : ⁅M.E,X⁆=(3/2 : ℂ) • X) : X=0 := by
  apply Complexification.eigen_eq_zero_of_imaginary_bracket M.euler (-M.rotation) (3/2)
  · intro Z hZ
    have hz := M.euler_extreme_rotation Z (by simpa using hZ)
    change ⁅Complexification.ofReal (-M.rotation),Z⁆=_
    rw [map_neg,neg_lie]
    change -⁅M.H,Z⁆=_
    rw [hz,neg_smul,neg_neg]
  · simpa using hX

theorem euler_spectrum (μ : ℂ) (hμ : (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).HasEigenvalue μ) :
    μ∈({-1,-(1/2),0,1/2,1} : Finset ℂ) := by
  obtain ⟨j,hj⟩ := LieFieldJets.conjugated_ad_eigenvalue M.field M.point M.analytic
    M.jet_injective M.lie (modelBasis r k) M.center M.E (flatWeightedEuler r k)
    M.centered_euler_germ modelEulerWeight (flatWeightedEuler_basis r k) hμ
  have hm := secondJet_modelEulerWeight_mem j
  rw [hj] at hm
  have hne : μ≠(3/2 : ℂ) := by
    intro he
    obtain ⟨X,hX,hne⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    have hx := M.euler_extreme_zero X (by simpa [he] using (Module.End.mem_eigenspace_iff.mp hX))
    exact hne hx
  simpa only [Finset.mem_insert,Finset.mem_singleton] using
    (by simpa only [Finset.mem_insert,Finset.mem_singleton,hne,or_false] using hm :
      μ=-1 ∨ μ= -(1/2 : ℂ) ∨ μ=0 ∨ μ=1/2 ∨ μ=1)

end WeightedLieModel
end Release061.Biholomorph

open Filter Topology
open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneKernel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

attribute [local instance] complexificationRatLieAlgebra

theorem euler_jet (X : ℂ ⊗[ℝ] G) (j : SecondJetIndex (ModelIndex r k)) :
    M.jet (M.center ⁅M.E,X⁆) j=secondJetWeight modelEulerWeight j*M.jet (M.center X) j :=
  LieFieldJets.conjugated_diagonal M.field M.point M.analytic M.lie (modelBasis r k)
    M.center M.E (flatWeightedEuler r k) M.centered_euler_germ modelEulerWeight
    (flatWeightedEuler_basis r k) X j

theorem rotation_jet (X : ℂ ⊗[ℝ] G) (j : SecondJetIndex (ModelIndex r k)) :
    M.jet (M.center ⁅M.H,X⁆) j=secondJetWeight modelRotationWeight j*M.jet (M.center X) j :=
  LieFieldJets.conjugated_diagonal M.field M.point M.analytic M.lie (modelBasis r k)
    M.center M.H (flatTangentialInfinitesimal r k) M.centered_rotation_germ modelRotationWeight
    (flatTangentialInfinitesimal_basis r k) X j

theorem eigen_jet_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (j : SecondJetIndex (ModelIndex r k)) (hj : secondJetWeight modelEulerWeight j≠μ) :
    M.jet (M.center X) j=0 := by
  have he := M.euler_jet X j
  simp only [hX,map_smul,Pi.smul_apply,smul_eq_mul] at he
  have hh : (secondJetWeight modelEulerWeight j-μ)*M.jet (M.center X) j=0 := by
    rw [sub_mul,←he,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hj)

theorem centered_value_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (hμ : μ=0 ∨ μ=1/2 ∨ μ=1) : M.field (M.center X) M.point=0 := by
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inl i) (by
    rcases hμ with rfl|rfl|rfl <;> cases i <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates] using hh

theorem centered_firstJet_one_zero {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1 : ℂ) • X) :
    M.firstJet (M.center X)=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inr (.inl (i,j))) (by
    cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates,firstJet] using hh

theorem centered_half_rotation_firstJet {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1/2 : ℂ) • X) :
    M.firstJet (M.center ⁅M.H,X⁆)= -Complex.I • M.firstJet (M.center X) := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.rotation_jet X (.inr (.inl (i,j)))
  change (modelBasis r k).repr ((M.firstJet (M.center ⁅M.H,X⁆)) (modelBasis r k j)) i=
    secondJetWeight modelRotationWeight (.inr (.inl (i,j)))*
      (modelBasis r k).repr ((M.firstJet (M.center X)) (modelBasis r k j)) i at hh
  change (modelBasis r k).repr ((M.firstJet (M.center ⁅M.H,X⁆)) (modelBasis r k j)) i=
    (modelBasis r k).repr ((-Complex.I • M.firstJet (M.center X)) (modelBasis r k j)) i
  simp only [smul_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [hh]
  by_cases hw : secondJetWeight modelEulerWeight (.inr (.inl (i,j)))=(1/2 : ℂ)
  · have hv : secondJetWeight modelRotationWeight (.inr (.inl (i,j)))= -Complex.I := by
      cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight] at hw
      simp [secondJetWeight,modelRotationWeight]
    rw [hv]
  · have hz := M.eigen_jet_zero hX (.inr (.inl (i,j))) hw
    change (modelBasis r k).repr ((M.firstJet (M.center X)) (modelBasis r k j)) i=0 at hz
    rw [hz,mul_zero,mul_zero]

theorem centered_rotation_value (X : ℂ ⊗[ℝ] G) :
    M.field (M.center ⁅M.H,X⁆) M.point= -flatTangentialInfinitesimal r k (M.field (M.center X) M.point) := by
  rw [M.center.map_lie,M.center_rotation]
  have he := LieFieldJets.centered_bracket M.field M.point M.lie M.H
    (flatTangentialInfinitesimal r k) (by simpa only [M.center_rotation] using M.centered_rotation_germ)
    (M.center X)
  rw [he.eq_of_nhds,lieBracket_centeredLinear_zeroJet]

theorem ofReal_eigen {X : G} {μ : ℝ} (hX : ⁅M.euler,X⁆=μ • X) :
    ⁅M.E,Complexification.ofReal X⁆=(μ : ℂ) • Complexification.ofReal X := by
  rw [←Complexification.ofReal_lie,hX,map_smul]
  exact (IsScalarTower.algebraMap_smul ℂ μ (Complexification.ofReal X)).symm

theorem center_of_commutes {X : ℂ ⊗[ℝ] G} (hX : ⁅M.T,X⁆=0) : M.center X=X :=
  LieAlgebra.innerExp_fixed _ _ _ _ hX

theorem real_zero_of_zero_jet (X : G)
    (h0 : M.field (Complexification.ofReal X) M.point=0)
    (h1 : M.firstJet (Complexification.ofReal X)=0) : X=0 := by
  apply M.isotropy_real X 0 h0
  · simp
  · change M.firstJet (Complexification.ofReal 0)=Complex.I • M.firstJet (Complexification.ofReal X)
    simp only [map_zero,h1,smul_zero]

theorem half_real_kernel {X : G} (hX : ⁅M.euler,X⁆=(1/2 : ℝ) • X)
    (hTX : ⁅M.translation,X⁆=0) : X=0 := by
  let Z := Complexification.ofReal X
  have hZ : ⁅M.E,Z⁆=(1/2 : ℂ) • Z := by simpa [Z] using M.ofReal_eigen hX
  have hcZ : M.center Z=Z := M.center_of_commutes (by rw [←Complexification.ofReal_lie,hTX,map_zero])
  have hz0 : M.field Z M.point=0 := by
    simpa only [hcZ] using M.centered_value_zero hZ (Or.inr (Or.inl rfl))
  have hcB : M.center ⁅M.H,Z⁆=⁅M.H,Z⁆ := by rw [M.center.map_lie,M.center_rotation,hcZ]
  have hb0 : M.field ⁅M.H,Z⁆ M.point=0 := by
    simpa only [hcB,hcZ,hz0,map_zero,neg_zero] using M.centered_rotation_value Z
  have hb1 : M.firstJet ⁅M.H,Z⁆= -Complex.I • M.firstJet Z := by
    simpa only [hcB,hcZ] using M.centered_half_rotation_firstJet hZ
  apply M.isotropy_real X (-⁅M.rotation,X⁆) hz0
  · rw [map_neg,Complexification.ofReal_lie,map_neg]
    change -M.field ⁅M.H,Z⁆ M.point=0
    rw [hb0,neg_zero]
  · change M.firstJet (Complexification.ofReal (-⁅M.rotation,X⁆))=Complex.I • M.firstJet Z
    rw [map_neg,Complexification.ofReal_lie,map_neg,hb1,neg_smul,neg_neg]

theorem half_kernel {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1/2 : ℂ) • X)
    (hTX : ⁅M.T,X⁆=0) : X=0 := by
  have hr : Complexification.realPart X=0 := M.half_real_kernel
    (Complexification.realPart_eigen M.euler (1/2) (by simpa using hX))
    (by simpa only [T,Complexification.realPart_lie_ofReal,map_zero] using congrArg Complexification.realPart hTX)
  have hi : Complexification.imagPart X=0 := M.half_real_kernel
    (Complexification.imagPart_eigen M.euler (1/2) (by simpa using hX))
    (by simpa only [T,Complexification.imagPart_lie_ofReal,map_zero] using congrArg Complexification.imagPart hTX)
  rw [Complexification.normalForm X,hr,hi,map_zero,smul_zero,add_zero]

theorem one_real_kernel {X : G} (hX : ⁅M.euler,X⁆=(1 : ℝ) • X)
    (hTX : ⁅M.translation,⁅M.translation,X⁆⁆=0) : X=0 := by
  let Z := Complexification.ofReal X
  let Y := ⁅M.translation,X⁆
  have hZ : ⁅M.E,Z⁆=(1 : ℂ) • Z := by simpa [Z] using M.ofReal_eigen hX
  have hTZ : ⁅M.T,Z⁆=Complexification.ofReal Y := (Complexification.ofReal_lie _ _).symm
  have hTTZ : ⁅M.T,⁅M.T,Z⁆⁆=0 := by rw [hTZ,←Complexification.ofReal_lie,hTX,map_zero]
  have hcZ : M.center Z=Z-Complex.I • Complexification.ofReal Y := by
    rw [center,LieAlgebra.innerExp_apply_of_square_zero _ _ _ _ hTTZ,hTZ]
    simp [sub_eq_add_neg]
  have hcY : M.center (Complexification.ofReal Y)=Complexification.ofReal Y :=
    M.center_of_commutes (by rw [←Complexification.ofReal_lie,hTX,map_zero])
  have hY : ⁅M.E,Complexification.ofReal Y⁆=(0 : ℂ) • Complexification.ofReal Y := by
    simpa only [hTZ,sub_self] using M.bracket_translation_eigen hZ
  have hy0 : M.field (Complexification.ofReal Y) M.point=0 := by
    simpa only [hcY] using M.centered_value_zero hY (Or.inl rfl)
  have hz0 : M.field Z M.point=0 := by
    have hh := M.centered_value_zero hZ (Or.inr (Or.inr rfl))
    simpa only [hcZ,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,hy0,smul_zero,sub_zero] using hh
  have hz1 : M.firstJet Z=Complex.I • M.firstJet (Complexification.ofReal Y) := by
    have hh := M.centered_firstJet_one_zero hZ
    rw [hcZ,map_sub,map_smul] at hh
    exact sub_eq_zero.mp hh
  have hy : Y=0 := M.isotropy_real Y X hy0 hz0 hz1
  apply M.real_zero_of_zero_jet X hz0
  rw [hz1,hy,map_zero,map_zero,smul_zero]

theorem one_kernel {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1 : ℂ) • X)
    (hTX : ⁅M.T,⁅M.T,X⁆⁆=0) : X=0 := by
  have hr : Complexification.realPart X=0 := M.one_real_kernel
    (Complexification.realPart_eigen M.euler 1 (by simpa using hX))
    (by simpa only [T,Complexification.realPart_lie_ofReal,map_zero] using congrArg Complexification.realPart hTX)
  have hi : Complexification.imagPart X=0 := M.one_real_kernel
    (Complexification.imagPart_eigen M.euler 1 (by simpa using hX))
    (by simpa only [T,Complexification.imagPart_lie_ofReal,map_zero] using congrArg Complexification.imagPart hTX)
  rw [Complexification.normalForm X,hr,hi,map_zero,smul_zero,add_zero]

end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RatLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
namespace Module.End
open scoped _root_.Module _root_.Module.End
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

 theorem trace_eq_sum_eigenspace_finrank (A : Module.End ℂ V) (hA : A.IsSemisimple)
    (s : Finset ℂ) (hs : ∀ μ, A.HasEigenvalue μ → μ∈s) :
    LinearMap.trace ℂ V A=∑ μ∈s, μ*(Module.finrank ℂ (A.eigenspace μ) : ℂ) := by
  classical
  let N : s → Submodule ℂ V := fun μ => A.eigenspace μ.val
  have hi : iSupIndep N := (_root_.Module.End.eigenspaces_iSupIndep A).comp Subtype.val_injective
  have htop : iSup N=⊤ := by
    rw [←hA.iSup_eigenspace_eq_top]
    apply le_antisymm
    · exact iSup_le fun μ => le_iSup (A.eigenspace) μ.val
    · apply iSup_le
      intro μ
      by_cases hm : μ∈s
      · exact le_iSup N ⟨μ,hm⟩
      · have hz : A.eigenspace μ=⊥ := by
          by_contra hn
          exact hm (hs μ hn)
        simp [hz]
  have hint : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mpr ⟨hi,htop⟩
  have hmaps (μ : s) : Set.MapsTo A (N μ) (N μ) := by
    intro x hx
    change x∈A.eigenspace μ.val at hx
    change A x∈A.eigenspace μ.val
    rw [_root_.Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hx,map_smul,hx]
  rw [←Finset.sum_coe_sort,LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  apply Finset.sum_congr rfl
  intro μ _
  have he : A.restrict (hmaps μ)=μ.val • (LinearMap.id : N μ →ₗ[ℂ] N μ) := by
    ext x
    exact _root_.Module.End.mem_eigenspace_iff.mp x.property
  rw [he,map_smul,LinearMap.trace_id,smul_eq_mul]

 theorem five_weight_trace_balance (A : Module.End ℂ V) (hA : A.IsSemisimple)
    (hs : ∀ μ, A.HasEigenvalue μ → μ∈({-1,-(1/2),0,1/2,1} : Finset ℂ))
    (hz : LinearMap.trace ℂ V A=0)
    (hhalf : Module.finrank ℂ (A.eigenspace (1/2)) ≤ Module.finrank ℂ (A.eigenspace (-(1/2))))
    (hone : Module.finrank ℂ (A.eigenspace 1) ≤ Module.finrank ℂ (A.eigenspace (-1))) :
    Module.finrank ℂ (A.eigenspace (1/2)) = Module.finrank ℂ (A.eigenspace (-(1/2))) ∧
    Module.finrank ℂ (A.eigenspace 1) = Module.finrank ℂ (A.eigenspace (-1)) := by
  have he := trace_eq_sum_eigenspace_finrank A hA _ hs
  rw [hz] at he
  have hr := congrArg Complex.re he
  norm_num [Finset.sum_insert,Complex.mul_re,Complex.div_re] at hr
  have hh : (Module.finrank ℂ (A.eigenspace (1/2)) : ℝ) ≤ Module.finrank ℂ (A.eigenspace (-(1/2))) := by exact_mod_cast hhalf
  have ho : (Module.finrank ℂ (A.eigenspace 1) : ℝ) ≤ Module.finrank ℂ (A.eigenspace (-1)) := by exact_mod_cast hone
  constructor
  · have heq : (Module.finrank ℂ (A.eigenspace (1/2)) : ℝ)=Module.finrank ℂ (A.eigenspace (-(1/2))) := by linarith
    exact_mod_cast heq
  · have heq : (Module.finrank ℂ (A.eigenspace 1) : ℝ)=Module.finrank ℂ (A.eigenspace (-1)) := by linarith
    exact_mod_cast heq
end Module.End

open Filter Topology
open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PositiveReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

theorem lowerHalf_injective : Function.Injective M.lowerHalf := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  apply Subtype.ext
  exact M.half_kernel (Module.End.mem_eigenspace_iff.mp X.property) (congrArg Subtype.val hX)

theorem lowerOneSquared_injective : Function.Injective M.lowerOneSquared := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  apply Subtype.ext
  exact M.one_kernel (Module.End.mem_eigenspace_iff.mp X.property) (congrArg Subtype.val hX)

variable [FiniteDimensional ℝ G]

theorem complex_euler_trace_zero (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    LinearMap.trace ℂ (ℂ ⊗[ℝ] G) (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E)=0 := by
  rw [Complexification.ad_ofReal_baseChange,LinearMap.trace_baseChange,htrace,map_zero]

theorem grading_balance (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    Module.finrank ℂ (M.grade (1/2))=Module.finrank ℂ (M.grade (-(1/2))) ∧
    Module.finrank ℂ (M.grade 1)=Module.finrank ℂ (M.grade (-1)) := by
  apply Module.End.five_weight_trace_balance _ M.euler_semisimple M.euler_spectrum
    (M.complex_euler_trace_zero htrace)
  · exact LinearMap.finrank_le_finrank_of_injective M.lowerHalf_injective
  · exact LinearMap.finrank_le_finrank_of_injective M.lowerOneSquared_injective

theorem lowerOneSquared_surjective (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    Function.Surjective M.lowerOneSquared :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (M.grading_balance htrace).2).mp
    M.lowerOneSquared_injective

theorem exists_positive_real_oai (htrace : LinearMap.trace ℝ G (LieAlgebra.ad ℝ G M.euler)=0) :
    ∃ V : G, ⁅M.euler,V⁆=V ∧ ⁅M.translation,⁅M.translation,V⁆⁆=(-2 : ℝ) • M.translation := by
  have ht : (-2 : ℂ) • M.T∈M.grade (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    change ⁅M.E,(-2 : ℂ) • M.T⁆= -1 • ((-2 : ℂ) • M.T)
    rw [LieAlgebra.lie_smul (-2 : ℂ) M.E M.T,←lie_skew M.E M.T,M.translation_euler]
    module
  obtain ⟨V,hV⟩ := M.lowerOneSquared_surjective htrace ⟨_,ht⟩
  refine ⟨Complexification.realPart V.val,?_,?_⟩
  · have he := Complexification.realPart_eigen M.euler 1
      (by simpa using (Module.End.mem_eigenspace_iff.mp V.property))
    simpa using he
  · have he : ⁅M.T,⁅M.T,V.val⁆⁆=(-2 : ℂ) • M.T := congrArg Subtype.val hV
    have hr := congrArg Complexification.realPart he
    rw [show (-2 : ℂ)=((-2 : ℝ) : ℂ) by norm_num] at hr
    simpa only [T,Complexification.realPart_lie_ofReal,Complexification.realPart_real_smul,
      Complexification.realPart_ofReal] using hr
end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.Biholomorph.WeightedLieModel.exists_positive_real_oai.{u_1} := @OAI.Release061.Biholomorph.WeightedLieModel.exists_positive_real_oai.{u_1}
