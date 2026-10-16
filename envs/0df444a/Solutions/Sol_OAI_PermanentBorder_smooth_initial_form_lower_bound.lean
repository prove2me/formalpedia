-- Prove2me | solution 1 for OAI.PermanentBorder.smooth_initial_form_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:48:40.678536+00:00
-- url     : https://prove2.me/submissions/48ce01d6-1057-4068-bdb5-b60b315384fe

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/InitialForm.lean:L128-L158
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PermanentBorder.smooth_initial_form_lower_bound.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_PermanentBorder_smooth_initial_form_lower_bound) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
import Definitions.Def_OAI_Algebra_Determinantal_InitialForm
import Theorems.Thm_OAI_PermanentBorder_CI_hasFDerivAt_eval
import Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_lowest_homogeneousComponent
import Theorems.Thm_OAI_PermanentBorder_KernelBilinear_affine_polar_count
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_finite_simple_zeros_persist
import Theorems.Thm_OAI_PermanentBorder_Polar_smooth_polar_affine_certificate
import Theorems.Thm_OAI_PermanentBorder_degree_affineMatrixPolynomial
import Theorems.Thm_OAI_PermanentBorder_support_subset_cube_of_limit

-- ---- from OAI.Algebra.Determinantal.PointBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

end ProductComparison
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section BlockInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable (group : σ → ι) (base : ι → σ) (hbase : ∀ j, group (base j) = j)

variable [Fintype L] [DecidableEq L]

end BlockInterpolation
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section NormalizedPointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end NormalizedPointBound
end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
theorem fderiv_slice {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) (c : C) (x : V) :
    fderiv ℂ (fun x => F (c,x)) x =
      fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V := by
  have hi : HasFDerivAt (fun x : V => (c,x)) (ContinuousLinearMap.inr ℂ C V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) c x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (c,x)).hasFDerivAt.comp x hi).fderiv

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
theorem contDiff_mvPolynomial_eval (p : MvPolynomial τ ℂ) :
    ContDiff ℂ 1 (fun x : τ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : τ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section ProductSimplePointBound
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end ProductSimplePointBound
end PermanentBorder.Multigraded

end OAI

-- ---- from OAI.Algebra.Determinantal.RankTransfer ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma affineNormChart_eq
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) (j : Option ι) :
    affineNormChart e z j = e.symm (Pi.single none 1) j +
      ∑ i, e.symm (Pi.single (some i) 1) j * z i := by
  classical
  have hd : Option.elim' 1 z = Pi.single none 1 + ∑ i, z i • Pi.single (some i) 1 := by
    funext j
    cases j <;> simp [Pi.single_apply]
  rw [affineNormChart, hd, map_add, map_sum]
  simp [Finset.sum_apply, mul_comm]

end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.Model ----
namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

theorem HasExactDeterminant.hasBorderDeterminant {σ : Type*} [Fintype σ]
    {n : ℕ} {p : Poly σ} (h : HasExactDeterminant n p) :
    HasBorderDeterminant n p := by
  rcases h with ⟨hn, A₀, A, hp⟩
  refine ⟨hn, (fun _ => A₀), (fun _ => A), ?_⟩
  intro d
  simpa only [hp] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.coeff d) atTop (𝓝 (p.coeff d)))

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

theorem support_subset_exponentCube {P : Poly σ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    P.support ⊆ exponentCube n := by
  intro d hd
  rw [mem_exponentCube]
  intro i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree P i).trans hP)

theorem sum_over_exponentCube {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) :
    P = ∑ d ∈ exponentCube n, monomial d (P.coeff d) := by
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := MvPolynomial.as_sum P
    _ = _ := ?_
  apply Finset.sum_subset hP
  intro d _ hd
  simp only [notMem_support_iff.mp hd, map_zero]

theorem coeff_linear_map_cube (F : Poly σ →ₗ[ℂ] Poly τ) {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) (e : τ →₀ ℕ) :
    (F P).coeff e = ∑ d ∈ exponentCube n,
      P.coeff d * (F (monomial d 1)).coeff e := by
  conv_lhs => rw [sum_over_exponentCube hP]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by simp [smul_monomial],
    map_smul, coeff_smul, smul_eq_mul]

theorem coefficientwise_linear_map_limit (F : Poly σ →ₗ[ℂ] Poly τ)
    {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    ∀ e, Tendsto (fun j => (F (P j)).coeff e) atTop (𝓝 ((F p).coeff e)) := by
  intro e
  have hc := support_subset_cube_of_limit hP hp
  have ht := tendsto_finsetSum (exponentCube (σ := σ) n)
    (fun d _ => (hp d).mul (tendsto_const_nhds (x := (F (monomial d 1)).coeff e)))
  convert ht using 1
  · funext j
    exact coeff_linear_map_cube F (hP j) e
  · congr 1
    exact coeff_linear_map_cube F hc e
end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem affineSubstitution_matrix (b : σ → ℂ) (B : σ → τ → ℂ)
    (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineSubstitution b B (affineMatrixPolynomial n A₀ A) =
      affineMatrixPolynomial n
        (fun i j => A₀ i j + ∑ v : σ, A v i j * b v)
        (fun w i j => ∑ v : σ, A v i j * B v w) := by
  classical
  unfold affineMatrixPolynomial
  have he := RingHom.map_det (affineSubstitution b B).toRingHom
    (show Matrix (Fin n) (Fin n) (Poly σ) from
      fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  refine he.trans ?_
  apply congrArg Matrix.det
  funext i j
  change (affineSubstitution b B) (C (A₀ i j) + ∑ v, C (A v i j) * X v) =
    C (A₀ i j + ∑ v, A v i j * b v) + ∑ w, C (∑ v, A v i j * B v w) * X w
  simp only [affineSubstitution, map_add, map_sum, map_mul,
    aeval_C, aeval_X, algebraMap_eq]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← map_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, map_mul, mul_assoc]

theorem HasBorderDeterminant.affineSubstitution {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) :
    HasBorderDeterminant n (affineSubstitution b B p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  refine ⟨hn,
    (fun l i j => A₀ l i j + ∑ v : σ, A l v i j * b v),
    (fun l w i j => ∑ v : σ, A l v i j * B v w), ?_⟩
  have hf := coefficientwise_linear_map_limit (PermanentBorder.affineSubstitution b B).toLinearMap
    (fun l => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ l) (A l))) hlim
  intro e
  simpa only [AlgHom.toLinearMap_apply, affineSubstitution_matrix] using hf e
end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

end ScalarNormalization
end PermanentBorder

end OAI

-- ---- from OAI.Algebra.Determinantal.BorderPolars ----
namespace OAI

namespace PermanentBorder.PolarAnalysis
open MvPolynomial Filter
open scoped Topology

section PolynomialSystem
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem contDiff_coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ) :
    ContDiff ℂ 1 (coefficientSystem n L) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro d _
  exact ((contDiff_apply ℂ ℂ d).comp contDiff_fst).mul
    ((contDiff_mvPolynomial_eval _).comp contDiff_snd)

omit [Fintype τ] in
theorem coefficientSystem_eq {n : ℕ} (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    {P : Poly σ} (hP : P.support ⊆ exponentCube n) (x : τ → ℂ) :
    coefficientSystem n L ((fun d => P.coeff d.val),x) = polynomialSystem L P x := by
  classical
  ext i
  change (∑ d : exponentCube n, P.coeff d.val * eval x (L i (monomial d.val 1))) = _
  change _ = eval x (L i P)
  conv_rhs => rw [sum_over_exponentCube hP]
  simp only [map_sum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d.val (P.coeff d.val) = P.coeff d.val • monomial d.val (1 : ℂ) by
    simp [smul_monomial], map_smul]
  simp

theorem coefficient_limit_simple_zeros {ι : Type*} [Fintype ι]
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d)))
    (x : ι → τ → ℂ) (hx : Function.Injective x)
    (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∀ᶠ j in atTop, ∃ y : ι → τ → ℂ, Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (P j) (y i) := by
  classical
  let c : exponentCube (σ := σ) n → ℂ := fun d => p.coeff d.val
  let cs : ℕ → exponentCube (σ := σ) n → ℂ := fun j d => (P j).coeff d.val
  have hc : Tendsto cs atTop (𝓝 c) := tendsto_pi_nhds.mpr fun d => hp d.val
  let F := coefficientSystem n L
  have hF : ContDiff ℂ 1 F := contDiff_coefficientSystem n L
  have hp' := support_subset_cube_of_limit hP hp
  have he : (fun x => F (c,x)) = polynomialSystem L p := by
    funext x
    exact coefficientSystem_eq L hp' x
  have hz : ∀ i, F (c,x i) = 0 := by
    intro i
    rw [congrFun he]
    exact (hs i).1
  have hs' : ∀ i, SimpleAt F c (x i) := by
    intro i
    unfold SimpleAt
    rw [← fderiv_slice hF, he]
    exact (hs i).2
  have ht := finite_simple_zeros_persist hF x hx hz hs'
  filter_upwards [hc.eventually ht] with j hj
  obtain ⟨y,hy,hys⟩ := hj
  refine ⟨y,hy,?_⟩
  intro i
  have he' : (fun x => F (cs j,x)) = polynomialSystem L (P j) := by
    funext x
    exact coefficientSystem_eq L (hP j) x
  constructor
  · rw [← congrFun he']
    exact (hys i).1
  · rw [← he', fderiv_slice hF]
    exact (hys i).2

theorem HasBorderDeterminant.exists_simple_approximant {ι : Type*} [Fintype ι]
    {p : Poly σ} {n : ℕ} (h : HasBorderDeterminant n p)
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) (x : ι → τ → ℂ)
    (hx : Function.Injective x) (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ)
      (y : ι → τ → ℂ), Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (affineMatrixPolynomial n A₀ A) (y i) := by
  obtain ⟨hn,A₀,A,hlim⟩ := h
  obtain ⟨j,y,hy,hys⟩ := (coefficient_limit_simple_zeros L
    (fun j => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ j) (A j)))
    hlim x hx hs).exists
  exact ⟨A₀ j,A j,y,hy,hys⟩
end PolynomialSystem
end PermanentBorder.PolarAnalysis
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

lemma eval_affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (f : Poly (PolarVars τ)) (z : Option τ → ℂ) :
    eval z (affineChartSubstitution e f) = eval (affineNormChart e z) f := by
  change (aeval z : Poly (Option τ) →ₐ[ℂ] ℂ) (aeval _ f) = _
  rw [comp_aeval_apply]
  apply congrArg (fun g : PolarVars τ → ℂ => aeval g f)
  funext j
  simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  convert (affineNormChart_eq e z j).symm using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply congrArg (fun v : PolarVars τ → ℂ => e.symm v j)
  funext v
  simp [Pi.single_apply]

lemma polarOperator_eq (w : τ → PolarVars τ → ℂ) (i : τ) (f : Poly (PolarVars τ)) :
    polarOperator w i f = polarPolynomial w f i := by
  simp [polarOperator, polarPolynomial, smul_eq_C_mul]

lemma polynomialSystem_affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    PolarAnalysis.polynomialSystem (affinePolarOperators w e) f =
      fun z j => eval (affineNormChart e z) (hypersurfacePolars w f j) := by
  funext z j
  cases j with
  | none => exact eval_affineChartSubstitution e f z
  | some i =>
    change eval z (affineChartSubstitution e (polarOperator w i f)) = _
    rw [eval_affineChartSubstitution, polarOperator_eq]
    rfl

theorem HasBorderDeterminant.simple_polar_approximant {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : PolarVars τ → Matrix (Fin n) (Fin n) ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧ ∀ i,
        PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e)
          (affineMatrixPolynomial n A₀ A) (x i) := by
  obtain ⟨w,e,x,hx,hsx⟩ := smooth_polar_affine_certificate f hr hh hs
  have hp (i) : PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e) f (x i) := by
    unfold PolarAnalysis.SimplePolynomialZero
    rw [polynomialSystem_affinePolarOperators]
    exact hsx i
  obtain ⟨A₀,A,y,hy,hys⟩ := PolarAnalysis.HasBorderDeterminant.exists_simple_approximant
    hb (affinePolarOperators w e) x hx hp
  exact ⟨w,e,A₀,A,y,hy,hys⟩
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {τ : Type} [Fintype τ]

lemma derivative_polar (w : τ → PolarVars τ → ℂ) (f : Poly (PolarVars τ))
    (y : PolarVars τ → ℂ) (i : τ) :
    fderiv ℂ (fun y => eval y f) y (w i) = eval y (polarPolynomial w f i) := by
  rw [(CI.hasFDerivAt_eval f y).fderiv, CI.polynomialDerivative_apply]
  simp [polarPolynomial,mul_comm]

lemma polarPair_polynomialSystem (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    polarPair (fun y => eval y f) (fun z => affineNormChart e (optionProduct.symm z)) w =
      fun z => optionProduct (polynomialSystem (affinePolarOperators w e) f (optionProduct.symm z)) := by
  funext z
  rw [polynomialSystem_affinePolarOperators]
  apply Prod.ext
  · rfl
  · funext i
    exact derivative_polar w f _ i

omit [Fintype τ] in
lemma affineNormChart_add (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (z : Option τ → ℂ) :
    affineNormChart e z = e.symm (Pi.single none 1) +
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  change e.symm (Option.elim' 1 z) = e.symm (Pi.single none 1) + e.symm (optionInsert z)
  rw [← map_add]
  apply congrArg e.symm
  funext j
  cases j <;> simp

lemma eval_matrix {σ : Type} [Fintype σ] {n : ℕ}
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    eval y (affineMatrixPolynomial (n+1) A₀ A) = (affine A₀ A y).det := by
  classical
  let M : Matrix (Fin (n+1)) (Fin (n+1)) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  change eval y M.det = _
  calc
    eval y M.det = ((eval y).mapMatrix M).det := RingHom.map_det (eval y) M
    _ = (affine A₀ A y).det := by
      apply congrArg Matrix.det
      ext i j
      change eval y (M i j) = (affine A₀ A y) i j
      simp [M,affine,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]

lemma simple_conjugate {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (e : V ≃L[ℂ] W) {F : V → V} {x : V} (hF : DifferentiableAt ℂ F x)
    (hs : (fderiv ℂ F x).IsInvertible) :
    (fderiv ℂ (fun y => e (F (e.symm y))) (e x)).IsInvertible := by
  have hF' : HasFDerivAt F (fderiv ℂ F x) (e.symm (e x)) := by simpa using hF.hasFDerivAt
  have hd := e.hasFDerivAt.comp (e x)
    (hF'.comp (e x) e.symm.hasFDerivAt)
  change (fderiv ℂ (e ∘ F ∘ e.symm) (e x)).IsInvertible
  rw [hd.fderiv]
  exact (show e.toContinuousLinearMap.IsInvertible from ⟨e,rfl⟩).comp
    (hs.comp (show e.symm.toContinuousLinearMap.IsInvertible from ⟨e.symm,rfl⟩))

theorem HasBorderDeterminant.polar_count {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    r * (r-1)^Fintype.card τ ≤
      2^Fintype.card τ * (2*n-1).choose (Fintype.card τ+1) := by
  classical
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb.1)
  | succ n =>
    obtain ⟨w,e,A₀,A,x,hx,hxs⟩ := HasBorderDeterminant.simple_polar_approximant hb hr hh hs
    let P := affineMatrixPolynomial (n+1) A₀ A
    let Q := polynomialSystem (affinePolarOperators w e) P
    let b := e.symm (Pi.single none 1)
    let L := e.symm.toContinuousLinearMap.comp optionInsert
    have hrel : polarPair (fun y => (affine A₀ A y).det)
        (fun z => b + L (optionProduct.symm z)) w =
          fun z => optionProduct (Q (optionProduct.symm z)) := by
      have heval : (fun y => (affine A₀ A y).det) = (fun y => eval y P) := by
        funext y
        exact (eval_matrix A₀ A y).symm
      have hψ : (fun z => b + L (optionProduct.symm z)) =
          (fun z => affineNormChart e (optionProduct.symm z)) := by
        funext z
        exact (affineNormChart_add e _).symm
      rw [heval,hψ]
      exact polarPair_polynomialSystem w e P
    have hQ (z : Option τ → ℂ) : DifferentiableAt ℂ Q z := by
      apply differentiableAt_pi.mpr
      intro j
      exact ((contDiff_mvPolynomial_eval ((affinePolarOperators w e j) P)).differentiable (by decide)).differentiableAt
    have hcount := affine_polar_count A₀ A b L w (fun j => optionProduct (x j))
      (optionProduct.injective.comp hx)
      (fun j => by
        rw [hrel]
        change optionProduct (Q (optionProduct.symm (optionProduct (x j)))) = 0
        rw [optionProduct.symm_apply_apply]
        have hz : Q (x j) = 0 := (hxs j).1
        rw [hz, map_zero])
      (fun j => by
        rw [hrel]
        exact simple_conjugate optionProduct (hQ (x j)) (hxs j).2)
    have hn : 2*(n+1)-1 = 2*n+1 := by omega
    simpa [hn] using hcount
end PermanentBorder.Polar

namespace PermanentBorder.Polar

 theorem factorial_exp_lower (b : ℕ) : ((b : ℝ) / Real.exp 1)^b ≤ b.factorial := by
  rcases b with _ | b
  · simp
  have hb : (1:ℝ) ≤ b+1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hπ : (1:ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (b+1)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  have hn := Stirling.le_factorial_stirling (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at hn ⊢
  exact le_trans (le_mul_of_one_le_left (by positivity) hs) hn

 theorem choose_exp_bound (a b : ℕ) (hb : 0 < b) :
    (a.choose b : ℝ) ≤ (Real.exp 1 * a / b)^b := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hfact := factorial_exp_lower b
  have hx : (0:ℝ) < ((b:ℝ)/Real.exp 1)^b := by positivity
  calc
    (a.choose b : ℝ) ≤ (a:ℝ)^b / b.factorial := Nat.choose_le_pow_div b a
    _ ≤ (a:ℝ)^b / ((b:ℝ)/Real.exp 1)^b :=
      div_le_div_of_nonneg_left (by positivity) hx hfact
    _ = (Real.exp 1 * a / b)^b := by rw [← div_pow]; congr 1; field_simp

 theorem smooth_count_numerical_bound (n K r : ℕ) (hn : 0 < n) (hr : 2 ≤ r)
    (hcount : (r:ℝ) * ((r-1:ℕ):ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ)) :
    ((r-1:ℕ):ℝ) * (K+1) / (4 * Real.exp 1) ≤ n := by
  have hr0 : (0:ℝ) < (r-1:ℕ) := by exact_mod_cast (show 0 < r-1 by omega)
  have hrle : ((r-1:ℕ):ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hK : (0:ℝ) < K+1 := by positivity
  have hchoose := choose_exp_bound (2*n-1) (K+1) (by omega)
  have htwo : ((2*n-1:ℕ):ℝ) ≤ 2*n := by
    exact_mod_cast (Nat.sub_le (2*n) 1)
  have hbase : Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ) ≤
      (2 * Real.exp 1 * n) / (K+1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.exp_pos (1:ℝ)]
  have hpow : (((r-1:ℕ):ℝ))^(K+1) ≤ (4 * Real.exp 1 * n / (K+1))^(K+1) := by
    calc
      (((r-1:ℕ):ℝ))^(K+1) ≤ (r:ℝ) * ((r-1:ℕ):ℝ)^K := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right hrle (by positivity)
      _ ≤ 2^K * ((2*n-1).choose (K+1) : ℝ) := hcount
      _ ≤ 2^K * (Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ))^(K+1) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ ≤ 2^(K+1) * ((2 * Real.exp 1 * n) / (K+1))^(K+1) := by
        apply mul_le_mul
        · have : (2:ℝ)^K ≤ 2^(K+1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) K]
          exact this
        · exact pow_le_pow_left₀ (by positivity) hbase _
        · positivity
        · positivity
      _ = (4 * Real.exp 1 * n / (K+1))^(K+1) := by
        rw [← mul_pow]; congr 1; ring
  have hle : ((r-1:ℕ):ℝ) ≤ 4 * Real.exp 1 * n / (K+1) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : K+1 ≠ 0)).mp hpow
  apply (div_le_iff₀ (by positivity)).mpr
  have := (le_div_iff₀ hK).mp hle
  nlinarith

end PermanentBorder.Polar

namespace PermanentBorder
open MvPolynomial
open scoped Classical

theorem HasBorderDeterminant.rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    {n : ℕ} {f : Poly σ} (h : HasBorderDeterminant n f) (e : σ → τ) :
    HasBorderDeterminant n (MvPolynomial.rename e f) := by
  classical
  let B : σ → τ → ℂ := fun i j => if e i = j then 1 else 0
  have he : PermanentBorder.affineSubstitution (fun _ : σ => 0) B = (MvPolynomial.rename e : Poly σ →ₐ[ℂ] Poly τ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PermanentBorder.affineSubstitution,B,eq_comm]
  simpa only [he] using h.affineSubstitution (fun _ => 0) B

namespace Polar

lemma smooth_rename {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (f : Poly σ)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∀ y : τ → ℂ, eval y (rename e f) = 0 →
      (∀ j, eval y (pderiv j (rename e f)) = 0) → y = 0 := by
  intro y hy hg
  rw [eval_rename] at hy
  have hgrad (i : σ) : eval (y ∘ e) (pderiv i f) = 0 := by
    have h := hg (e i)
    rw [pderiv_rename e.injective,eval_rename] at h
    exact h
  have hz := hs _ hy hgrad
  funext i
  simpa only [Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun hz (e.symm i)

theorem HasBorderDeterminant.smooth_lower_bound {σ : Type} [Fintype σ]
    {n r : ℕ} {f : Poly σ} (hb : HasBorderDeterminant n f)
    (hσ : 2 ≤ Fintype.card σ) (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ((r-1 : ℕ) : ℝ) * ((Fintype.card σ-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ n := by
  classical
  let K := Fintype.card σ - 2
  have hc : Fintype.card σ = Fintype.card (PolarVars (Fin K)) := by
    simp only [PolarVars,Fintype.card_option,Fintype.card_fin]
    dsimp [K]
    omega
  let e := Fintype.equivOfCardEq hc
  have hb' := hb.rename e
  have hp := HasBorderDeterminant.polar_count hb' hr (hh.rename_isHomogeneous)
    (smooth_rename e f hs)
  have hcount : (r : ℝ) * ((r-1 : ℕ) : ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ) := by
    simp only [Fintype.card_fin] at hp
    exact_mod_cast hp
  have h := smooth_count_numerical_bound n K r hb.1 hr hcount
  have hk : K+1 = Fintype.card σ-1 := by dsimp [K]; omega
  have hkR : (K : ℝ)+1 = ((Fintype.card σ-1 : ℕ) : ℝ) := by exact_mod_cast hk
  simpa only [hkR] using h
end Polar
end PermanentBorder

end OAI

-- ---- from OAI.Algebra.Determinantal.InitialForm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

namespace InitialHomogeneous
variable {σ : Type*} [Fintype σ]

end InitialHomogeneous

/-- A smooth lowest homogeneous term after translation bounds both border and exact
determinant sizes by the product of its degree minus one and dimension minus one,
divided by `4 * Real.exp 1`. -/
theorem smooth_initial_form_lower_bound (d r : ℕ) (g : Poly (Fin d))
    (a : Fin d → ℂ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (_hG : homogeneousComponent r
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) ≠ 0)
    (hlow : ∀ j < r, homogeneousComponent j
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) = 0)
    (hs : ∀ y : Fin d → ℂ,
      eval y (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g)) = 0 →
      (∀ i, eval y (pderiv i (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g))) = 0) →
      y = 0) :
    ∀ n : ℕ,
      (HasBorderDeterminant n g →
        ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ)) ∧
      (HasExactDeterminant n g →
        ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ)) := by
  intro n
  have hb : HasBorderDeterminant n g →
      ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ) := by
    intro h
    have hq := h.affineSubstitution a
      (fun i j : Fin d => if i = j then (1 : ℂ) else 0)
    have hinit := hq.lowest_homogeneousComponent hlow
    simpa only [Fintype.card_fin] using Polar.HasBorderDeterminant.smooth_lower_bound hinit
      (by simpa only [Fintype.card_fin] using hd) hr
      (homogeneousComponent_isHomogeneous r _) hs
  exact ⟨hb, fun h => hb h.hasBorderDeterminant⟩

end PermanentBorder

end OAI

-- ---- mission target ----
open OAI OAI.PermanentBorder
open MvPolynomial
open Filter
open scoped Topology
open MvPolynomial Filter

namespace OAI
namespace PermanentBorder
theorem _root_.solution (d r : ℕ) (g : Poly (Fin d))
    (a : Fin d → ℂ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hG : homogeneousComponent r
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) ≠ 0)
    (hlow : ∀ j < r, homogeneousComponent j
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) = 0)
    (hs : ∀ y : Fin d → ℂ,
      eval y (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g)) = 0 →
      (∀ i, eval y (pderiv i (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g))) = 0) →
      y = 0) :
    ∀ n : ℕ,
      (HasBorderDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) ∧
      (HasExactDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) := by
  first
    | exact OAI.PermanentBorder.smooth_initial_form_lower_bound d r g a hd hr hG hlow hs
    | exact OAI.PermanentBorder.smooth_initial_form_lower_bound
    | (apply OAI.PermanentBorder.smooth_initial_form_lower_bound <;> assumption)
    | (intros; apply OAI.PermanentBorder.smooth_initial_form_lower_bound <;> assumption)
end PermanentBorder
end OAI
