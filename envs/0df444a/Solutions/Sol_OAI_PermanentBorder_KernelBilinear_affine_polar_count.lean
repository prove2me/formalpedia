-- Prove2me | solution 1 for OAI.PermanentBorder.KernelBilinear.affine_polar_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:54:03.829383+00:00
-- url     : https://prove2.me/submissions/5c84c260-5183-4583-b60f-0b36c8681964

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/BilinearCounts.lean:L333-L384
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.KernelBilinear.affine_polar_count. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_PermanentBorder_KernelBilinear_mixed_coefficient_bound
import Theorems.Thm_OAI_PermanentBorder_KernelBilinear_system_eq_matrixKernelSystem
import Theorems.Thm_OAI_PermanentBorder_Multigraded_bilinear_simple_point_count_reindex
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_differentiableAt_auxiliary
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_differential_scalar
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_simple_after_elimination
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_simple_polarPair_unit

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

lemma linearMatrix_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    (linearMatrix A₀ A i j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single none 1) := by
  apply IsWeightedHomogeneous.add
  · exact (isWeightedHomogeneous_X ℂ _ _).C_mul _
  · exact IsWeightedHomogeneous.sum _ _ _ (fun k _ => (isWeightedHomogeneous_X ℂ _ _).C_mul _)

lemma right_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i : Fin (n+1)) :
    (rightEquation A₀ A i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some false) 1) := by
  unfold rightEquation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n))

lemma left_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (j : Fin (n+1)) :
    (leftEquation A₀ A j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some true) 1) := by
  unfold leftEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

omit [Fintype κ] in
lemma polar_homogeneous (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (polarEquation (κ := κ) B).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (some false : Groups) 1 + Pi.single (some true) 1) := by
  unfold polarEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  apply IsWeightedHomogeneous.sum
  intro j _
  exact ((isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n)).C_mul (B i j)).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

lemma system_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1))
    (i : Equations κ n) :
    (system A₀ A B pivot i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (firstGroup i) 1 + Pi.single (secondGroup i) 1) := by
  rcases i with i | j | k
  · exact right_homogeneous A₀ A i
  · exact left_homogeneous A₀ A (pivot.succAbove j)
  · exact polar_homogeneous (B k)

lemma card_equations : Fintype.card (Equations κ n) = ∑ j, dimensions κ n j := by
  simp [Equations, Fintype.sum_option]
  omega

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem det_block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (block a β γ E).det = E.det * scalar a β γ E := by
  let := E.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hE)
  rw [block, det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp only [Matrix.sub_apply, Matrix.mul_apply, scalar]
  simp only [invOf_eq_nonsing_inv, Matrix.of_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_det {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (fun y => (E y).det) x := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem differentiableAt_adjugate {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply differentiableAt_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem differentiableAt_inverse {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((differentiableAt_det hE).inv hx).mul (differentiableAt_adjugate hE i j)
end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- from OAI.Algebra.Determinantal.SchurDifferentials ----
namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_right {γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => right (γ y) (E y) i) x := by
  simp only [right, Pi.neg_apply, mulVec, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (differentiableAt_inverse hE hx i j).mul (hγ j))).neg

 theorem differentiableAt_left {β : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => left (β y) (E y) i) x := by
  simp only [left, Pi.neg_apply, vecMul, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (hβ j).mul (differentiableAt_inverse hE hx j i))).neg

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem auxiliaryLinear_invertible (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (auxiliaryLinear E).IsInvertible := by
  have hu := isUnit_iff_ne_zero.mpr hE
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := auxiliaryLinear E⁻¹)
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
 theorem auxiliary_solved (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) (hx : (E x).det ≠ 0) :
    auxiliary β γ E (x,graphKernels β γ E x) = 0 := by
  have hu := isUnit_iff_ne_zero.mpr hx
  apply Prod.ext <;> simp [auxiliary, graphKernels, right, left, mulVec_neg, neg_vecMul,
    mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv (E x) hu, nonsing_inv_mul (E x) hu]

 theorem differentiableAt_graphKernels {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) : DifferentiableAt ℂ (graphKernels β γ E) x := by
  apply DifferentiableAt.prodMk
  · exact differentiableAt_pi.mpr (differentiableAt_right hγ hE hx)
  · exact differentiableAt_pi.mpr (differentiableAt_left hβ hE hx)

omit [DecidableEq ι] in
 theorem fderiv_auxiliary_inr {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    fderiv ℂ (auxiliary β γ E) (x,w) ∘L ContinuousLinearMap.inr ℂ V _ =
      auxiliaryLinear (E x) := by
  have hd := (differentiableAt_auxiliary (w := w) hβ hγ hE).hasFDerivAt.comp w
    ((hasFDerivAt_const x w).prodMk (hasFDerivAt_id w))
  have hf : HasFDerivAt (fun v => auxiliary β γ E (x,v)) (auxiliaryLinear (E x)) w := by
    convert! (auxiliaryLinear (E x)).hasFDerivAt.const_add (γ x,β x) using 1
  convert! hd.unique hf using 1

 theorem simple_kernel_elimination [FiniteDimensional ℂ V]
    {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    {R : V × ((ι → ℂ) × (ι → ℂ)) → V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0)
    (hR : DifferentiableAt ℂ R (x,graphKernels β γ E x))
    (hs : (fderiv ℂ (fun y => R (y,graphKernels β γ E y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,auxiliary β γ E z))
      (x,graphKernels β γ E x)).IsInvertible := by
  apply PermanentBorder.PolarAnalysis.simple_after_elimination hR
    (differentiableAt_auxiliary hβ hγ hE) (differentiableAt_graphKernels hβ hγ hE hx)
  · have he := (differentiableAt_det hE).continuousAt.eventually_ne hx
    filter_upwards [he] with y hy
    exact auxiliary_solved β γ E y hy
  · rw [fderiv_auxiliary_inr hβ hγ hE]
    exact auxiliaryLinear_invertible _ hx
  · exact hs
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem contDiff_det {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) :
    ContDiff ℂ n (fun y => (E y).det) := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem contDiff_adjugate {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : ι) :
    ContDiff ℂ n (fun y => (E y).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem contDiffAt_inverse {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) (i j : ι) :
    ContDiffAt ℂ n (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_det hE).contDiffAt.inv hx).mul (contDiff_adjugate hE i j).contDiffAt

 theorem contDiffAt_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) :
    ContDiffAt ℂ n (fun y => scalar (a y) (β y) (γ y) (E y)) x := by
  simp only [scalar, mulVec, dotProduct]
  exact ha.contDiffAt.sub (ContDiffAt.sum (fun j _ => (hβ j).contDiffAt.mul
    (ContDiffAt.sum (fun l _ => (contDiffAt_inverse hE hx j l).mul (hγ l).contDiffAt))))
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

 theorem differentiableAt_polarPair {F : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hF : ContDiffAt ℂ 2 F (ψ x)) (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (polarPair F ψ h) x := by
  apply DifferentiableAt.prodMk
  · exact (hF.differentiableAt (by norm_num)).comp x hψ
  · apply differentiableAt_pi.mpr
    intro i
    have hd : DifferentiableAt ℂ (fderiv ℂ F) (ψ x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h i))).comp x hψ

end PermanentBorder.PolarAnalysis

end OAI

-- ---- from OAI.Algebra.Determinantal.SchurLifts ----
namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

omit [Fintype κ] in
 theorem kernelRemaining_solved
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : DifferentiableAt ℂ a (ψ x))
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) (ψ x))
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) (ψ x))
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) (ψ x))
    (hx : (E (ψ x)).det ≠ 0) :
    kernelRemaining a β γ E ψ h
        (x, graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ) x) =
      polarPair (fun y => scalar (a y) (β y) (γ y) (E y)) ψ h x := by
  apply Prod.ext
  · simp [kernelRemaining, graphKernels, polarPair, scalar, right,
      dotProduct_neg, sub_eq_add_neg]
  · ext i
    exact (differential_scalar ha hβ hγ hE hx (h i)).symm

omit [Fintype ι] [DecidableEq ι] in
 theorem contDiff_block {a : T → ℂ} {β γ : T → ι → ℂ}
    {E : T → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : Unit ⊕ ι) :
    ContDiff ℂ n (fun y => block (a y) (β y) (γ y) (E y) i j) := by
  cases i <;> cases j <;> simp only [block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
  · exact ha
  · exact hβ _
  · exact hγ _
  · exact hE _ _

omit [DecidableEq ι] in
 theorem differentiableAt_kernelRemaining
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    {w : (ι → ℂ) × (ι → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (kernelRemaining a β γ E ψ h) (x,w) := by
  have hψ' : DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ψ z.1) (x,w) :=
    hψ.comp (x,w) (ContinuousLinearMap.fst ℂ (ℂ × (κ → ℂ)) ((ι → ℂ) × (ι → ℂ))).differentiableAt
  have hnorm (j : Unit ⊕ ι) (b : Bool) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => normalized (if b then z.2.1 else z.2.2) j) (x,w) := by
    cases j <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, normalized, Sum.elim_inl,
      Sum.elim_inr] <;> fun_prop
  have hdir (i j : Unit ⊕ ι) (l : κ) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) =>
        dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j) (x,w) := by
    have hc := (contDiff_block ha hβ hγ hE i j).contDiffAt (x := ψ x)
    have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h l))).comp (x,w) hψ'
  apply DifferentiableAt.prodMk
  · change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => a (ψ z.1) + ∑ j, β (ψ z.1) j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((ha.differentiable (by norm_num) _).comp (x,w) hψ')
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul (((hβ j).differentiable (by norm_num) _).comp (x,w) hψ')
    fun_prop
  · apply differentiableAt_pi.mpr
    intro l
    change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ∑ i, normalized z.2.2 i *
      ∑ j, dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j *
        normalized z.2.1 j) (x,w)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul (hnorm i false)
    apply DifferentiableAt.fun_sum
    intro j _
    exact (hdir i j l).mul (hnorm j true)

 theorem simple_kernel_lift
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) (hx : (E (ψ x)).det ≠ 0)
    (hz : polarPair (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair
      (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h) x).IsInvertible) :
    let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    let R := kernelRemaining a β γ E ψ h
    let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    (R (x,g x),J (x,g x)) = 0 ∧
      (fderiv ℂ (fun z => (R z,J z)) (x,g x)).IsInvertible := by
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  let R := kernelRemaining a β γ E ψ h
  let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  have hdE : ∀ i j y, DifferentiableAt ℂ (fun z => E z i j) y :=
    fun i j => (hE i j).differentiable (by norm_num)
  have hdb : ∀ i y, DifferentiableAt ℂ (fun z => β z i) y :=
    fun i => (hβ i).differentiable (by norm_num)
  have hdg : ∀ i y, DifferentiableAt ℂ (fun z => γ z i) y :=
    fun i => (hγ i).differentiable (by norm_num)
  have hda := ha.differentiable (by norm_num)
  have hevent : ∀ᶠ y in 𝓝 (ψ x), (E y).det ≠ 0 :=
    (differentiableAt_det (fun i j => hdE i j (ψ x))).continuousAt.eventually_ne hx
  have hFS : (fun y => (block (a y) (β y) (γ y) (E y)).det) =ᶠ[𝓝 (ψ x)]
      (fun y => (E y).det * S y) := by
    filter_upwards [hevent] with y hy
    exact det_block _ _ _ _ hy
  obtain ⟨hSz,hSs⟩ := simple_polarPair_unit (contDiff_det hE).contDiffAt
    (contDiffAt_scalar ha hβ hγ hE hx) hψ hFS hx hz hsimple
  have hRG : (fun y => R (y,g y)) =ᶠ[𝓝 x] polarPair S ψ h := by
    filter_upwards [hψ.continuousAt.eventually hevent] with y hy
    exact kernelRemaining_solved (hda _) (fun i => hdb i _) (fun i => hdg i _)
      (fun i j => hdE i j _) hy
  change (R (x,g x),J (x,g x)) = 0 ∧ _
  constructor
  · apply Prod.ext
    · exact hRG.eq_of_nhds.trans hSz
    · exact auxiliary_solved _ _ _ _ hx
  · apply simple_kernel_elimination (β := β ∘ ψ) (γ := γ ∘ ψ) (E := E ∘ ψ)
      (fun i => (hdb i _).comp x hψ) (fun i => (hdg i _).comp x hψ)
      (fun i j => (hdE i j _).comp x hψ) hx
      (differentiableAt_kernelRemaining ha hβ hγ hE hψ)
    rwa [hRG.fderiv_eq]
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] in
 theorem block_entries (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) :
    block (M (.inl ()) (.inl ())) (fun j => M (.inl ()) (.inr j))
      (fun i => M (.inr i) (.inl ())) (fun i j => M (.inr i) (.inr j)) = M := by
  ext i j
  cases i <;> cases j <;> rfl

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

 theorem exists_common_functional (v : J → I → ℂ) (hv : ∀ j, v j ≠ 0) :
    ∃ f : I → ℂ, ∀ j, f ⬝ᵥ v j ≠ 0 := by
  classical
  let p (j : J) := LinearMap.ker (dotLinear (v j))
  have hp (j : J) : p j ≠ ⊤ := by
    intro h
    apply hv j
    funext i
    have hi : Pi.single i 1 ∈ p j := h ▸ Submodule.mem_top
    change (Pi.single i 1 : I → ℂ) ⬝ᵥ v j = 0 at hi
    simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hi
  obtain ⟨f,hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨f,hf⟩

 theorem det_updateRow_one (i : I) (f : I → ℂ) :
    ((1 : Matrix I I ℂ).updateRow i f).det = f i := by
  have hsum : (∑ k, f k • (1 : Matrix I I ℂ) k) = f := by
    ext j
    simp [Matrix.one_apply, Finset.sum_apply, Pi.smul_apply]
  simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
    (Matrix.det_updateRow_sum (1 : Matrix I I ℂ) i f)

 theorem exists_common_kernel_chart (i₀ : I) (A : J → Matrix I I ℂ)
    (hA : ∀ j, (A j).adjugate ≠ 0) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (A j * S).adjugate i₀ r ≠ 0 := by
  classical
  have hv : ∀ j, ∃ r, (fun i => (A j).adjugate i r) ≠ 0 := by
    intro j
    by_contra! hz
    exact hA j (by funext i r; exact congrFun (hz r) i)
  choose r hr using hv
  let v : Option J → I → ℂ
    | none => Pi.single i₀ 1
    | some j => fun i => (A j).adjugate i (r j)
  have hv' : ∀ j, v j ≠ 0 := by
    rintro (_|j)
    · intro h
      have := congrFun h i₀
      simp [v] at this
    · exact hr j
  obtain ⟨f,hf⟩ := exists_common_functional v hv'
  have hf₀ : f i₀ ≠ 0 := by
    simpa only [v, dotProduct_single, mul_one] using hf none
  let T : Matrix I I ℂ := (1 : Matrix I I ℂ).updateRow i₀ f
  have hT : T.det ≠ 0 := by simpa only [T, det_updateRow_one] using hf₀
  let S : Matrix I I ℂ := T⁻¹
  have hST : S * T = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT)
  have hS : S.det ≠ 0 := by
    have he := congrArg Matrix.det hST
    rw [Matrix.det_mul, Matrix.det_one] at he
    exact left_ne_zero_of_mul_eq_one he
  have hadj : S.adjugate = S.det • T := by
    calc
      S.adjugate = S.adjugate * (S*T) := by rw [hST, Matrix.mul_one]
      _ = (S.adjugate*S)*T := (Matrix.mul_assoc _ _ _).symm
      _ = S.det • T := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨S,hS,?_⟩
  intro j
  refine ⟨r j,?_⟩
  rw [Matrix.adjugate_mul_distrib, hadj, Matrix.smul_mul]
  change S.det * (T * (A j).adjugate) i₀ (r j) ≠ 0
  apply mul_ne_zero hS
  simpa only [Matrix.mul_apply, T, Matrix.updateRow_self, v, dotProduct] using hf (some j)
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem determinantDifferential (M H : I → I → ℂ) :
    fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M H =
      ∑ i, ∑ j, (Matrix.of M).adjugate j i * H i j := by
  have hd := (determinantMultilinear (I := I)).hasFDerivAt M
  have he : fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M =
      (determinantMultilinear (I := I)).linearDeriv M := hd.fderiv
  rw [he, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((Matrix.of M).updateRow i (H i)).det = _
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose]
  change (Matrix.of M).transpose.cramer (H i) i = _
  rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  rfl

 theorem differentiableAt_determinant (M : I → I → ℂ) :
    DifferentiableAt ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M :=
  ((determinantMultilinear (I := I)).hasFDerivAt M).differentiableAt

 theorem adjugate_ne_zero_of_differential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → I → I → ℂ} {x : E} (hA : DifferentiableAt ℂ A x)
    (hd : fderiv ℂ (fun y => (Matrix.of (A y)).det) x ≠ 0) :
    (Matrix.of (A x)).adjugate ≠ 0 := by
  intro hz
  apply hd
  change fderiv ℂ ((fun M : I → I → ℂ => (Matrix.of M).det) ∘ A) x = 0
  rw [fderiv_comp x (differentiableAt_determinant (A x)) hA]
  ext v
  simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply]
  rw [determinantDifferential, hz]
  simp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
open scoped Topology
variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem first_derivative_ne_zero_of_invertible
    {P : (ℂ × W) → (ℂ × W)} {x : ℂ × W}
    (hP : DifferentiableAt ℂ P x) (hs : (fderiv ℂ P x).IsInvertible) :
    fderiv ℂ (fun y => (P y).1) x ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hs.bijective.surjective (1,0)
  have hh := congrArg (fun L : (ℂ × W) →L[ℂ] ℂ => L v) hz
  rw [(hP.hasFDerivAt.fst).fderiv] at hh
  change (fderiv ℂ P x v).1 = 0 at hh
  rw [hv] at hh
  exact one_ne_zero hh

variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

 theorem selected_simple_common_kernel_chart
    (i₀ : I) (A : E → I → I → ℂ) (ψ : (ℂ × W) → E)
    (P : (ℂ × W) → (ℂ × W)) (x : J → (ℂ × W))
    (hA : ∀ j, DifferentiableAt ℂ A (ψ (x j)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hP : ∀ j, DifferentiableAt ℂ P (x j))
    (hfirst : ∀ y, (P y).1 = (Matrix.of (A (ψ y))).det)
    (hsimple : ∀ j, (fderiv ℂ P (x j)).IsInvertible) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (Matrix.of (A (ψ (x j))) * S).adjugate i₀ r ≠ 0 := by
  apply exists_common_kernel_chart
  intro j
  apply adjugate_ne_zero_of_differential ((hA j).comp (x j) (hψ j))
  have hn := first_derivative_ne_zero_of_invertible (hP j) (hsimple j)
  simpa only [Function.comp_apply, hfirst] using hn
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix

 theorem det_submatrix_two_equiv {I J R : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [CommRing R]
    (er ec : I ≃ J) (M : Matrix J J R) :
    (M.submatrix er ec).det = (Equiv.Perm.sign (ec.symm.trans er) : ℤ) * M.det := by
  exact Matrix.det_reindex er.symm ec.symm M

 theorem determinant_pivot_scalar {n : ℕ} (i r : Fin (n+1)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      (M.submatrix (pivotEquiv r) (pivotEquiv i)).det = c*M.det := by
  let c : ℂ := (Equiv.Perm.sign ((pivotEquiv i).symm.trans (pivotEquiv r)) : ℤ)
  refine ⟨c, ?_, fun M => det_submatrix_two_equiv _ _ _⟩
  exact Int.cast_ne_zero.mpr (Units.ne_zero _)

 theorem pivot_minor_ne_zero {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i r : Fin (n+1)) (h : M.adjugate i r ≠ 0) :
    ((M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr).det ≠ 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have he : (M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr =
      M.submatrix r.succAbove i.succAbove := by ext a b; rfl
  rw [he]
  exact (mul_ne_zero_iff.mp h).2
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

 theorem simple_matrix_kernel_lift
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (hψ : DifferentiableAt ℂ ψ x)
    (hx : ((F (ψ x)).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hz : polarPair (fun y => (F y).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) x).IsInvertible) :
    matrixKernelSystem F ψ h (matrixKernelPoint F ψ x) = 0 ∧
      (fderiv ℂ (matrixKernelSystem F ψ h) (matrixKernelPoint F ψ x)).IsInvertible := by
  apply simple_kernel_lift (hF _ _) (fun j => hF _ _) (fun i => hF _ _)
    (fun i j => hF _ _) hψ hx
  · simpa only [block_entries] using hz
  · simpa only [block_entries] using hsimple
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- from OAI.Algebra.Determinantal.BilinearCounts ----
namespace OAI

namespace PermanentBorder.PolarAnalysis
open Matrix Schur Filter
open scoped Topology
variable {κ J T : Type*} [Fintype κ] [Finite J]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

 theorem finite_simple_polar_kernel_lifts {n : ℕ}
    (i₀ : Fin (n+1)) (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T) (x : J → (ℂ × (κ → ℂ)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hz : ∀ j, polarPair (fun y => (F y).det) ψ h (x j) = 0)
    (hsimple : ∀ j, (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) (x j)).IsInvertible) :
    ∃ S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ, S.det ≠ 0 ∧ ∀ j, ∃ r : Fin (n+1),
      let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
      matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧
        (fderiv ℂ (matrixKernelSystem F' ψ h) (matrixKernelPoint F' ψ (x j))).IsInvertible := by
  have hFd : ∀ y, DifferentiableAt ℂ (fun y i j => F y i j) y := by
    intro y
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hF i j).differentiable (by norm_num) y
  obtain ⟨S,hS,hs⟩ := selected_simple_common_kernel_chart i₀ (fun y i j => F y i j)
    ψ (polarPair (fun y => (F y).det) ψ h) x (fun j => hFd _) hψ
    (fun j => differentiableAt_polarPair (contDiff_det hF).contDiffAt (hψ j))
    (fun _ => rfl) hsimple
  refine ⟨S,hS,?_⟩
  intro j
  obtain ⟨r,hr⟩ := hs j
  refine ⟨r,?_⟩
  let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
  change matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧ _
  have hF' : ∀ a b, ContDiff ℂ 2 (fun y => F' y a b) := by
    intro a b
    change ContDiff ℂ 2 (fun y => ∑ k, F y (pivotEquiv r a) k * S k (pivotEquiv i₀ b))
    apply ContDiff.sum
    intro k _
    exact (hF _ _).mul contDiff_const
  obtain ⟨c,hc,hcF⟩ := determinant_pivot_scalar i₀ r
  have hcs : c*S.det ≠ 0 := mul_ne_zero hc hS
  have hdet (y : T) : (F' y).det = (c*S.det)*(F y).det := by
    rw [hcF, Matrix.det_mul]
    ring
  have hrel : (fun y => (F y).det) =ᶠ[𝓝 (ψ (x j))]
      (fun y => (c*S.det)⁻¹ * (F' y).det) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hdet, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
  obtain ⟨hzero,hsimp⟩ := simple_polarPair_unit contDiffAt_const
    (contDiff_det hF').contDiffAt (hψ j) hrel (inv_ne_zero hcs) (hz j) (hsimple j)
  apply simple_matrix_kernel_lift F' hF' (hψ j)
    (pivot_minor_ne_zero (F (ψ (x j)) * S) i₀ r hr) hzero hsimp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
omit [Fintype κ] in
lemma base_group (i r : Fin (n+1)) (j : Groups) : (base (κ := κ) i r j).1 = j := by
  rcases j with _ | (_ | _) <;> rfl
lemma chart_base (i r : Fin (n+1)) (z : ChartSpace κ n) (j : Groups) :
    chart i r z (base i r j) = 1 := by
  rcases j with _ | (_ | _) <;> simp [chart, coordinates, base]
lemma contDiff_chart (i r : Fin (n+1)) : ContDiff ℂ 1 (chart (κ := κ) i r) := by
  apply contDiff_pi.mpr
  rintro ⟨j,t⟩
  rcases j with _ | (_ | _)
  · rcases t with _ | (_ | t) <;> simp [chart, coordinates] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.1 ((pivotEquiv i).symm t))
    cases (pivotEquiv i).symm t <;> simp [normalized] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.2 ((pivotEquiv r).symm t))
    cases (pivotEquiv r).symm t <;> simp [normalized] <;> fun_prop

lemma chart_separated {i r s : Fin (n+1)} {x y : ChartSpace κ n} (h : x.1 ≠ y.1) :
    Multigraded.BlockSeparated Sigma.fst (chart i r x) (chart i s y) := by
  have he : optionProduct.symm x.1 ≠ optionProduct.symm y.1 :=
    fun e => h (optionProduct.symm.injective e)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp he
  refine ⟨⟨none,none⟩,⟨none,some j⟩,rfl,?_⟩
  simpa [chart, coordinates] using hj.symm
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

section Bridge
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

end Bridge
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem selected_kernel_count
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i : Fin (n+1)) (r : J → Fin (n+1)) (x : J → ChartSpace κ n)
    (hx : Function.Injective (fun j => (x j).1))
    (hz : ∀ j, matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  have he (j : J) :
      (fun z => output (r j) (fun a => eval (chart i (r j) z) (system A₀ A B i a))) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h := by
    funext z
    exact system_eq_matrixKernelSystem F ψ h A₀ A B hlocal hdir i (r j) z
  have hz' (j : J) (a : Equations κ n) : eval (chart i (r j) (x j)) (system A₀ A B i a) = 0 := by
    have hh : output (r j) (fun a => eval (chart i (r j) (x j)) (system A₀ A B i a)) =
        output (r j) 0 := by
      rw [map_zero, congrFun (he j) (x j)]
      exact hz j
    exact congrFun ((output (r j)).injective hh) a
  have hc := Multigraded.bilinear_simple_point_count_reindex (dimensions κ n)
    Sigma.fst variablesEquiv variablesEquiv_group firstGroup secondGroup card_equations
    (system A₀ A B i) (system_homogeneous A₀ A B i)
    (fun j => base i (r j)) (fun j => base_group i (r j))
    (fun j => output (r j)) (fun j => chart i (r j)) (fun j => contDiff_chart i (r j))
    (fun j z => chart_base i (r j) z) x
    (fun j k hjk => chart_separated (fun hh => hjk (hx hh))) hz'
    (fun j => by rw [he]; exact hs j)
  exact hc.trans mixed_coefficient_bound
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

lemma affine_contDiff (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    ContDiff ℂ 2 (fun y => affine A₀ A y i j) := by
  unfold affine
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma affine_derivative (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y h : σ → ℂ) (i j : Fin (n+1)) :
    fderiv ℂ (fun y => affine A₀ A y i j) y h = ∑ v, h v * A v i j := by
  let L : (σ → ℂ) →L[ℂ] ℂ := ∑ v, A v i j • ContinuousLinearMap.proj v
  have he : (fun y => affine A₀ A y i j) = (fun y => A₀ i j + L y) := by
    funext y
    simp [affine,L,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]
  have hd : HasFDerivAt (fun y => A₀ i j + L y) L y := by
    exact HasFDerivAt.const_add (A₀ i j) L.hasFDerivAt
  rw [he, hd.fderiv]
  simp [L,mul_comm]

lemma affine_right_mul (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    affine (A₀*S) (fun v => A v*S) y = affine A₀ A y * S := by
  simp [affine, add_mul, Finset.sum_mul]

theorem affine_polar_count
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (b : σ → ℂ) (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : J → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  let ψ := fun z : ℂ × (κ → ℂ) => b + L (optionProduct.symm z)
  obtain ⟨S,hS,hr⟩ := finite_simple_polar_kernel_lifts (0 : Fin (n+1))
    (affine A₀ A) (affine_contDiff A₀ A) ψ h x
    (fun _ => ((differentiable_const b).add (L.differentiable.comp optionProduct.symm.differentiable)).differentiableAt)
    hz hs
  choose r hr using hr
  let A₀' := A₀*S
  let A' := fun v => A v*S
  let B₀ := affine A₀' A' b
  let B := fun k => ∑ v, L (Pi.single k 1) v • A' v
  let D := fun k => ∑ v, h k v • A' v
  have hlocal (z : ℂ × (κ → ℂ)) (i j : Fin (n+1)) :
      B₀ i j + ∑ k, B k i j * optionProduct.symm z k = affine A₀' A' (ψ z) i j := by
    have hexp : optionProduct.symm z = ∑ k, optionProduct.symm z k • Pi.single k 1 := by
      ext k
      simp [Pi.single_apply]
    have hLe (v : σ) : L (optionProduct.symm z) v =
        ∑ k, optionProduct.symm z k * L (Pi.single k 1) v := by
      conv_lhs => rw [hexp, map_sum]
      simp
    simp only [B₀, B, affine, ψ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.add_apply, hLe, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm, ← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hd (y : σ → ℂ) (k : κ) (i j : Fin (n+1)) :
      fderiv ℂ (fun y => affine A₀' A' y i j) y (h k) = D k i j := by
    rw [affine_derivative]
    simp [D,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let X := fun j => matrixKernelPoint
    (fun y => (affine A₀' A' y).submatrix (pivotEquiv (r j)) (pivotEquiv (0 : Fin (n+1)))) ψ (x j)
  apply selected_kernel_count (affine A₀' A') ψ h B₀ B D hlocal hd 0 r X
  · exact hx
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).1
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).2
end PermanentBorder.KernelBilinear

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.KernelBilinear.affine_polar_count := @_root_.OAI.PermanentBorder.KernelBilinear.affine_polar_count
