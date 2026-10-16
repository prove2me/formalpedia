-- Prove2me | solution 1 for OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:51:21.259985+00:00
-- url     : https://prove2.me/submissions/84d122c1-0a63-4c03-9147-19b2c966b1bc

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/BilinearCounts.lean:L176-L251
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem. The node keeps its source
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

-- ---- from OAI.Algebra.Determinantal.BilinearCounts ----
namespace OAI

namespace PermanentBorder.PolarAnalysis
open Matrix Schur Filter
open scoped Topology
variable {κ J T : Type*} [Fintype κ] [Finite J]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

lemma sum_norm (i : Fin (n+1)) (f : Fin (n+1) → ℂ) (z : Fin n → ℂ) :
    ∑ j, f j * norm i z j = f i + ∑ j, f (i.succAbove j) * z j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma polar_norm (i r : Fin (n+1)) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (u v : Fin n → ℂ) :
    (∑ a, ∑ b, B a b * norm i u b * norm r v a) =
      normalized v ⬝ᵥ ((B.submatrix (pivotEquiv r) (pivotEquiv i)) *ᵥ normalized u) := by
  simp only [mulVec, dotProduct]
  symm
  apply Fintype.sum_equiv (pivotEquiv r)
  intro a
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (pivotEquiv i) _ _ (fun b => by
    simp [norm, Matrix.submatrix_apply, mul_comm, mul_left_comm])

section Bridge
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

lemma system_eq_matrixKernelSystem
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i r : Fin (n+1)) (z : ChartSpace κ n) :
    output r (fun j => eval (chart i r z) (system A₀ A B i j)) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) ψ h z := by
  have hright (a : Fin (n+1)) :
      eval (chart i r z) (rightEquation A₀ A a) =
        F (ψ z.1) a i + ∑ j, F (ψ z.1) a (i.succAbove j) * z.2.1 j := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_right]
    simp only [hlocal]
    exact sum_norm i _ _
  have hleft (b : Fin (n+1)) :
      eval (chart i r z) (leftEquation A₀ A b) =
        F (ψ z.1) r b + ∑ a, z.2.2 a * F (ψ z.1) (r.succAbove a) b := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_left]
    simp only [hlocal]
    rw [sum_norm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  have hpolar (k : κ) :
      eval (chart i r z) (polarEquation (B k)) =
        normalized z.2.2 ⬝ᵥ ((B k).submatrix (pivotEquiv r) (pivotEquiv i) *ᵥ normalized z.2.1) := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_polar, polar_norm]
  have hdir' (k : κ) :
      dirMatrix (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i))
        (ψ z.1) (h k) = (B k).submatrix (pivotEquiv r) (pivotEquiv i) := by
    ext a b
    exact hdir _ _ _ _
  apply Prod.ext
  · apply Prod.ext
    · change eval (chart i r z) (rightEquation A₀ A r) = _
      rw [hright]
      rfl
    · funext k
      change eval (chart i r z) (polarEquation (B k)) = _
      rw [hpolar]
      change _ = normalized z.2.2 ⬝ᵥ (dirMatrix
        (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr))
        (ψ z.1) (h k) *ᵥ normalized z.2.1)
      have hb : (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr)) =
          (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) := by
        funext y a b
        cases a with
        | inl u => cases u; cases b with
          | inl v => cases v; rfl
          | inr b => rfl
        | inr a => cases b with
          | inl v => cases v; rfl
          | inr b => rfl
      rw [hb, hdir']
  · apply Prod.ext
    · funext j
      change eval (chart i r z) (rightEquation A₀ A (r.succAbove j)) = _
      rw [hright]
      rfl
    · funext j
      change eval (chart i r z) (leftEquation A₀ A (i.succAbove j)) = _
      rw [hleft]
      rfl
end Bridge
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

end PermanentBorder.KernelBilinear

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem := @_root_.OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem
