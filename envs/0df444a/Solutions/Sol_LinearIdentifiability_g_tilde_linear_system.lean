-- Prove2me | solution 1 for LinearIdentifiability.g_tilde_linear_system
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:06:20.897925+00:00
-- url     : https://prove2.me/submissions/50ac32d5-0256-4a62-9dcf-71a1f9ae8cbe

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix
namespace LinearIdentifiability

lemma li_ratio {X Y : Type*} {M : ℕ} (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X)
    (S : Finset Y) (yA yB : Y) (hA : yA ∈ S) :
    modelProb f g x S yA / modelProb f g x S yB = Real.exp (f x ⬝ᵥ g yA - f x ⬝ᵥ g yB) := by
  have hZ : 0 < ∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨yA, hA⟩
  unfold modelProb
  rw [div_div_div_cancel_right₀ hZ.ne', Real.exp_sub]

lemma li_log {X Y : Type*} {M : ℕ} (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X)
    (S : Finset Y) (y : Y) (hy : y ∈ S) :
    augF f g x S ⬝ᵥ augG g y = Real.log (modelProb f g x S y) := by
  have hZ : 0 < ∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨y, hy⟩
  unfold augF augG modelProb logNormalizer
  rw [Matrix.cons_dotProduct_cons, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  ring

lemma li_solve {n : Type*} [Fintype n] [DecidableEq n] (L' Ls : Matrix n n ℝ)
    (hL' : IsUnit L'.det) (u v : n → ℝ) (h : L'ᵀ *ᵥ u = Lsᵀ *ᵥ v) :
    u = (Ls * L'⁻¹)ᵀ *ᵥ v := by
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← h, Matrix.transpose_nonsing_inv,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]),
    Matrix.one_mulVec]

lemma li_det {n : Type*} [Fintype n] [DecidableEq n] (L' Ls : Matrix n n ℝ)
    (hL' : IsUnit L'.det) (hLs : IsUnit Ls.det) : IsUnit (Ls * L'⁻¹)ᵀ.det := by
  rw [Matrix.det_transpose, Matrix.det_mul]
  exact hLs.mul (Matrix.isUnit_nonsing_inv_det L' hL')

theorem g_tilde_linear_system {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (y : Y) (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hpos : ∀ i, pD (xs i, y, Ss i) ≠ 0)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∀ i, augF f' g' (xs i) (Ss i) ⬝ᵥ augG g' y = augF fstar gstar (xs i) (Ss i) ⬝ᵥ augG gstar y) ∧
      (augFMatrix f' g' xs Ss)ᵀ *ᵥ augG g' y = (augFMatrix fstar gstar xs Ss)ᵀ *ᵥ augG gstar y ∧
      augG g' y = (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ *ᵥ augG gstar y ∧
      IsUnit (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ.det := by
  have h0 : ∀ i, augF f' g' (xs i) (Ss i) ⬝ᵥ augG g' y =
      augF fstar gstar (xs i) (Ss i) ⬝ᵥ augG gstar y := by
    intro i
    have hS : IsSupported pD (xs i) (Ss i) := ⟨y, hpos i⟩
    have hy : y ∈ Ss i := (hD.2 _ _ hS y).1 (hpos i)
    rw [li_log _ _ _ _ _ hy, li_log _ _ _ _ _ hy, hp _ _ hS y hy]
  have h1 : (augFMatrix f' g' xs Ss)ᵀ *ᵥ augG g' y =
      (augFMatrix fstar gstar xs Ss)ᵀ *ᵥ augG gstar y := by
    funext i
    have := h0 i
    simpa [Matrix.mulVec, dotProduct, augFMatrix, Matrix.transpose_apply] using this
  exact ⟨h0, h1, li_solve _ _ hM' _ _ h1, li_det _ _ hM' hMstar⟩

end LinearIdentifiability

open LinearIdentifiability Matrix in
theorem solution {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (y : Y) (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hpos : ∀ i, pD (xs i, y, Ss i) ≠ 0)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∀ i, augF f' g' (xs i) (Ss i) ⬝ᵥ augG g' y = augF fstar gstar (xs i) (Ss i) ⬝ᵥ augG gstar y) ∧
      (augFMatrix f' g' xs Ss)ᵀ *ᵥ augG g' y = (augFMatrix fstar gstar xs Ss)ᵀ *ᵥ augG gstar y ∧
      augG g' y = (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ *ᵥ augG gstar y ∧
      IsUnit (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ.det :=
  LinearIdentifiability.g_tilde_linear_system pD hD f' fstar g' gstar hp y xs Ss hpos hM' hMstar
