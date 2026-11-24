-- Prove2me | solution 1 for LinearIdentifiability.likelihood_ratio_identity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:06:20.929259+00:00
-- url     : https://prove2.me/submissions/4cfe3cff-97b0-4be3-95bf-1f9f2391f9c1

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

theorem likelihood_ratio_identity {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (x : X) (S : Finset Y) (hS : IsSupported pD x S) (yA yB : Y) (hA : yA ∈ S) (hB : yB ∈ S) :
    modelProb f' g' x S yA / modelProb f' g' x S yB =
        modelProb fstar gstar x S yA / modelProb fstar gstar x S yB ∧
      (g' yA - g' yB) ⬝ᵥ f' x = (gstar yA - gstar yB) ⬝ᵥ fstar x := by
  have h1 : modelProb f' g' x S yA / modelProb f' g' x S yB =
      modelProb fstar gstar x S yA / modelProb fstar gstar x S yB := by
    rw [hp x S hS yA hA, hp x S hS yB hB]
  refine ⟨h1, ?_⟩
  rw [li_ratio _ _ _ _ _ _ hA, li_ratio _ _ _ _ _ _ hA] at h1
  have h2 := Real.exp_injective h1
  rw [sub_dotProduct, sub_dotProduct, dotProduct_comm (g' yA), dotProduct_comm (g' yB),
    dotProduct_comm (gstar yA), dotProduct_comm (gstar yB)]
  exact h2

end LinearIdentifiability

open LinearIdentifiability Matrix in
theorem solution {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (x : X) (S : Finset Y) (hS : IsSupported pD x S) (yA yB : Y) (hA : yA ∈ S) (hB : yB ∈ S) :
    modelProb f' g' x S yA / modelProb f' g' x S yB =
        modelProb fstar gstar x S yA / modelProb fstar gstar x S yB ∧
      (g' yA - g' yB) ⬝ᵥ f' x = (gstar yA - gstar yB) ⬝ᵥ fstar x :=
  LinearIdentifiability.likelihood_ratio_identity pD hD f' fstar g' gstar hp x S hS yA yB hA hB
