-- Prove2me | solution 1 for LinearIdentifiability.linear_identifiability
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:07:39.687723+00:00
-- url     : https://prove2.me/submissions/27f24d4f-6552-4a63-9093-531fde3acae2

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

theorem f_linear_system {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (x : X) (a b : Fin M → Y)
    (hab : ∀ i, ∃ S, IsSupported pD x S ∧ a i ∈ S ∧ b i ∈ S)
    (hL' : IsUnit (diffMatrix g' a b).det) (hLstar : IsUnit (diffMatrix gstar a b).det) :
    (diffMatrix g' a b)ᵀ *ᵥ f' x = (diffMatrix gstar a b)ᵀ *ᵥ fstar x ∧
      f' x = (diffMatrix gstar a b * (diffMatrix g' a b)⁻¹)ᵀ *ᵥ fstar x ∧
      IsUnit (diffMatrix gstar a b * (diffMatrix g' a b)⁻¹)ᵀ.det := by
  have h1 : (diffMatrix g' a b)ᵀ *ᵥ f' x = (diffMatrix gstar a b)ᵀ *ᵥ fstar x := by
    funext i
    obtain ⟨S, hS, ha, hb⟩ := hab i
    have := (likelihood_ratio_identity pD hD f' fstar g' gstar hp x S hS (a i) (b i) ha hb).2
    simpa [Matrix.mulVec, dotProduct, diffMatrix, Matrix.transpose_apply] using this
  exact ⟨h1, li_solve _ _ hL' _ _ h1, li_det _ _ hL' hLstar⟩

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

theorem linear_identifiability {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (a b : Fin M → Y)
    (hab : ∀ x ∈ inputSupport pD, ∀ i, ∃ S, IsSupported pD x S ∧ a i ∈ S ∧ b i ∈ S)
    (hL' : IsUnit (diffMatrix g' a b).det) (hLstar : IsUnit (diffMatrix gstar a b).det)
    (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hxs : ∀ i, IsSupported pD (xs i) (Ss i)) (hcov : ∀ y ∈ targetSupport pD, ∀ i, y ∈ Ss i)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∃ A : Matrix (Fin M) (Fin M) ℝ, IsUnit A.det ∧
        ∀ x ∈ inputSupport pD, f' x = A *ᵥ fstar x) ∧
      (∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ, IsUnit C.det ∧
        ∀ y ∈ targetSupport pD, augG g' y = C *ᵥ augG gstar y) ∧
      (∃ (B : Matrix (Fin M) (Fin M) ℝ) (c : Fin M → ℝ), IsUnit B.det ∧
        ∀ y ∈ targetSupport pD, g' y = B *ᵥ gstar y + c) := by
  classical
  refine ⟨⟨(diffMatrix gstar a b * (diffMatrix g' a b)⁻¹)ᵀ, li_det _ _ hL' hLstar, fun x hx => ?_⟩,
    ?_⟩
  · exact (f_linear_system pD hD f' fstar g' gstar hp x a b (hab x hx) hL' hLstar).2.1
  set C := (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ with hC
  have hG : ∀ y ∈ targetSupport pD, augG g' y = C *ᵥ augG gstar y := by
    intro y hy
    have hpos : ∀ i, pD (xs i, y, Ss i) ≠ 0 := fun i => ((hD.2 _ _ (hxs i) y).2 (hcov y hy i))
    exact (g_tilde_linear_system pD hD f' fstar g' gstar hp y xs Ss hpos hM' hMstar).2.2.1
  refine ⟨⟨C, li_det _ _ hM' hMstar, hG⟩, ?_⟩
  set B : Matrix (Fin M) (Fin M) ℝ := fun j i => C j.succ i.succ with hB
  set c : Fin M → ℝ := fun j => C j.succ 0 with hc
  have hg : ∀ y ∈ targetSupport pD, g' y = B *ᵥ gstar y + c := by
    intro y hy
    funext j
    have := congrFun (hG y hy) j.succ
    simp only [augG, Matrix.cons_val_succ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, mul_one] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, hB, hc]
    rw [this]; ring
  by_cases hT : (targetSupport pD).Nonempty
  · obtain ⟨y0, x0, S0, h0⟩ := hT
    have hx0 : x0 ∈ inputSupport pD := ⟨S0, y0, h0⟩
    have hmem : ∀ i, a i ∈ targetSupport pD ∧ b i ∈ targetSupport pD := by
      intro i
      obtain ⟨S, hS, ha, hb⟩ := hab x0 hx0 i
      exact ⟨⟨x0, S, (hD.2 _ _ hS _).2 ha⟩, ⟨x0, S, (hD.2 _ _ hS _).2 hb⟩⟩
    have hLB : diffMatrix g' a b = B * diffMatrix gstar a b := by
      ext j i
      simp only [diffMatrix, Matrix.mul_apply]
      rw [hg (a i) (hmem i).1, hg (b i) (hmem i).2]
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    refine ⟨B, c, ?_, hg⟩
    rw [hLB, Matrix.det_mul] at hL'
    exact isUnit_of_mul_isUnit_left hL'
  · exact ⟨1, 0, by simp, fun y hy => (hT ⟨y, hy⟩).elim⟩

end LinearIdentifiability

open LinearIdentifiability Matrix in
theorem solution {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (a b : Fin M → Y)
    (hab : ∀ x ∈ inputSupport pD, ∀ i, ∃ S, IsSupported pD x S ∧ a i ∈ S ∧ b i ∈ S)
    (hL' : IsUnit (diffMatrix g' a b).det) (hLstar : IsUnit (diffMatrix gstar a b).det)
    (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hxs : ∀ i, IsSupported pD (xs i) (Ss i)) (hcov : ∀ y ∈ targetSupport pD, ∀ i, y ∈ Ss i)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∃ A : Matrix (Fin M) (Fin M) ℝ, IsUnit A.det ∧
        ∀ x ∈ inputSupport pD, f' x = A *ᵥ fstar x) ∧
      (∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ, IsUnit C.det ∧
        ∀ y ∈ targetSupport pD, augG g' y = C *ᵥ augG gstar y) ∧
      (∃ (B : Matrix (Fin M) (Fin M) ℝ) (c : Fin M → ℝ), IsUnit B.det ∧
        ∀ y ∈ targetSupport pD, g' y = B *ᵥ gstar y + c) :=
  LinearIdentifiability.linear_identifiability pD hD f' fstar g' gstar hp a b hab hL' hLstar xs Ss hxs hcov hM' hMstar
