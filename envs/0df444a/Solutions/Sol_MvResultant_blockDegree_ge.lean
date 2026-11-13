-- Prove2me | solution 1 for MvResultant.blockDegree_ge
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T19:04:35.743716+00:00
-- url     : https://prove2.me/submissions/3cc97c21-4f97-4eaf-ae84-48d37fcb9366

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper MvPolynomial Finset

namespace LowerAux

variable {n : ℕ}

/-- `∏_{a=1}^{d} (x_j - a x_i)` -/
noncomputable def G (i j : Fin n) (d : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ a ∈ range d, (X j - C ((a : ℂ) + 1) * X i)

lemma lin_hom (i j : Fin n) (c : ℂ) : (X j - C c * X i : MvPolynomial (Fin n) ℂ).IsHomogeneous 1 := by
  have h2 := (isHomogeneous_C (Fin n) c).mul (isHomogeneous_X ℂ i)
  rw [zero_add] at h2
  exact (isHomogeneous_X ℂ j).sub h2

lemma G_hom (i j : Fin n) (d : ℕ) : (G i j d).IsHomogeneous d := by
  have := IsHomogeneous.prod (range d) (fun a => (X j - C ((a : ℂ) + 1) * X i : MvPolynomial (Fin n) ℂ))
    (fun _ => 1) (fun a _ => lin_hom i j _)
  rw [sum_const, card_range, smul_eq_mul, mul_one] at this
  exact this

lemma eval_G (i j : Fin n) (d : ℕ) (x : Fin n → ℂ) :
    eval x (G i j d) = ∏ a ∈ range d, (x j - ((a : ℂ) + 1) * x i) := by
  simp [G]

/-- the direction of the line: `x_i^{d-1} (x_i + ∑_{j ≠ i} B^j (x_j - x_i))` -/
noncomputable def hdir (i : Fin n) (B d : ℕ) : MvPolynomial (Fin n) ℂ :=
  X i ^ (d - 1) * (X i + ∑ j ∈ univ.erase i, C ((B : ℂ) ^ (j : ℕ)) * (X j - X i))

lemma hdir_hom (i : Fin n) (B d : ℕ) (hd : 1 ≤ d) : (hdir i B d).IsHomogeneous d := by
  have h1 : (X i + ∑ j ∈ univ.erase i, C ((B : ℂ) ^ (j : ℕ)) * (X j - X i) :
      MvPolynomial (Fin n) ℂ).IsHomogeneous 1 := by
    refine (isHomogeneous_X ℂ i).add (IsHomogeneous.sum _ _ _ fun j _ => ?_)
    have := (isHomogeneous_C (Fin n) ((B : ℂ) ^ (j : ℕ))).mul (lin_hom i j 1)
    simpa using this
  have := (isHomogeneous_X_pow i (d - 1)).mul h1
  unfold hdir
  rwa [Nat.sub_add_cancel hd] at this

/-- degree bound for a polynomial substitution -/
lemma natDegree_aeval_le {σ : Type*} (P : MvPolynomial σ ℂ) (f : σ → Polynomial ℂ) (d : σ → ℕ)
    (hf : ∀ v, (f v).natDegree ≤ d v) (δ : ℕ)
    (hP : ∀ m ∈ P.support, ∑ v ∈ m.support, m v * d v ≤ δ) :
    (aeval f P).natDegree ≤ δ := by
  rw [aeval_def, eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ((sum_le_sum fun v _ => ?_).trans (hP m hm))
  refine Polynomial.natDegree_pow_le.trans ?_
  exact Nat.mul_le_mul_left _ (hf v)

end LowerAux

open LowerAux in
theorem solution {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) (δ : ℕ)
    (hδ : res.IsWeightedHomogeneous (fun v : ResVar n D => if v.1 = i then 1 else 0) δ) :
    ∏ j ∈ Finset.univ.erase i, D j ≤ δ := by
  classical
  set P := MvPolynomial.map (Int.castRingHom ℂ) res with hP
  set B : ℕ := (∑ j, D j) + 1 with hB
  have hDB : ∀ j, D j < B := fun j => by
    have := single_le_sum (f := D) (fun _ _ => Nat.zero_le _) (mem_univ j); omega
  -- the forms along the line
  set h := hdir i B (D i) with hh
  set F0 : Fin n → MvPolynomial (Fin n) ℂ :=
    fun j => if j = i then X i ^ D i else G i j (D j) with hF0
  set Fh : Fin n → MvPolynomial (Fin n) ℂ := fun j => if j = i then -h else 0 with hFh
  set Fs : ℂ → Fin n → MvPolynomial (Fin n) ℂ := fun s j => F0 j + C s * Fh j with hFs_def
  have hFs : ∀ s j, (Fs s j).IsHomogeneous (D j) := by
    intro s j
    have h0 : (F0 j).IsHomogeneous (D j) := by
      by_cases hj : j = i
      · subst hj; simp only [hF0, if_true]; exact isHomogeneous_X_pow _ _
      · simp only [hF0, if_neg hj]; exact G_hom i j (D j)
    have h1 : (Fh j).IsHomogeneous (D j) := by
      by_cases hj : j = i
      · subst hj; simp only [hFh, if_true]; exact (hdir_hom j B (D j) (hD j)).neg
      · simp only [hFh, if_neg hj]; exact isHomogeneous_zero _ _ _
    have h2 := (isHomogeneous_C (Fin n) s).mul h1
    rw [zero_add] at h2
    exact h0.add h2
  -- the restriction of the resultant to the line
  set ρ : Polynomial ℂ := aeval (fun v : ResVar n D =>
    Polynomial.C (coeff v.2.1 (F0 v.1)) + Polynomial.C (coeff v.2.1 (Fh v.1)) * Polynomial.X) P
    with hρ
  have hρeval : ∀ s, ρ.eval s = aeval (fun v : ResVar n D => coeff v.2.1 (Fs s v.1)) P := by
    intro s
    rw [← Polynomial.coe_aeval_eq_eval, hρ, ← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext v
    simp only [hFs_def, coeff_add, coeff_C_mul, map_add, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hdeg : ρ.natDegree ≤ δ := by
    apply natDegree_aeval_le P _ (fun v => if v.1 = i then 1 else 0)
    · intro v
      by_cases hv : v.1 = i
      · rw [if_pos hv, add_comm]; exact Polynomial.natDegree_linear_le
      · simp [hFh, hv]
    · intro m hm
      have hm' : coeff m res ≠ 0 := by
        intro h0; apply mem_support_iff.mp hm; rw [hP, coeff_map, h0, map_zero]
      have := hδ hm'
      rw [Finsupp.weight_apply, Finsupp.sum] at this
      simp only [smul_eq_mul] at this
      exact this.le
  -- nonvanishing at `t = 0`
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have hz : aeval (fun v : ResVar n D => coeff v.2.1 (Fs 0 v.1)) P = 0 := by
      rw [← hρeval, h0, Polynomial.eval_zero]
    obtain ⟨x, hx0, hx⟩ := (hres.1 (Fs 0) (hFs 0)).mpr hz
    apply hx0
    have hxi : x i = 0 := by
      have := hx i
      simp only [hFs_def, hF0, if_true, map_zero, zero_mul, add_zero, eval_pow, eval_X] at this
      exact pow_eq_zero_iff (by have := hD i; omega) |>.mp this
    funext j
    by_cases hj : j = i
    · rw [hj, hxi]; rfl
    · have := hx j
      simp only [hFs_def, hF0, if_neg hj, map_zero, zero_mul, add_zero, eval_G, hxi,
        mul_zero, sub_zero, prod_const, card_range] at this
      exact pow_eq_zero_iff (by have := hD j; omega) |>.mp this
  -- the roots
  let T := (j : {j : Fin n // j ≠ i}) → Fin (D j)
  let p : T → Fin n → ℂ := fun y j => if hj : j = i then 1 else ((y ⟨j, hj⟩ : ℕ) : ℂ) + 1
  let Y : T → Fin n → Fin B := fun y j =>
    if hj : j = i then ⟨0, by omega⟩ else ⟨y ⟨j, hj⟩, (y ⟨j, hj⟩).2.trans (hDB j)⟩
  have hY : Function.Injective Y := by
    intro y y' hyy
    funext ⟨j, hj⟩
    have := congrFun hyy j
    simp only [Y, dif_neg hj, Fin.mk.injEq] at this
    exact Fin.ext this
  have hhp : ∀ y, eval (p y) h = ((finFunctionFinEquiv (Y y) : ℕ) : ℂ) + 1 := by
    intro y
    rw [finFunctionFinEquiv_apply]
    simp only [hh, hdir, map_mul, map_pow, eval_X, map_add, map_sum, eval_C, map_sub]
    have hpi : p y i = 1 := by simp [p]
    rw [hpi, one_pow, one_mul, add_comm (1 : ℂ)]
    push_cast
    congr 1
    rw [← sum_erase (s := univ) (a := i) (by simp [Y])]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≠ i := ne_of_mem_erase hj
    simp [p, Y, dif_neg hj', mul_comm]
  let root : T → ℂ := fun y => 1 / (((finFunctionFinEquiv (Y y) : ℕ) : ℂ) + 1)
  have hroot_inj : Function.Injective root := by
    intro y y' hyy
    simp only [root, one_div, inv_inj, add_left_inj, Nat.cast_inj] at hyy
    exact hY (finFunctionFinEquiv.injective (Fin.ext hyy))
  have hroot : ∀ y, ρ.eval (root y) = 0 := by
    intro y
    rw [hρeval]
    apply (hres.1 (Fs (root y)) (hFs (root y))).mp
    refine ⟨p y, fun h0 => by simpa [p] using congrFun h0 i, fun j => ?_⟩
    by_cases hj : j = i
    · rw [hj]
      have hne : ((finFunctionFinEquiv (Y y) : ℕ) : ℂ) + 1 ≠ 0 :=
        Nat.cast_add_one_ne_zero _
      simp only [hFs_def, hF0, hFh, if_true, map_add, map_mul, eval_C, map_neg, map_pow,
        eval_X, hhp, root]
      have hpi : p y i = 1 := by simp [p]
      rw [hpi, one_pow]
      field_simp
      ring
    · simp only [hFs_def, hF0, hFh, if_neg hj, mul_zero, add_zero, eval_G]
      apply prod_eq_zero (i := ((y ⟨j, hj⟩ : ℕ))) (mem_range.mpr (y ⟨j, hj⟩).2)
      simp [p, dif_neg hj]
  have hcard : (univ.image root).card = ∏ j ∈ univ.erase i, D j := by
    rw [card_image_of_injective _ hroot_inj, card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact (prod_subtype (univ.erase i) (p := fun j => j ≠ i) (by simp) D).symm
  rw [← hcard]
  refine (Polynomial.card_le_degree_of_subset_roots ?_).trans hdeg
  intro z hz
  obtain ⟨y, _, rfl⟩ := mem_image.mp hz
  exact (Polynomial.mem_roots hρ0).mpr (hroot y)
