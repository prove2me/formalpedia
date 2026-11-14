-- Prove2me | solution 1 for HararySachs.Hyper.phiPoly_vTensor_factor
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T05:21:08.62379+00:00
-- url     : https://prove2.me/submissions/a3d2bdd8-5e2a-4eaa-a5ca-dbb04364dfd9

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_HararySachs_Hyper_det_generic_irreducible
import Theorems.Thm_HararySachs_Hyper_irreducible_dvd_of_vanishing
import Theorems.Thm_HararySachs_Hyper_phiPoly_vTensor_eval
import Theorems.Thm_HararySachs_Hyper_phiPoly_natDegree_le

open HararySachs.Hyper Finset

set_option linter.unusedSectionVars false

namespace FactorAux

/-! ### Polynomials in `z` whose `z^j`-coefficient is homogeneous of degree `j r` -/

section Graded

variable {σ K : Type*} [CommRing K]

def GrW (r : ℕ) (Φ : Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ j, (Φ.coeff j).IsHomogeneous (j * r)

lemma GrW_add {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ K)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ + Ψ) :=
  fun j => by rw [Polynomial.coeff_add]; exact (h1 j).add (h2 j)

lemma GrW_neg {r : ℕ} {Φ : Polynomial (MvPolynomial σ K)} (h : GrW r Φ) : GrW r (-Φ) :=
  fun j => by rw [Polynomial.coeff_neg]; exact (h j).neg

lemma GrW_sub {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ K)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ - Ψ) := by
  rw [sub_eq_add_neg]; exact GrW_add h1 (GrW_neg h2)

lemma GrW_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ K))
    (h : ∀ x ∈ s, GrW r (f x)) : GrW r (∑ x ∈ s, f x) :=
  fun j => by
    rw [Polynomial.finsetSum_coeff]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun x hx => h x hx j

lemma GrW_mul {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ K)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ * Ψ) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have := (h1 x.1).mul (h2 x.2)
  rwa [← add_mul, hx] at this

lemma GrW_intCast (r : ℕ) (c : ℤ) : GrW r (c : Polynomial (MvPolynomial σ K)) := by
  intro j
  rw [← map_intCast (Polynomial.C : MvPolynomial σ K →+* _) c, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [← map_intCast (MvPolynomial.C : K →+* MvPolynomial σ K) c, zero_mul]
    exact MvPolynomial.isHomogeneous_C _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

lemma GrW_one (r : ℕ) : GrW r (1 : Polynomial (MvPolynomial σ K)) := by
  have := GrW_intCast (σ := σ) (K := K) r 1
  rwa [Int.cast_one] at this

lemma GrW_prod {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ K))
    (h : ∀ x ∈ s, GrW r (f x)) : GrW r (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty]; exact GrW_one r
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact GrW_mul (h a (mem_insert_self a s)) (ih fun x hx => h x (mem_insert_of_mem hx))

lemma GrW_eval₂ {r : ℕ} {τ : Type*} (res : MvPolynomial τ ℤ)
    (g : τ → Polynomial (MvPolynomial σ K)) (hg : ∀ v, GrW r (g v)) :
    GrW r (MvPolynomial.eval₂ (Int.castRingHom _) g res) := by
  induction res using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.eval₂_C]; exact GrW_intCast r a
  | add p q hp hq => rw [MvPolynomial.eval₂_add]; exact GrW_add hp hq
  | mul_X p v hp => rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact GrW_mul hp (hg v)

lemma GrW_lin (a b : MvPolynomial σ K) (ha : a.IsHomogeneous 0) (hb : b.IsHomogeneous 1) :
    GrW 1 (Polynomial.C a - Polynomial.C b * Polynomial.X) := by
  intro m
  rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  rcases m with _ | _ | m
  · simpa using ha
  · simpa using hb.neg
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      show m + 1 + 1 ≠ 1 by omega, sub_zero]
    exact MvPolynomial.isHomogeneous_zero _ _ _

lemma charpolyRev_GrW {n : ℕ} (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    (hN : ∀ i j, (N i j).IsHomogeneous 1) : GrW 1 N.charpolyRev := by
  classical
  unfold Matrix.charpolyRev
  rw [Matrix.det_apply]
  refine GrW_sum _ _ fun τ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine GrW_mul (GrW_intCast 1 _) (GrW_prod _ _ fun i _ => ?_)
  have he : (1 - (Polynomial.X : Polynomial (MvPolynomial σ K)) • N.map Polynomial.C) (τ i) i =
      Polynomial.C (if τ i = i then 1 else 0) - Polynomial.C (N (τ i) i) * Polynomial.X := by
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.X_mul_C]
    split_ifs <;> simp
  rw [he]
  refine GrW_lin _ _ ?_ (hN _ _)
  split_ifs
  · exact MvPolynomial.isHomogeneous_one _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- a graded polynomial is recovered from its value at `z = 1` -/
lemma coeff_eq_homComp (F : Polynomial (MvPolynomial σ K)) (hF : GrW 1 F) (m : ℕ) :
    F.coeff m = MvPolynomial.homogeneousComponent m (F.eval 1) := by
  rw [Polynomial.eval_eq_sum_range, map_sum]
  simp only [one_pow, mul_one]
  have hc : ∀ j, MvPolynomial.homogeneousComponent m (F.coeff j) =
      if m = j * 1 then F.coeff j else 0 := fun j =>
    MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hF j))
  simp_rw [hc, mul_one]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end Graded

/-! ### Homogeneous polynomials along a line -/

section Line

variable {σ : Type*}

lemma eval_smul_homog {p : MvPolynomial σ ℂ} {d : ℕ} (hp : p.IsHomogeneous d) (t : ℂ)
    (x : σ → ℂ) : MvPolynomial.eval (fun q => t * x q) p = t ^ d * MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, mul_sum]
  refine sum_congr rfl fun μ hμ => ?_
  have hdeg : ∑ i ∈ μ.support, μ i = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hμ)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hdeg]
  ring

variable {n : ℕ}

/-- restriction to the line `t ↦ t x` -/
noncomputable def lam (x : Fin n × Fin n → ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun p => Polynomial.C (x p) * Polynomial.X

lemma eval_lam (x : Fin n × Fin n → ℂ) (t : ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    (lam x p).eval t = MvPolynomial.eval (fun q => t * x q) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lam]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X, lam,
      MvPolynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

lemma lam_homog (x : Fin n × Fin n → ℂ) {p : MvPolynomial (Fin n × Fin n) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    lam x p = Polynomial.C (MvPolynomial.eval x p) * Polynomial.X ^ d := by
  refine Polynomial.funext fun t => ?_
  rw [eval_lam, eval_smul_homog hp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, mul_comm]

lemma natDegree_charpolyRev (N : Matrix (Fin n) (Fin n) ℂ) (h : N.det ≠ 0) :
    N.charpolyRev.natDegree = n := by
  rw [← Matrix.reverse_charpoly, Polynomial.reverse_natDegree,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h0 : N.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply h
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  rw [Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr h0), Nat.sub_zero]

lemma charpolyRev_ne_zero (N : Matrix (Fin n) (Fin n) ℂ) : N.charpolyRev ≠ 0 := by
  intro h
  have := Matrix.eval_charpolyRev (M := N)
  rw [h, Polynomial.eval_zero] at this
  exact zero_ne_one this

end Line

/-! ### Homogeneity of `Φ_V` -/

lemma phi_GrW (n k : ℕ) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    GrW (k - 1) (phiPoly (k := k) (vTensor n k) res) := by
  have hΦ' : phiPoly (k := k) (vTensor n k) res = MvPolynomial.eval₂ (Int.castRingHom _)
      (fun v : ResVar n (fun _ => k - 1) =>
        MvPolynomial.coeff v.2.1 (zcoord (k := k) (vTensor n k) v.1)) res := by
    unfold phiPoly
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  rw [hΦ']
  refine GrW_eval₂ res _ fun v => ?_
  unfold zcoord
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum]
  refine GrW_sub ?_ (GrW_sum _ _ fun t _ => ?_)
  · split_ifs
    · intro j; rw [Polynomial.coeff_one]; split_ifs with h
      · subst h; rw [zero_mul]; exact MvPolynomial.isHomogeneous_one _ _
      · exact MvPolynomial.isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact MvPolynomial.isHomogeneous_zero _ _ _
  · rw [MvPolynomial.coeff_monomial]
    split_ifs
    · intro j
      rw [Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        rw [one_mul]
        have := MvPolynomial.IsHomogeneous.prod (univ : Finset (Fin (k - 1)))
          (fun s => (MvPolynomial.X (v.1, t s) : AuxPoly n)) (fun _ => 1)
          fun s _ => MvPolynomial.isHomogeneous_X _ _
        simpa [vTensor] using this
      · exact MvPolynomial.isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact MvPolynomial.isHomogeneous_zero _ _ _

/-! ### The objects over `ℂ` -/

section Main

variable {n : ℕ}

/-- the generic matrix over `ℂ` -/
noncomputable def Wm (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

/-- `det(I - diag(c) W)` -/
noncomputable def Dp (c : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (1 - Matrix.diagonal (fun i => MvPolynomial.C (c i)) * Wm n).det

/-- `Ψ = Φ_W(1)` over `ℂ` -/
noncomputable def PsiC (n k : ℕ) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  ((phiPoly (k := k) (vTensor n k) res).map (MvPolynomial.map (algebraMap ℚ ℂ))).eval 1

lemma eval_Dp (c : Fin n → ℂ) (x : Fin n × Fin n → ℂ) :
    MvPolynomial.eval x (Dp c) =
      (1 - Matrix.diagonal c * Matrix.of fun i j => x (i, j)).det := by
  rw [Dp, RingHom.map_det]
  congr 1
  ext i j
  simp [Wm, Matrix.diagonal_mul, Matrix.one_apply]

lemma eval_Dp_zero (c : Fin n → ℂ) : MvPolynomial.eval 0 (Dp c) = 1 := by
  rw [eval_Dp]
  have : (Matrix.of fun i j => (0 : Fin n × Fin n → ℂ) (i, j)) = 0 := by ext; rfl
  rw [this, mul_zero, sub_zero, Matrix.det_one]

lemma eval_Dp_single (c : Fin n → ℂ) (i : Fin n) (a : ℂ) :
    MvPolynomial.eval (fun p => if p = (i, i) then a else 0) (Dp c) = 1 - c i * a := by
  classical
  rw [eval_Dp]
  have hm : (1 - Matrix.diagonal c * Matrix.of fun a' b =>
      (fun p : Fin n × Fin n => if p = (i, i) then a else 0) (a', b)) =
      Matrix.diagonal fun j => 1 - c j * (if j = i then a else 0) := by
    ext a' b
    by_cases hab : a' = b
    · subst hab
      by_cases h : a' = i <;> simp [Matrix.diagonal_mul, Matrix.one_apply, h]
    · simp [Matrix.diagonal_mul, hab]
      intro h1 h2
      exact absurd (h1.trans h2.symm) hab
  rw [hm, Matrix.det_diagonal, prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma irreducible_Dp (hn : 1 ≤ n) (c : Fin n → ℂ) (hc0 : ∀ i, c i ≠ 0) :
    Irreducible (Dp c) := by
  classical
  let fwd : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    MvPolynomial.aeval fun p => (if p.1 = p.2 then 1 else 0) -
      MvPolynomial.C (c p.1) * MvPolynomial.X p
  let bwd : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    MvPolynomial.aeval fun p => MvPolynomial.C (c p.1)⁻¹ *
      ((if p.1 = p.2 then 1 else 0) - MvPolynomial.X p)
  have hcc : ∀ i, MvPolynomial.C (c i)⁻¹ * MvPolynomial.C (c i) =
      (1 : MvPolynomial (Fin n × Fin n) ℂ) := fun i => by
    rw [← map_mul, inv_mul_cancel₀ (hc0 i), map_one]
  have h1 : fwd.comp bwd = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro p
    by_cases hp : p.1 = p.2
    · obtain ⟨a, b⟩ := p
      simp only at hp
      subst hp
      simp only [AlgHom.comp_apply, fwd, bwd, MvPolynomial.aeval_X, if_true, map_mul,
        map_sub, map_one, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
      linear_combination (MvPolynomial.X (a, a)) * hcc a
    · simp only [AlgHom.comp_apply, fwd, bwd, MvPolynomial.aeval_X, hp, if_false, map_mul,
        map_sub, map_zero, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
      linear_combination (MvPolynomial.X p) * hcc p.1
  have h2 : bwd.comp fwd = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro p
    by_cases hp : p.1 = p.2
    · obtain ⟨a, b⟩ := p
      simp only at hp
      subst hp
      simp only [AlgHom.comp_apply, fwd, bwd, MvPolynomial.aeval_X, if_true, map_mul,
        map_sub, map_one, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
      linear_combination (MvPolynomial.X (a, a) - 1) * hcc a
    · simp only [AlgHom.comp_apply, fwd, bwd, MvPolynomial.aeval_X, hp, if_false, map_mul,
        map_sub, map_zero, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
      linear_combination (MvPolynomial.X p) * hcc p.1
  let e := AlgEquiv.ofAlgHom fwd bwd h1 h2
  have he : e (Wm n).det = Dp c := by
    change fwd (Wm n).det = _
    rw [AlgHom.map_det, Dp]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp [fwd, Wm, Matrix.diagonal_mul, Matrix.one_apply]
  rw [← he, MulEquiv.irreducible_iff]
  exact det_generic_irreducible ℂ n hn

lemma vanish {k : ℕ} (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (c : Fin n → ℂ) (hc : ∀ i, c i ^ (k - 1) = 1) (x : Fin n × Fin n → ℂ)
    (hx : MvPolynomial.eval x (Dp c) = 0) : MvPolynomial.eval x (PsiC n k res) = 0 := by
  classical
  rw [eval_Dp] at hx
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
  have hFh : ∀ i, ((MvPolynomial.X i ^ (k - 1) -
      (∑ j, MvPolynomial.C (x (i, j)) * MvPolynomial.X j) ^ (k - 1) :
        MvPolynomial (Fin n) ℂ)).IsHomogeneous (k - 1) := by
    intro i
    refine (MvPolynomial.isHomogeneous_X_pow i (k - 1)).sub ?_
    have := (MvPolynomial.IsHomogeneous.sum univ (fun j => MvPolynomial.C (x (i, j)) *
      MvPolynomial.X j) 1 fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _).pow (k - 1)
    rwa [one_mul] at this
  have hzero : ∀ i, MvPolynomial.eval v ((MvPolynomial.X i ^ (k - 1) -
      (∑ j, MvPolynomial.C (x (i, j)) * MvPolynomial.X j) ^ (k - 1) :
        MvPolynomial (Fin n) ℂ)) = 0 := by
    intro i
    have hvi : v i = c i * ∑ j, x (i, j) * v j := by
      have h := congrFun hv i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal, Pi.zero_apply, sub_eq_zero] at h
      rw [h]
      simp [Matrix.mulVec, dotProduct]
    simp only [map_sub, map_pow, MvPolynomial.eval_X, map_sum, map_mul, MvPolynomial.eval_C]
    rw [hvi, mul_pow, hc i, one_mul, sub_self]
  rw [PsiC, phiPoly_vTensor_eval]
  exact (hres.1 (fun i => (MvPolynomial.X i ^ (k - 1) -
      (∑ j, MvPolynomial.C (x (i, j)) * MvPolynomial.X j) ^ (k - 1) :
        MvPolynomial (Fin n) ℂ)) hFh).mp ⟨v, hv0, hzero⟩

lemma PsiC_zero {k : ℕ} (hk : 2 ≤ k) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) : MvPolynomial.eval 0 (PsiC n k res) = 1 := by
  classical
  rw [PsiC, phiPoly_vTensor_eval]
  have hz : ∀ v : ResVar n (fun _ => k - 1),
      MvPolynomial.coeff v.2.1 ((MvPolynomial.X v.1 ^ (k - 1) -
        (∑ j, MvPolynomial.C ((0 : Fin n × Fin n → ℂ) (v.1, j)) * MvPolynomial.X j) ^ (k - 1) :
          MvPolynomial (Fin n) ℂ)) =
        (Int.castRingHom ℂ) (if v.2.1 = Finsupp.single v.1 (k - 1) then 1 else 0) := by
    intro v
    have h0 : (∑ j, MvPolynomial.C ((0 : Fin n × Fin n → ℂ) (v.1, j)) * MvPolynomial.X j :
        MvPolynomial (Fin n) ℂ) = 0 := by simp
    rw [h0, zero_pow (by omega), sub_zero, MvPolynomial.coeff_X_pow]
    by_cases h : v.2.1 = Finsupp.single v.1 (k - 1)
    · rw [if_pos h.symm, if_pos h, map_one]
    · rw [if_neg (Ne.symm h), if_neg h, map_zero]
  simp_rw [hz]
  have h2 := congrArg (Int.castRingHom ℂ) hres.2.1
  rw [map_one, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left] at h2
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  convert h2 using 2 <;> first | exact RingHom.ext_int _ _ | rfl

lemma lam_Dp (c : Fin n → ℂ) (x : Fin n × Fin n → ℂ) :
    lam x (Dp c) = (Matrix.diagonal c * Matrix.of fun i j => x (i, j)).charpolyRev := by
  rw [Dp, AlgHom.map_det]
  unfold Matrix.charpolyRev
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h; simp [lam, Wm, Matrix.diagonal_mul]; ring
  · simp [lam, Wm, Matrix.diagonal_mul, h]; ring

lemma lam_PsiC_natDegree {k : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (x : Fin n × Fin n → ℂ) :
    (lam x (PsiC n k res)).natDegree ≤ n * (k - 1) ^ (n - 1) * (k - 1) := by
  set ΦC := (phiPoly (k := k) (vTensor n k) res).map (MvPolynomial.map (algebraMap ℚ ℂ))
    with hΦC
  have hhom : ∀ j, (ΦC.coeff j).IsHomogeneous (j * (k - 1)) := fun j => by
    rw [hΦC, Polynomial.coeff_map]; exact (phi_GrW n k res j).map _
  have hdeg : ΦC.natDegree ≤ n * (k - 1) ^ (n - 1) :=
    Polynomial.natDegree_map_le.trans (phiPoly_natDegree_le n k hk hn res hres _)
  have hsum : PsiC n k res = ∑ j ∈ range (ΦC.natDegree + 1), ΦC.coeff j := by
    rw [PsiC, ← hΦC, Polynomial.eval_eq_sum_range]; simp
  rw [hsum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  rw [lam_homog x (hhom j)]
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  rw [mem_range] at hj
  exact Nat.mul_le_mul_right _ (by omega)

/-- a product of pairwise non-dividing primes, each dividing `a`, divides `a` -/
lemma prod_dvd_of_primes {ι α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α] [DecidableEq ι]
    (f : ι → α) (hp : ∀ i, Prime (f i)) (hnd : ∀ i j, i ≠ j → ¬ f j ∣ f i) (a : α)
    (ha : ∀ i, f i ∣ a) (s : Finset ι) : ∏ i ∈ s, f i ∣ a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    obtain ⟨d, hd⟩ := ih
    rw [prod_insert hx]
    have hda : f x ∣ (∏ i ∈ s, f i) * d := by rw [← hd]; exact ha x
    rcases (hp x).dvd_or_dvd hda with h | h
    · exfalso
      obtain ⟨b, hb, hxb⟩ := ((hp x).dvd_finsetProd_iff _).mp h
      have hne : b ≠ x := fun hbx => hx (hbx ▸ hb)
      exact hnd b x hne hxb
    · obtain ⟨e, he⟩ := h
      exact ⟨e, by rw [hd, he]; ac_rfl⟩

end Main

end FactorAux

set_option maxHeartbeats 1000000 in
open FactorAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    ((phiPoly (k := k) (vTensor n k) res).map (MvPolynomial.map (algebraMap ℚ ℂ))).comp
        (Polynomial.X ^ (k - 1)) =
      ∏ Ω : Fin n → Fin (k - 1),
        Matrix.charpolyRev
          (Matrix.diagonal (fun i => MvPolynomial.C
              (Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) ^ (Ω i : ℕ))) *
            Matrix.of (fun i j : Fin n => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ))) := by
  classical
  have hr0 : k - 1 ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp (k - 1) hr0
  generalize hξdef : Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) = ξ
  rw [hξdef] at hprim
  have hξ : ξ ^ (k - 1) = 1 := hprim.pow_eq_one
  have hξ0 : ξ ≠ 0 := hprim.ne_zero hr0
  -- the factors
  let c : (Fin n → Fin (k - 1)) → Fin n → ℂ := fun Ω i => ξ ^ (Ω i : ℕ)
  have hc0 : ∀ Ω i, c Ω i ≠ 0 := fun Ω i => pow_ne_zero _ hξ0
  have hcr : ∀ Ω i, c Ω i ^ (k - 1) = 1 := fun Ω i => by
    show (ξ ^ (Ω i : ℕ)) ^ (k - 1) = 1
    rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow]
  set Ψ := PsiC n k res with hΨ
  set G := ∏ Ω : Fin n → Fin (k - 1), Dp (c Ω) with hG
  have hprime : ∀ Ω, Prime (Dp (c Ω)) := fun Ω =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_Dp hn _ (hc0 Ω))
  -- each factor divides `Ψ`
  have hdvd1 : ∀ Ω, Dp (c Ω) ∣ Ψ := fun Ω =>
    irreducible_dvd_of_vanishing _ _ (irreducible_Dp hn _ (hc0 Ω))
      (fun x hx => vanish res hres _ (hcr Ω) x hx)
  -- distinct factors do not divide each other
  have hnassoc : ∀ Ω Ω', Ω ≠ Ω' → ¬ Dp (c Ω') ∣ Dp (c Ω) := by
    intro Ω Ω' hne hdvd
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    obtain ⟨q, hq⟩ := hdvd
    have h := congrArg (MvPolynomial.eval (fun p => if p = (i, i) then (c Ω' i)⁻¹ else 0)) hq
    rw [map_mul, eval_Dp_single, eval_Dp_single, mul_inv_cancel₀ (hc0 Ω' i), sub_self,
      zero_mul, sub_eq_zero] at h
    apply hi
    have h' : c Ω i = c Ω' i := by
      have := congrArg (· * c Ω' i) h
      simp only [one_mul, mul_assoc, inv_mul_cancel₀ (hc0 Ω' i), mul_one] at this
      exact this.symm
    exact Fin.ext (hprim.pow_inj (Ω i).isLt (Ω' i).isLt h')
  -- hence the product divides `Ψ`
  have hGdvd := prod_dvd_of_primes (fun Ω => Dp (c Ω)) hprime hnassoc Ψ hdvd1
  obtain ⟨H, hH⟩ := hGdvd univ
  rw [← hG] at hH
  have hG0 : MvPolynomial.eval 0 G = 1 := by
    rw [hG, map_prod]
    exact prod_eq_one fun Ω _ => eval_Dp_zero _
  have hΨ0 : MvPolynomial.eval 0 Ψ = 1 := PsiC_zero hk res hres
  have hH0 : MvPolynomial.eval 0 H = 1 := by
    have := congrArg (MvPolynomial.eval 0) hH
    rwa [map_mul, hΨ0, hG0, one_mul, eq_comm] at this
  -- along lines through invertible matrices, `H` is constant
  have hline : ∀ x : Fin n × Fin n → ℂ, (Matrix.of fun i j => x (i, j)).det ≠ 0 →
      MvPolynomial.eval x Ψ = MvPolynomial.eval x G := by
    intro x hx
    have hΨl := lam_PsiC_natDegree hk hn res hres x
    rw [← hΨ] at hΨl
    have hdet : ∀ Ω : Fin n → Fin (k - 1),
        (Matrix.diagonal (c Ω) * Matrix.of fun i j => x (i, j)).det ≠ 0 := by
      intro Ω
      rw [Matrix.det_mul, Matrix.det_diagonal]
      exact mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => hc0 Ω i) hx
    have hGdeg : (lam x G).natDegree = n * (k - 1) ^ (n - 1) * (k - 1) := by
      rw [hG, map_prod]
      simp_rw [lam_Dp]
      rw [Polynomial.natDegree_prod _ _ fun Ω _ => charpolyRev_ne_zero _]
      simp_rw [natDegree_charpolyRev _ (hdet _)]
      rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        smul_eq_mul]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    have hl := congrArg (lam x) hH
    rw [map_mul] at hl
    have hzero_fun : (fun q : Fin n × Fin n => (0 : ℂ) * x q) = 0 := by
      funext q; simp
    have hone_fun : (fun q : Fin n × Fin n => (1 : ℂ) * x q) = x := by
      funext q; simp
    have hΨne : lam x Ψ ≠ 0 := by
      intro h0
      have := eval_lam x 0 Ψ
      rw [h0, Polynomial.eval_zero, hzero_fun, hΨ0] at this
      exact zero_ne_one this
    have hGne : lam x G ≠ 0 := fun h0 => hΨne (by rw [hl, h0, zero_mul])
    have hHne : lam x H ≠ 0 := fun h0 => hΨne (by rw [hl, h0, mul_zero])
    have hHdeg : (lam x H).natDegree = 0 := by
      have := Polynomial.natDegree_mul hGne hHne
      rw [← hl] at this
      omega
    have hc := Polynomial.eq_C_of_natDegree_eq_zero hHdeg
    have hH1 : MvPolynomial.eval x H = 1 := by
      have e1 := eval_lam x 1 H
      have e0 := eval_lam x 0 H
      rw [hone_fun] at e1
      rw [hzero_fun, hH0] at e0
      rw [← e1, hc, Polynomial.eval_C]
      rw [hc, Polynomial.eval_C] at e0
      exact e0
    rw [hH, map_mul, hH1, mul_one]
  -- density: `Ψ = G`
  have hΨG : Ψ = G := by
    have hdetW0 : (Wm n).det ≠ 0 := (det_generic_irreducible ℂ n hn).ne_zero
    have hprod : (Ψ - G) * (Wm n).det = 0 := by
      refine MvPolynomial.funext fun x => ?_
      rw [map_mul, map_zero, map_sub]
      have hdx : MvPolynomial.eval x (Wm n).det = (Matrix.of fun i j => x (i, j)).det := by
        rw [RingHom.map_det]; congr 1; ext i j; simp [Wm]
      by_cases hx : (Matrix.of fun i j => x (i, j)).det = 0
      · rw [hdx, hx, mul_zero]
      · rw [hline x hx, sub_self, zero_mul]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdetW0
  -- back to the `ζ`-form via the grading
  set ΦC := (phiPoly (k := k) (vTensor n k) res).map (MvPolynomial.map (algebraMap ℚ ℂ))
    with hΦC
  have hL : GrW 1 (ΦC.comp (Polynomial.X ^ (k - 1))) := by
    intro m
    rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand (by omega)]
    split_ifs with h
    · obtain ⟨q, rfl⟩ := h
      rw [Nat.mul_div_cancel_left q (by omega), mul_one, mul_comm, hΦC, Polynomial.coeff_map]
      exact (phi_GrW n k res q).map _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hR : GrW 1 (∏ Ω : Fin n → Fin (k - 1),
      (Matrix.diagonal (fun i => MvPolynomial.C (c Ω i)) * Wm n).charpolyRev) := by
    refine GrW_prod _ _ fun Ω _ => charpolyRev_GrW _ fun i j => ?_
    simp only [Wm, Matrix.diagonal_mul, Matrix.of_apply]
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have hLe : (ΦC.comp (Polynomial.X ^ (k - 1))).eval 1 = Ψ := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, one_pow, hΨ, PsiC]
  have hRe : (∏ Ω : Fin n → Fin (k - 1),
      (Matrix.diagonal (fun i => MvPolynomial.C (c Ω i)) * Wm n).charpolyRev).eval 1 = G := by
    rw [Polynomial.eval_prod, hG]
    refine prod_congr rfl fun Ω _ => ?_
    rw [Dp]
    unfold Matrix.charpolyRev
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j
    · subst h; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h]
  show ΦC.comp (Polynomial.X ^ (k - 1)) = ∏ Ω : Fin n → Fin (k - 1),
      (Matrix.diagonal (fun i => MvPolynomial.C (c Ω i)) * Wm n).charpolyRev
  ext1 m
  rw [coeff_eq_homComp _ hL, coeff_eq_homComp _ hR, hLe, hRe, hΨG]
