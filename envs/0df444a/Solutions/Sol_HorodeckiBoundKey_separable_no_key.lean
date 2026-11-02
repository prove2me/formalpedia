-- Prove2me | solution 1 for HorodeckiBoundKey.separable_no_key
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:09:23.011188+00:00
-- url     : https://prove2.me/submissions/2ebc60cc-1a93-4970-9cd2-b2d8b7baa262

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open scoped Matrix ComplexOrder ENNReal

namespace SepNoKeyAux

open Matrix
open scoped MatrixOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### Trace inequalities
`psd_re`, `fin`, `cs`, `re_tr_le`, `tr_pow_swap`, `tr_aeval_swap`, `tr_cfc_swap` are copied from the
accepted public solution of `QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_3`
(namespaces `X5B2`, `X5UH`). -/

section TraceIneq
open Matrix Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin _ _) (fin _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]


end TraceIneq

section Proj

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `Re Tr(Π Y) ≤ ‖Y‖₁` for a Hermitian projector `Π`. -/
lemma re_trace_proj_le (Pj Y : Matrix I I ℂ) (hH : Pjᴴ = Pj) (hP : Pj * Pj = Pj) :
    (Pj * Y).trace.re ≤ traceNorm Y := by
  have hY : Y.trace.re ≤ traceNorm Y := by
    have := re_tr_le Y
    rw [← tr_cfc_swap Y Real.sqrt Real.sqrt_zero] at this
    exact this
  set V := (2 : ℂ) • Pj - 1 with hV
  have hVV : V * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH, Matrix.conjTranspose_one]
    simp only [star_ofNat]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, hP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      smul_smul]
    module
  have hVY : (Y * V).trace.re ≤ traceNorm Y := by
    have := re_tr_le (Y * V)
    rw [Matrix.conjTranspose_mul, show Y * V * (Vᴴ * Yᴴ) = Y * (V * Vᴴ) * Yᴴ by
      simp only [Matrix.mul_assoc], hVV, Matrix.mul_one,
      ← tr_cfc_swap Y Real.sqrt Real.sqrt_zero] at this
    exact this
  have e : (Pj * Y).trace = (1/2 : ℂ) * (Y.trace + (Y * V).trace) := by
    rw [Matrix.trace_mul_comm Y V, hV, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul]
    ring
  rw [e]
  simp only [Complex.mul_re, Complex.add_re]
  norm_num
  linarith

end Proj

/-- The cone of (unnormalised) separable operators on `Fin a × Fin b`. -/
def SepCone (a b : ℕ) : AddSubmonoid (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  AddSubmonoid.closure {X | ∃ A : Matrix (Fin a) (Fin a) ℂ, ∃ B : Matrix (Fin b) (Fin b) ℂ,
    A.PosSemidef ∧ B.PosSemidef ∧ X = Matrix.kronecker A B}

lemma alice_step {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) {X : Op (Fin a × Fin b)}
    (hX : X ∈ SepCone a b) :
    ((Matrix.kronecker E (1 : Op (Fin b)) * X : Matrix (Fin h × Fin b) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker E (1 : Op (Fin b)))ᴴ : Op (Fin h × Fin b)) ∈ SepCone h b := by
  induction hX using AddSubmonoid.closure_induction with
  | mem X hX =>
    obtain ⟨A, B, hA, hB, rfl⟩ := hX
    refine AddSubmonoid.subset_closure ⟨E * A * Eᴴ, B, hA.mul_mul_conjTranspose_same E, hB, ?_⟩
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | zero => simp [(SepCone h b).zero_mem]
  | add X Y _ _ hX hY =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact (SepCone h b).add_mem hX hY

lemma bob_step {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) {X : Op (Fin a × Fin b)}
    (hX : X ∈ SepCone a b) :
    ((Matrix.kronecker (1 : Op (Fin a)) E * X : Matrix (Fin a × Fin h) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker (1 : Op (Fin a)) E)ᴴ : Op (Fin a × Fin h)) ∈ SepCone a h := by
  induction hX using AddSubmonoid.closure_induction with
  | mem X hX =>
    obtain ⟨A, B, hA, hB, rfl⟩ := hX
    refine AddSubmonoid.subset_closure ⟨A, E * B * Eᴴ, hA, hB.mul_mul_conjTranspose_same E, ?_⟩
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | zero => simp [(SepCone a h).zero_mem]
  | add X Y _ _ hX hY =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact (SepCone a h).add_mem hX hY

/-- Finite adaptive LOCC maps separable operators to separable operators. -/
lemma locc_sep {a b c d : ℕ} {L : QAlgorithms.Superop (Fin a × Fin b) (Fin c × Fin d)}
    (hL : FiniteLOCC L) : ∀ X ∈ SepCone a b, L X ∈ SepCone c d := by
  induction hL with
  | identity a b => exact fun X hX => hX
  | alice E _ next _ ih =>
    intro X hX
    exact (SepCone _ _).sum_mem fun i _ => ih i _ (alice_step (E i) hX)
  | bob E _ next _ ih =>
    intro X hX
    exact (SepCone _ _).sum_mem fun i _ => ih i _ (bob_step (E i) hX)

/-- Tensor products of positive semidefinite matrices, indexed by tuples, are positive. -/
lemma piTensor_psd {n a : ℕ} (F : Fin n → Op (Fin a)) (hF : ∀ i, (F i).PosSemidef) :
    (Matrix.of fun (x y : Fin n → Fin a) => ∏ i, F i (x i) (y i)).PosSemidef := by
  choose C hC using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hF i).nonneg
  let Tc : Matrix (Fin n → Fin a) (Fin n → Fin a) ℂ := Matrix.of fun x y => ∏ i, C i (x i) (y i)
  have h : (Matrix.of fun (x y : Fin n → Fin a) => ∏ i, F i (x i) (y i)) = Tcᴴ * Tc := by
    ext x y
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Tc]
    have hsummand : ∀ z : Fin n → Fin a, star (∏ i, C i (z i) (x i)) * ∏ i, C i (z i) (y i) =
        ∏ i, (star (C i (z i) (x i)) * C i (z i) (y i)) := by
      intro z
      rw [Finset.prod_mul_distrib]
      congr 1
      exact map_prod (starRingEnd ℂ) _ _
    rw [Finset.sum_congr rfl fun z _ => hsummand z]
    rw [← Fintype.prod_sum (fun i w => star (C i w (x i)) * C i w (y i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hC i, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
    rfl
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self Tc

/-- Tensor powers of a separable state are separable (as operators on the relabelled cut). -/
lemma sep_power {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hsep : HorodeckiBoundKey.IsSeparable ρ) (n : ℕ) :
    Dependency50.P42.dimensionedPower ρ n ∈ SepCone (a ^ n) (b ^ n) := by
  obtain ⟨q, w, A, B, hw, _, hAB, hρ⟩ := hsep
  have hexp : Dependency50.P42.dimensionedPower ρ n = ∑ J : Fin n → Fin q, Matrix.kronecker
      ((Matrix.of fun (x y : Fin n → Fin a) => ∏ i, ((w (J i) : ℂ) • A (J i)) (x i) (y i)).submatrix
        (Dependency50.P42.copyIndex a n).symm (Dependency50.P42.copyIndex a n).symm)
      ((Matrix.of fun (x y : Fin n → Fin b) => ∏ i, B (J i) (x i) (y i)).submatrix
        (Dependency50.P42.copyIndex b n).symm (Dependency50.P42.copyIndex b n).symm) := by
    ext p p'
    simp only [Dependency50.P42.dimensionedPower, Information100.P80.groupedPower, hρ,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply, Matrix.of_apply, smul_eq_mul]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  rw [hexp]
  refine (SepCone _ _).sum_mem fun J _ => AddSubmonoid.subset_closure ⟨_, _, ?_, ?_, rfl⟩
  · exact (piTensor_psd _ fun i => (hAB (J i)).1.1.smul
      (Complex.zero_le_real.mpr (hw (J i)))).submatrix _
  · exact (piTensor_psd _ fun i => (hAB (J i)).2.1).submatrix _

section Core

/-- A matrix with orthonormal columns preserves Euclidean norms. -/
lemma norm_mulVec_of_isometry {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (W : Matrix I J ℂ) (hW : Wᴴ * W = 1) (φ : J → ℂ) :
    ∑ i, ‖(W *ᵥ φ) i‖ ^ 2 = ∑ j, ‖φ j‖ ^ 2 := by
  have h1 : ((∑ i, ‖(W *ᵥ φ) i‖ ^ 2 : ℝ) : ℂ) = star (W *ᵥ φ) ⬝ᵥ (W *ᵥ φ) := by
    push_cast
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  have h2 : ((∑ j, ‖φ j‖ ^ 2 : ℝ) : ℂ) = star φ ⬝ᵥ φ := by
    push_cast
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  have h3 : star (W *ᵥ φ) ⬝ᵥ (W *ᵥ φ) = star φ ⬝ᵥ φ := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hW,
      Matrix.one_mulVec]
  exact_mod_cast h1.trans (h3.trans h2.symm)

/-- The key estimate: `Σ_w |Σ_i [U_iᵀ (x_i ⊗ y_i)]_w|² ≤ (Σ|x|²)(Σ|y|²)`. -/
lemma core {d s t : ℕ} (U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ)
    (x : Fin d → Fin s → ℂ) (y : Fin d → Fin t → ℂ) :
    ∑ w, ‖∑ i, ∑ σ, ∑ τ, x i σ * y i τ * (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w‖ ^ 2
      ≤ (∑ i, ∑ σ, ‖x i σ‖ ^ 2) * (∑ i, ∑ τ, ‖y i τ‖ ^ 2) := by
  set X : Fin d → ℝ := fun i => ∑ σ, ‖x i σ‖ ^ 2
  set Y : Fin d → ℝ := fun i => ∑ τ, ‖y i τ‖ ^ 2
  let φ : Fin d → Fin s × Fin t → ℂ := fun i p => x i p.1 * y i p.2
  let v : Fin d → EuclideanSpace ℂ (Fin s × Fin t) := fun i =>
    WithLp.toLp 2 ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᵀ *ᵥ φ i)
  have hv_apply : ∀ i w, v i w = ∑ σ, ∑ τ, x i σ * y i τ *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w := by
    intro i w
    simp only [v, φ, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_prod_type,
      PiLp.toLp_apply]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hUT : ∀ i, ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᵀ)ᴴ *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᵀ = 1 := by
    intro i
    have h := (U i).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    have e : ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᵀ)ᴴ =
        ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᴴ)ᵀ := by
      ext a b; simp
    rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]
  have hnorm : ∀ i, ‖v i‖ ^ 2 = X i * Y i := by
    intro i
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v, PiLp.toLp_apply]
    rw [norm_mulVec_of_isometry _ (hUT i) (φ i)]
    simp only [φ, Fintype.sum_prod_type, norm_mul, mul_pow, X, Y, Finset.sum_mul_sum]
  have hsum : ∑ w, ‖∑ i, ∑ σ, ∑ τ, x i σ * y i τ *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w‖ ^ 2 = ‖∑ i, v i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [hv_apply]
  rw [hsum]
  have hX : ∀ i, 0 ≤ X i := fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : ∀ i, 0 ≤ Y i := fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hvi : ∀ i, ‖v i‖ = Real.sqrt (X i) * Real.sqrt (Y i) := by
    intro i
    rw [← Real.sqrt_mul (hX i), ← hnorm i, Real.sqrt_sq (norm_nonneg _)]
  have h1 : ‖∑ i, v i‖ ≤ ∑ i, Real.sqrt (X i) * Real.sqrt (Y i) := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => hvi i
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (X i))
    (fun i => Real.sqrt (Y i))
  simp only [Real.sq_sqrt (hX _), Real.sq_sqrt (hY _)] at h2
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, Real.sqrt (X i) * Real.sqrt (Y i)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, X i) * (∑ i, Y i) := h2

end Core

section Private

variable {d s t : ℕ}

/-- Unfolded index `(key_A, (shield_A, (key_B, shield_B)))`. -/
abbrev Ix (d s t : ℕ) := Fin d × (Fin s × (Fin d × Fin t))

/-- The relabelling of the bipartite layout used by `bipartitePrivateRaw`. -/
noncomputable def eIx (d s t : ℕ) : Fin (d * s) × Fin (d * t) ≃ Ix d s t :=
  ((Gap48.P42.localIndex d s).symm.prodCongr (Gap48.P42.localIndex d t).symm).trans
    (Equiv.prodAssoc _ _ _)

lemma bp_eq (ρ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)
    (U : Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    Gap48.P42.bipartitePrivateRaw ρ U =
      (Information100.P67.privateState U ρ).submatrix (eIx d s t) (eIx d s t) := by
  ext x y; rfl

/-- `G : |i,σ,i,τ⟩ ↦ U_i|σ,τ⟩`, so that `γ = G τ G†/d`. -/
def Gm (U : Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    Matrix (Ix d s t) (Fin s × Fin t) ℂ :=
  fun u w => if u.1 = u.2.2.1 then U u.1 (u.2.1, u.2.2.2) w else 0

lemma priv_eq (U : Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)
    (τ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    Information100.P67.privateState U τ = ((d : ℂ)⁻¹) • (Gm U * τ * (Gm U)ᴴ) := by
  ext u v
  simp only [Information100.P67.privateState, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Gm, Matrix.conjTranspose_apply]
  by_cases hu : u.1 = u.2.2.1
  · by_cases hv : v.1 = v.2.2.1
    · simp only [hu, hv, and_self, if_true]
    · simp [hv]
  · simp [hu]

lemma GhG (U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ) :
    (Gm (fun i => (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)))ᴴ *
      Gm (fun i => (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)) = (d : ℂ) • 1 := by
  have hU : ∀ i, (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)ᴴ * U i = 1 := by
    intro i
    have h := (U i).2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  ext w w'
  have key : ∀ i, (∑ p : Fin s × Fin t, star ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) p w) *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) p w')
      = (1 : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) w w' := by
    intro i
    rw [← hU i, Matrix.mul_apply]
    rfl
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Gm, Fintype.sum_prod_type,
    Matrix.smul_apply, smul_eq_mul]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have h1 : ∀ (i : Fin d) (σ : Fin s), (∑ j : Fin d, ∑ τ : Fin t, if i = j then
      star ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w) *
        (if i = j then (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w' else 0) else 0) =
      ∑ τ, star ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w) * (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w' := by
    intro i σ
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  simp only [h1]
  have h2 : ∀ i : Fin d, (∑ σ : Fin s, ∑ τ : Fin t, star ((U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w) *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w') = (1 : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) w w' := by
    intro i
    rw [← key i, Fintype.sum_prod_type]
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Private

section PrivateProps

variable {d s t : ℕ}

lemma trace_submatrix_equiv' {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I I ℂ)
    (e : J ≃ I) : (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

/-- The coerced twists. -/
def Uc (U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ) :
    Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ :=
  fun i => (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)

/-- The twisted maximally-entangled projector `U (P⁺_d ⊗ 1) U†`, in the bipartite layout. -/
noncomputable def Pbp (U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ) :
    Matrix (Fin (d * s) × Fin (d * t)) (Fin (d * s) × Fin (d * t)) ℂ :=
  Gap48.P42.bipartitePrivateRaw (1 : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (Uc U)

variable (U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ)

lemma Pp_eq : Information100.P67.privateState (Uc U) 1 =
    ((d : ℂ)⁻¹) • (Gm (Uc U) * (Gm (Uc U))ᴴ) := by
  rw [priv_eq, Matrix.mul_one]

lemma Pp_idem (hd : 0 < d) :
    Information100.P67.privateState (Uc U) 1 * Information100.P67.privateState (Uc U) 1 =
      Information100.P67.privateState (Uc U) 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Pp_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show Gm (Uc U) * (Gm (Uc U))ᴴ * (Gm (Uc U) * (Gm (Uc U))ᴴ) =
      Gm (Uc U) * ((Gm (Uc U))ᴴ * Gm (Uc U)) * (Gm (Uc U))ᴴ by simp only [Matrix.mul_assoc],
    show (Gm (Uc U))ᴴ * Gm (Uc U) = (d : ℂ) • 1 from GhG U, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, smul_smul]
  congr 1
  field_simp

lemma Pp_herm : (Information100.P67.privateState (Uc U) 1)ᴴ =
    Information100.P67.privateState (Uc U) 1 := by
  rw [Pp_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  simp

lemma Pp_mul_priv (hd : 0 < d) (τ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    Information100.P67.privateState (Uc U) 1 * Information100.P67.privateState (Uc U) τ =
      Information100.P67.privateState (Uc U) τ := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Pp_eq, priv_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show Gm (Uc U) * (Gm (Uc U))ᴴ * (Gm (Uc U) * τ * (Gm (Uc U))ᴴ) =
      Gm (Uc U) * ((Gm (Uc U))ᴴ * Gm (Uc U)) * τ * (Gm (Uc U))ᴴ by simp only [Matrix.mul_assoc],
    show (Gm (Uc U))ᴴ * Gm (Uc U) = (d : ℂ) • 1 from GhG U, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.smul_mul, smul_smul]
  congr 1
  field_simp

lemma priv_trace (hd : 0 < d) (τ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    (Information100.P67.privateState (Uc U) τ).trace = τ.trace := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [priv_eq, Matrix.trace_smul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    show (Gm (Uc U))ᴴ * Gm (Uc U) = (d : ℂ) • 1 from GhG U, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd', one_mul]

/-! Lifting to the bipartite layout. -/

lemma Pbp_idem (hd : 0 < d) : Pbp U * Pbp U = Pbp U := by
  unfold Pbp
  rw [bp_eq, Matrix.submatrix_mul_equiv, Pp_idem U hd]

lemma Pbp_herm : (Pbp U)ᴴ = Pbp U := by
  unfold Pbp
  rw [bp_eq, Matrix.conjTranspose_submatrix, Pp_herm]

lemma Pbp_priv (hd : 0 < d) (τ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    (Pbp U * Gap48.P42.bipartitePrivate τ U).trace = τ.trace := by
  unfold Pbp Gap48.P42.bipartitePrivate
  rw [bp_eq, bp_eq, Matrix.submatrix_mul_equiv, trace_submatrix_equiv']
  exact (congrArg Matrix.trace (Pp_mul_priv U hd τ)).trans (priv_trace U hd τ)

lemma bp_trace (hd : 0 < d) (τ : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    (Gap48.P42.bipartitePrivate τ U).trace = τ.trace := by
  unfold Gap48.P42.bipartitePrivate
  rw [bp_eq, trace_submatrix_equiv']
  exact priv_trace U hd τ

lemma re_trace_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : (Mᴴ * M).trace.re = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Product operators have overlap at most `Tr A Tr B / d` with the twisted projector. -/
lemma Pbp_kron_le (hd : 0 < d) (A : Matrix (Fin (d * s)) (Fin (d * s)) ℂ)
    (B : Matrix (Fin (d * t)) (Fin (d * t)) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Pbp U * Matrix.kronecker A B).trace.re ≤ A.trace.re * B.trace.re / d := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.star_eq_conjTranspose] at hC hD
  set e := eIx d s t with he
  set ls := Gap48.P42.localIndex d s
  set lt := Gap48.P42.localIndex d t
  set G := Gm (Uc U) with hG
  set K : Matrix (Fin (d * s) × Fin (d * t)) (Ix d s t) ℂ :=
    Matrix.of fun kl u => C kl.1 (ls (u.1, u.2.1)) * D kl.2 (lt (u.2.2.1, u.2.2.2)) with hK
  have hXp : Matrix.kronecker A B = (Kᴴ * K).submatrix e e := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hK,
      Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hC, hD, Fintype.sum_prod_type]
    have hx : ls ((e x).1, (e x).2.1) = x.1 := by simp [he, eIx, ls]
    have hx' : lt ((e x).2.2.1, (e x).2.2.2) = x.2 := by simp [he, eIx, lt]
    have hy : ls ((e y).1, (e y).2.1) = y.1 := by simp [he, eIx, ls]
    have hy' : lt ((e y).2.2.1, (e y).2.2.2) = y.2 := by simp [he, eIx, lt]
    rw [hx, hx', hy, hy', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [star_mul']
    ring
  have htr : (Pbp U * Matrix.kronecker A B).trace = (d : ℂ)⁻¹ * ((K * G)ᴴ * (K * G)).trace := by
    unfold Pbp
    rw [bp_eq, hXp, Matrix.submatrix_mul_equiv, trace_submatrix_equiv', Pp_eq, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc, hG]
  -- entries of `K G`
  have hKG : ∀ k l w, (K * G) (k, l) w = ∑ i, ∑ σ, ∑ τ, C k (ls (i, σ)) * D l (lt (i, τ)) *
      (U i : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) (σ, τ) w := by
    intro k l w
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      simp [hK, hG, Gm, Uc]
    · intro j _ hj
      refine Finset.sum_eq_zero fun τ _ => ?_
      simp [hG, Gm, Ne.symm hj]
    · simp
  have hbound : ((K * G)ᴴ * (K * G)).trace.re ≤ A.trace.re * B.trace.re := by
    rw [re_trace_conjTranspose_mul_self, hC, hD, re_trace_conjTranspose_mul_self,
      re_trace_conjTranspose_mul_self, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    simp only [hKG]
    refine (core U (fun i σ => C k (ls (i, σ))) (fun i τ => D l (lt (i, τ)))).trans (le_of_eq ?_)
    congr 1
    · rw [← Fintype.sum_prod_type']
      exact Equiv.sum_comp ls (fun m => ‖C k m‖ ^ 2)
    · rw [← Fintype.sum_prod_type']
      exact Equiv.sum_comp lt (fun m => ‖D l m‖ ^ 2)
  rw [htr]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : ((d : ℂ)⁻¹ * ((K * G)ᴴ * (K * G)).trace).re =
      ((K * G)ᴴ * (K * G)).trace.re / d := by
    rw [show ((d : ℂ)⁻¹) = (((d : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    field_simp
  rw [this]
  exact div_le_div_of_nonneg_right hbound hd'.le

/-- Separable operators have overlap at most `Tr X / d` with the twisted projector. -/
lemma Pbp_sep_le (hd : 0 < d) {X : Matrix (Fin (d * s) × Fin (d * t)) (Fin (d * s) × Fin (d * t)) ℂ}
    (hX : X ∈ SepCone (d * s) (d * t)) : (Pbp U * X).trace.re ≤ X.trace.re / d := by
  induction hX using AddSubmonoid.closure_induction with
  | mem X hX =>
    obtain ⟨A, B, hA, hB, rfl⟩ := hX
    refine (Pbp_kron_le U hd A B hA hB).trans (le_of_eq ?_)
    congr 1
    have hkr : (Matrix.kronecker A B).trace = A.trace * B.trace := Matrix.trace_kronecker A B
    have hAi : A.trace.im = 0 := (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
    have hBi : B.trace.im = 0 := (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm
    rw [hkr, Complex.mul_re, hAi, hBi]
    ring
  | zero => simp
  | add X Y _ _ hX hY =>
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re,
      add_div]
    linarith

end PrivateProps

end SepNoKeyAux

open SepNoKeyAux in
theorem solution {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hsep : HorodeckiBoundKey.IsSeparable ρ) : Gap48.P42.distillableKey ρ = 0 := by
  unfold Gap48.P42.distillableKey
  refine le_antisymm (iSup_le fun r => ?_) (zero_le)
  obtain ⟨r, hr0, hach⟩ := r
  show ENNReal.ofReal r ≤ 0
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
  by_contra hpos
  have hpos : 0 < r := lt_of_not_ge hpos
  obtain ⟨n0, hn0⟩ := hach (1/4) (by norm_num) (r/2) (by linarith)
  obtain ⟨d, s, t, hd, hs, ht, τ, hτ, U, L, hL, hdist, hrate⟩ :=
    hn0 (max n0 1) (le_max_left _ _) (by positivity)
  -- the key dimension is at least two
  have hd2 : 2 ≤ d := by
    by_contra h
    have h1 : d = 1 := by omega
    rw [h1, Nat.cast_one, Real.logb_one, zero_div] at hrate
    linarith
  -- the output of the protocol is separable
  have hX := locc_sep hL _ (sep_power ρ hsep (max n0 1))
  set X := L (Dependency50.P42.dimensionedPower ρ (max n0 1)) with hXdef
  set γ := Gap48.P42.bipartitePrivate τ U with hγ
  have h1 := Pbp_sep_le U hd hX
  have h2 : (Pbp U * γ).trace.re = 1 := by rw [hγ, Pbp_priv U hd τ, hτ.2]; simp
  have h3 : γ.trace.re = 1 := by rw [hγ, bp_trace U hd τ, hτ.2]; simp
  have hneg : traceNorm (γ - X) = traceNorm (X - γ) := by
    unfold traceNorm
    rw [show γ - X = -(X - γ) by abel, Matrix.conjTranspose_neg, neg_mul_neg]
  have h4 : (Pbp U * (γ - X)).trace.re ≤ traceNorm (X - γ) := by
    rw [← hneg]
    exact re_trace_proj_le (Pbp U) (γ - X) (Pbp_herm U) (Pbp_idem U hd)
  have h5 : (X - γ).trace.re ≤ traceNorm (X - γ) := by
    have := re_trace_proj_le (1 : Matrix (Fin (d * s) × Fin (d * t)) (Fin (d * s) × Fin (d * t)) ℂ)
      (X - γ) Matrix.conjTranspose_one (Matrix.one_mul 1)
    rwa [Matrix.one_mul] at this
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, h2] at h4
  rw [Matrix.trace_sub, Complex.sub_re, h3] at h5
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have h6 : X.trace.re / d ≤ 5 / 8 := by
    rcases le_or_gt (X.trace.re) 0 with hneg' | hpos'
    · have : X.trace.re / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg' (by linarith)
      linarith
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  linarith

