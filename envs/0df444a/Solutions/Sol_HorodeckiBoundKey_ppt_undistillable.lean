-- Prove2me | solution 1 for HorodeckiBoundKey.ppt_undistillable
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:22:29.747358+00:00
-- url     : https://prove2.me/submissions/b4b3af91-fb76-455b-9284-9ae007ba3053

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal

namespace PPTAux

open Matrix
open scoped MatrixOrder ComplexConjugate
open QAlgorithms.Papers.Independent.Claimed50.P33 (FiniteState LOCC LocalInstrument liftLocalKraus
  stateEntry RegisterBasis)

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

/-- Partial transpose on party `0` of an operator on a two-party register. -/
def ptm {α : Fin 2 → Type*} (M : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ :=
  fun x y => M (Function.update x 0 (y 0)) (Function.update y 0 (x 0))

/-- The swap of party-0 coordinates, an involution of pairs of basis vectors. -/
def swap0 {α : Fin 2 → Type*} (p : ((i : Fin 2) → α i) × ((i : Fin 2) → α i)) :
    ((i : Fin 2) → α i) × ((i : Fin 2) → α i) :=
  (Function.update p.1 0 (p.2 0), Function.update p.2 0 (p.1 0))

lemma swap0_invol {α : Fin 2 → Type*} : Function.Involutive (swap0 (α := α)) := by
  intro p
  simp [swap0]

lemma lift_apply0 {s r : FiniteState 2} (A : Matrix (Fin (r.dims 0)) (Fin (s.dims 0)) ℂ)
    (z : RegisterBasis (fun i => Fin (r.dims i))) (u : RegisterBasis (fun i => Fin (s.dims i))) :
    liftLocalKraus s r 0 A z u = if (z 1).val = (u 1).val then A (z 0) (u 0) else 0 := by
  unfold liftLocalKraus
  congr 1
  apply propext
  constructor
  · intro h; exact h 1 (by decide)
  · intro h i hi
    fin_cases i
    · exact absurd rfl hi
    · exact h

lemma lift_apply1 {s r : FiniteState 2} (A : Matrix (Fin (r.dims 1)) (Fin (s.dims 1)) ℂ)
    (z : RegisterBasis (fun i => Fin (r.dims i))) (u : RegisterBasis (fun i => Fin (s.dims i))) :
    liftLocalKraus s r 1 A z u = if (z 0).val = (u 0).val then A (z 1) (u 1) else 0 := by
  unfold liftLocalKraus
  congr 1
  apply propext
  constructor
  · intro h; exact h 0 (by decide)
  · intro h i hi
    fin_cases i
    · exact h
    · exact absurd rfl hi

/-- Partial transposition intertwines a conjugation `X ↦ K X K†` with `X ↦ K' X K'†` whenever
`K, K'` satisfy the pointwise compatibility `hK`. -/
lemma ptm_conj {αR αS : Fin 2 → Type*} [∀ i, Fintype (αR i)] [∀ i, DecidableEq (αR i)]
    [∀ i, Fintype (αS i)] [∀ i, DecidableEq (αS i)]
    (K K' : Matrix ((i : Fin 2) → αR i) ((i : Fin 2) → αS i) ℂ)
    (hK : ∀ x y u v, K (Function.update x 0 (y 0)) u * star (K (Function.update y 0 (x 0)) v) =
      K' x (Function.update u 0 (v 0)) * star (K' y (Function.update v 0 (u 0))))
    (X : Matrix ((i : Fin 2) → αS i) ((i : Fin 2) → αS i) ℂ) :
    ptm (K * X * Kᴴ) = K' * ptm X * K'ᴴ := by
  ext x y
  simp only [ptm, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun v u => K' x u * X _ _ * star (K' y v))]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (swap0_invol (α := αS)).toPerm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Function.Involutive.coe_toPerm, swap0]
  have h := hK x y (Function.update p.1 0 (p.2 0)) (Function.update p.2 0 (p.1 0))
  have e1 : Function.update (Function.update p.1 0 (p.2 0)) 0
      ((Function.update p.2 0 (p.1 0)) 0) = p.1 := by simp
  have e2 : Function.update (Function.update p.2 0 (p.1 0)) 0
      ((Function.update p.1 0 (p.2 0)) 0) = p.2 := by simp
  rw [e1, e2] at h
  linear_combination (X (Function.update p.1 0 (p.2 0)) (Function.update p.2 0 (p.1 0))) * h

lemma compat0 {s r : FiniteState 2} (A : Matrix (Fin (r.dims 0)) (Fin (s.dims 0)) ℂ)
    (x y : RegisterBasis (fun i => Fin (r.dims i))) (u v : RegisterBasis (fun i => Fin (s.dims i))) :
    liftLocalKraus s r 0 A (Function.update x 0 (y 0)) u *
        star (liftLocalKraus s r 0 A (Function.update y 0 (x 0)) v) =
      liftLocalKraus s r 0 (A.map star) x (Function.update u 0 (v 0)) *
        star (liftLocalKraus s r 0 (A.map star) y (Function.update v 0 (u 0))) := by
  simp only [lift_apply0, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.map_apply]
  split_ifs <;> simp [mul_comm]

lemma compat1 {s r : FiniteState 2} (A : Matrix (Fin (r.dims 1)) (Fin (s.dims 1)) ℂ)
    (x y : RegisterBasis (fun i => Fin (r.dims i))) (u v : RegisterBasis (fun i => Fin (s.dims i))) :
    liftLocalKraus s r 1 A (Function.update x 0 (y 0)) u *
        star (liftLocalKraus s r 1 A (Function.update y 0 (x 0)) v) =
      liftLocalKraus s r 1 A x (Function.update u 0 (v 0)) *
        star (liftLocalKraus s r 1 A y (Function.update v 0 (u 0))) := by
  simp only [lift_apply1, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  split_ifs <;> simp [mul_comm]

/-- PPT of a two-party finite state (partial transpose on party `0`). -/
def PPT (s : FiniteState 2) : Prop := (ptm s.rho).PosSemidef

lemma ptm_add {α : Fin 2 → Type*} (M N : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    ptm (M + N) = ptm M + ptm N := rfl

lemma ptm_smul {α : Fin 2 → Type*} (c : ℂ) (M : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    ptm (c • M) = c • ptm M := rfl

lemma ptm_sum {α : Fin 2 → Type*} {ι : Type*} (S : Finset ι)
    (M : ι → Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    ptm (∑ z ∈ S, M z) = ∑ z ∈ S, ptm (M z) := by
  ext x y
  simp [ptm, Matrix.sum_apply]

lemma ptm_ptm {α : Fin 2 → Type*} (M : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    ptm (ptm M) = M := by
  ext x y
  simp [ptm]

/-- One local instrument preserves PPT on every branch of positive probability. -/
lemma instr_ppt {s : FiniteState 2} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → FiniteState 2}
    (h : LocalInstrument s p r) (hs : PPT s) (j : Fin k) (hpj : p j ≠ 0) : PPT (r j) := by
  obtain ⟨hp0, _, party, count, A, _, _, hrho⟩ := h
  have e := congrArg ptm (hrho j)
  rw [ptm_smul, ptm_sum] at e
  have hpos : (0 : ℝ) < p j := lt_of_le_of_ne (hp0 j) (Ne.symm hpj)
  have hsum : (∑ z, ptm (liftLocalKraus s (r j) party (A j z) * s.rho *
      (liftLocalKraus s (r j) party (A j z))ᴴ)).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun z _ => ?_
    rcases (show party = 0 ∨ party = 1 by fin_cases party <;> simp) with rfl | rfl
    · rw [ptm_conj _ _ (compat0 (A j z))]
      exact hs.mul_mul_conjTranspose_same _
    · rw [ptm_conj _ _ (compat1 (A j z))]
      exact hs.mul_mul_conjTranspose_same _
  rw [← e] at hsum
  have := hsum.smul (a := (((p j)⁻¹ : ℝ) : ℂ)) (Complex.zero_le_real.mpr (inv_nonneg.mpr hpos.le))
  rw [smul_smul, show (((p j)⁻¹ : ℝ) : ℂ) * (p j : ℂ) = 1 by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpj, Complex.ofReal_one], one_smul] at this
  exact this

/-- Relabel basis vectors along equal dimension vectors. -/
def castIdx {d d' : Fin 2 → ℕ} (h : d' = d) (x : RegisterBasis (fun i => Fin (d i))) :
    RegisterBasis (fun i => Fin (d' i)) :=
  fun i => ⟨(x i).val, by rw [h]; exact (x i).isLt⟩

lemma stateEntry_eq (w t : FiniteState 2) (hd : w.dims = t.dims)
    (x y : RegisterBasis (fun i => Fin (t.dims i))) :
    stateEntry w (fun i => (x i).val) (fun i => (y i).val) = w.rho (castIdx hd x) (castIdx hd y) := by
  unfold stateEntry
  rw [dif_pos ⟨fun i => by rw [hd]; exact (x i).isLt, fun i => by rw [hd]; exact (y i).isLt⟩]
  rfl

lemma stateEntry_self (t : FiniteState 2) (x y : RegisterBasis (fun i => Fin (t.dims i))) :
    stateEntry t (fun i => (x i).val) (fun i => (y i).val) = t.rho x y := by
  unfold stateEntry
  rw [dif_pos ⟨fun i => (x i).isLt, fun i => (y i).isLt⟩]

lemma castIdx_update {d d' : Fin 2 → ℕ} (h : d' = d) (x y : RegisterBasis (fun i => Fin (d i))) :
    castIdx h (Function.update x 0 (y 0)) = Function.update (castIdx h x) 0 (castIdx h y 0) := by
  funext i
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · simp [castIdx]
  · simp only [castIdx, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

/-- The mixing step of the LOCC tree preserves PPT. -/
lemma forget_ppt (t : FiniteState 2) (out : List (ℝ × FiniteState 2))
    (hd : ∀ w ∈ out, w.2.dims = t.dims)
    (hmix : ∀ x y, stateEntry t x y = (out.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum)
    (hw : ∀ w ∈ out, 0 ≤ w.1 ∧ (w.1 = 0 ∨ PPT w.2)) : PPT t := by
  have key : ∀ L : List (ℝ × FiniteState 2), (∀ w ∈ L, w.2.dims = t.dims) →
      (∀ w ∈ L, 0 ≤ w.1 ∧ (w.1 = 0 ∨ PPT w.2)) →
      (Matrix.of fun x y : RegisterBasis (fun i => Fin (t.dims i)) =>
        (L.map fun w => (w.1 : ℂ) * stateEntry w.2
          (fun i => ((Function.update x 0 (y 0)) i).val)
          (fun i => ((Function.update y 0 (x 0)) i).val)).sum).PosSemidef := by
    intro L
    induction L with
    | nil =>
      intro _ _
      have h0 : (Matrix.of fun x y : RegisterBasis (fun i => Fin (t.dims i)) =>
          (([] : List (ℝ × FiniteState 2)).map fun w => (w.1 : ℂ) * stateEntry w.2
            (fun i => ((Function.update x 0 (y 0)) i).val)
            (fun i => ((Function.update y 0 (x 0)) i).val)).sum) = 0 := by
        ext x y; simp
      rw [h0]
      exact Matrix.PosSemidef.zero
    | cons w L ih =>
      intro hdL hwL
      have hw0 := hdL w (List.mem_cons_self)
      have hsplit : (Matrix.of fun x y : RegisterBasis (fun i => Fin (t.dims i)) =>
          ((w :: L).map fun w => (w.1 : ℂ) * stateEntry w.2
            (fun i => ((Function.update x 0 (y 0)) i).val)
            (fun i => ((Function.update y 0 (x 0)) i).val)).sum) =
          (w.1 : ℂ) • (ptm w.2.rho).submatrix (castIdx hw0) (castIdx hw0) +
          Matrix.of fun x y : RegisterBasis (fun i => Fin (t.dims i)) =>
            (L.map fun w => (w.1 : ℂ) * stateEntry w.2
              (fun i => ((Function.update x 0 (y 0)) i).val)
              (fun i => ((Function.update y 0 (x 0)) i).val)).sum := by
        ext x y
        simp only [List.map_cons, List.sum_cons, Matrix.of_apply, Matrix.add_apply,
          Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
        congr 1
        rw [stateEntry_eq w.2 t hw0, castIdx_update, castIdx_update]
        rfl
      rw [hsplit]
      refine Matrix.PosSemidef.add ?_ (ih (fun w hw => hdL w (List.mem_cons_of_mem _ hw))
        (fun w hw => hwL w (List.mem_cons_of_mem _ hw)))
      rcases (hwL w List.mem_cons_self) with ⟨hnn, h0 | hppt⟩
      · rw [h0]; simpa using (Matrix.PosSemidef.zero :
          (0 : Matrix (RegisterBasis (fun i => Fin (t.dims i)))
            (RegisterBasis (fun i => Fin (t.dims i))) ℂ).PosSemidef)
      · exact (hppt.submatrix _).smul (Complex.zero_le_real.mpr hnn)
  have e : ptm t.rho = Matrix.of fun x y : RegisterBasis (fun i => Fin (t.dims i)) =>
      (out.map fun w => (w.1 : ℂ) * stateEntry w.2
        (fun i => ((Function.update x 0 (y 0)) i).val)
        (fun i => ((Function.update y 0 (x 0)) i).val)).sum := by
    ext x y
    simp only [ptm, Matrix.of_apply]
    rw [← stateEntry_self, hmix]
  unfold PPT
  rw [e]
  exact key out hd hw

/-- Every positive-weight output of a two-party LOCC tree started from a PPT state is PPT. -/
lemma locc_ppt {s : FiniteState 2} {out : List (ℝ × FiniteState 2)} (h : LOCC s out) :
    PPT s → ∀ w ∈ out, 0 ≤ w.1 ∧ (w.1 = 0 ∨ PPT w.2) := by
  induction h with
  | stop s =>
    intro hs w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨zero_le_one, Or.inr hs⟩
  | step s k p r h next hn ih =>
    intro hs w hw
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hw
    obtain ⟨j, w', hw', rfl⟩ := hw
    have hp0 : 0 ≤ p j := h.1 j
    by_cases hpj : p j = 0
    · simp [hpj]
    · obtain ⟨h1, h2⟩ := ih j (instr_ppt h hs j hpj) w' hw'
      refine ⟨mul_nonneg hp0 h1, ?_⟩
      rcases h2 with h2 | h2
      · left; simp [h2]
      · right; exact h2
  | forget s t out h hd hmix ih =>
    intro hs w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨zero_le_one, Or.inr (forget_ppt t out hd hmix (ih hs))⟩

/-! ### PPT of the input copies -/

/-- Tensor products (over copies) of positive semidefinite matrices are positive. -/
lemma piTensor_psd {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Fin n → Matrix ι ι ℂ)
    (hF : ∀ i, (F i).PosSemidef) :
    (Matrix.of fun (x y : Fin n → ι) => ∏ i, F i (x i) (y i)).PosSemidef := by
  choose C hC using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hF i).nonneg
  let Tc : Matrix (Fin n → ι) (Fin n → ι) ℂ := Matrix.of fun x y => ∏ i, C i (x i) (y i)
  have h : (Matrix.of fun (x y : Fin n → ι) => ∏ i, F i (x i) (y i)) = Tcᴴ * Tc := by
    ext x y
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Tc]
    have hsummand : ∀ z : Fin n → ι, star (∏ i, C i (z i) (x i)) * ∏ i, C i (z i) (y i) =
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

lemma partyPower_psd {D : Fin 2 → ℕ}
    {M : Matrix (Gap48.P42.PartyBasis D) (Gap48.P42.PartyBasis D) ℂ} (hM : M.PosSemidef) (n : ℕ) :
    (Gap48.P42.partyPower M n).PosSemidef := by
  have h := (piTensor_psd (fun _ : Fin n => M) (fun _ => hM)).submatrix
    (fun (x : Gap48.P42.PartyBasis (fun k => D k ^ n)) (t : Fin n) =>
      (fun k => (Dependency50.P42.copyIndex (D k) n).symm (x k) t : Gap48.P42.PartyBasis D))
  convert h using 1
  ext x y
  rfl

lemma ptm_partyPower {D : Fin 2 → ℕ}
    (M : Matrix (Gap48.P42.PartyBasis D) (Gap48.P42.PartyBasis D) ℂ) (n : ℕ) :
    ptm (Gap48.P42.partyPower M n) = Gap48.P42.partyPower (ptm M) n := by
  ext x y
  simp only [ptm, Gap48.P42.partyPower]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  · funext k
    rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
    · simp
    · simp [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  · funext k
    rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
    · simp
    · simp [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

lemma ptm_asTwoParties {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ptm (Gap48.P42.asTwoParties ρ) = (Entanglement.partialTransposeFirst ρ).submatrix
      (fun x => (x 0, x 1)) (fun x => (x 0, x 1)) := by
  ext x y
  simp [ptm, Gap48.P42.asTwoParties, Entanglement.partialTransposeFirst,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

/-! ### The target `m` Bell pairs -/

lemma bell_vec (x : Fin 2 → Fin 2) :
    Gap48.P42.twoLabelGHZVector 2 2 0 1 false x =
      if x 0 = x 1 then ((Real.sqrt 2 : ℂ))⁻¹ else 0 := by
  simp only [Gap48.P42.twoLabelGHZVector, PiLp.toLp_apply, Fin.forall_fin_two]
  generalize x 0 = u
  generalize x 1 = v
  fin_cases u <;> fin_cases v <;> simp

lemma ghz_apply (m : ℕ) (x y : Fin 2 → Fin (2 ^ m)) :
    Gap48.P42.ghzCopies 2 m x y = if x 0 = x 1 ∧ y 0 = y 1 then ((2 : ℂ) ^ m)⁻¹ else 0 := by
  simp only [Gap48.P42.ghzCopies, Gap48.P42.partyPower, pureDensity, Matrix.of_apply, bell_vec]
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hterm : ∀ t : Fin m,
      ((if (Dependency50.P42.copyIndex 2 m).symm (x 0) t = (Dependency50.P42.copyIndex 2 m).symm (x 1) t
        then ((Real.sqrt 2 : ℂ))⁻¹ else 0) *
      (starRingEnd ℂ) (if (Dependency50.P42.copyIndex 2 m).symm (y 0) t =
        (Dependency50.P42.copyIndex 2 m).symm (y 1) t then ((Real.sqrt 2 : ℂ))⁻¹ else 0)) =
      if (Dependency50.P42.copyIndex 2 m).symm (x 0) t = (Dependency50.P42.copyIndex 2 m).symm (x 1) t ∧
        (Dependency50.P42.copyIndex 2 m).symm (y 0) t = (Dependency50.P42.copyIndex 2 m).symm (y 1) t
      then (1 / 2 : ℂ) else 0 := by
    intro t
    split_ifs with h1 h3 h3 <;> simp_all
  simp only [hterm]
  rw [Finset.prod_ite]
  have hfilter : ∀ (P : Fin m → Prop) [DecidablePred P],
      (∏ t ∈ Finset.univ.filter (fun t => ¬ P t), (0 : ℂ)) = if ∀ t, P t then 1 else 0 := by
    intro P _
    split_ifs with hP
    · have : Finset.univ.filter (fun t => ¬ P t) = ∅ := by
        ext t; simp [hP t]
      rw [this, Finset.prod_empty]
    · simp only [not_forall] at hP
      obtain ⟨t, ht⟩ := hP
      exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) rfl
  rw [hfilter]
  have hiff : (∀ t, (Dependency50.P42.copyIndex 2 m).symm (x 0) t =
        (Dependency50.P42.copyIndex 2 m).symm (x 1) t ∧
      (Dependency50.P42.copyIndex 2 m).symm (y 0) t = (Dependency50.P42.copyIndex 2 m).symm (y 1) t) ↔
      (x 0 = x 1 ∧ y 0 = y 1) := by
    constructor
    · intro h
      exact ⟨(Dependency50.P42.copyIndex 2 m).symm.injective (funext fun t => (h t).1),
        (Dependency50.P42.copyIndex 2 m).symm.injective (funext fun t => (h t).2)⟩
    · rintro ⟨h1, h2⟩ t
      exact ⟨by rw [h1], by rw [h2]⟩
  by_cases hxy : x 0 = x 1 ∧ y 0 = y 1
  · rw [if_pos (hiff.mpr hxy), if_pos hxy, mul_one]
    have : Finset.univ.filter (fun t : Fin m => (Dependency50.P42.copyIndex 2 m).symm (x 0) t =
        (Dependency50.P42.copyIndex 2 m).symm (x 1) t ∧
      (Dependency50.P42.copyIndex 2 m).symm (y 0) t = (Dependency50.P42.copyIndex 2 m).symm (y 1) t)
        = Finset.univ := by
      ext t; simp [(hiff.mpr hxy) t]
    rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [div_pow, one_pow, one_div]
  · rw [if_neg (fun h => hxy (hiff.mp h)), if_neg hxy, mul_zero]

section Swap

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The swap of the two parties' labels. -/
def Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ :=
  Matrix.of fun x y => if y 0 = x 1 ∧ y 1 = x 0 then 1 else 0

lemma Fsw_herm : (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ)ᴴ = Fsw := by
  ext x y
  simp only [Fsw, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : x 0 = y 1 ∧ x 1 = y 0
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩, star_one]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩), star_zero]

lemma Fsw_sq : (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ) * Fsw = 1 := by
  ext x z
  simp only [Fsw, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ![x 1, x 0]]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_self, if_true, one_mul]
    by_cases h : x = z
    · subst h; simp
    · simp only [h, if_false]
      have h' : ¬(z 0 = x 0 ∧ z 1 = x 1) := fun h' =>
        h (funext fun i => by fin_cases i <;> simp [h'.1, h'.2])
      simp [h']
  · intro y _ hy
    rw [if_neg, zero_mul]
    intro h'
    exact hy (funext fun i => by fin_cases i <;> simp [h'.1, h'.2])
  · simp

lemma one_sub_Fsw_psd : (1 - (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ))
  have e : (1 - (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ))ᴴ * (1 - Fsw) = (2 : ℂ) • (1 - Fsw) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Fsw_herm, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Fsw_sq,
      two_smul]
    abel
  rw [e] at h
  have := h.smul (a := ((1/2 : ℝ) : ℂ)) (Complex.zero_le_real.mpr (by norm_num))
  rwa [smul_smul, show ((1/2 : ℝ) : ℂ) * 2 = 1 by push_cast; norm_num, one_smul] at this

lemma re_trace_Fsw_le {Y : Matrix (Fin 2 → T) (Fin 2 → T) ℂ} (hY : Y.PosSemidef) :
    (Fsw * Y).trace.re ≤ Y.trace.re := by
  have hP : (1 - (Fsw : Matrix (Fin 2 → T) (Fin 2 → T) ℂ)).PosSemidef := one_sub_Fsw_psd
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have h0 : 0 ≤ ((1 - Fsw) * Y).trace.re := by
    rw [hB, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp (hY.mul_mul_conjTranspose_same B).trace_nonneg).1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h0
  linarith

end Swap

/-- `Tr(AB) = Tr(Aᵀᵖ Bᵀᵖ)` for the partial transpose. -/
lemma trace_ptm {α : Fin 2 → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (A B : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) :
    (ptm A * ptm B).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Equiv.sum_comp (swap0_invol (α := α)).toPerm (fun p => A p.1 p.2 * B p.2 p.1)

lemma trace_ptm_self {α : Fin 2 → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (A : Matrix ((i : Fin 2) → α i) ((i : Fin 2) → α i) ℂ) : (ptm A).trace = A.trace := by
  simp [Matrix.trace, ptm]

lemma count_diag (K : ℕ) : (∑ y : Fin 2 → Fin K, if y 0 = y 1 then (1 : ℂ) else 0) = K := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ => Fin K)).symm]
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma ptm_ghz (m : ℕ) : ptm (Gap48.P42.ghzCopies 2 m) = ((2 : ℂ) ^ m)⁻¹ • Fsw := by
  ext x y
  simp only [ptm, ghz_apply, Matrix.smul_apply, Fsw, Matrix.of_apply, smul_eq_mul,
    Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  by_cases h : y 0 = x 1 ∧ x 0 = y 1
  · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩, mul_one]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩), mul_zero]

lemma ghz_herm (m : ℕ) : (Gap48.P42.ghzCopies 2 m)ᴴ = Gap48.P42.ghzCopies 2 m := by
  ext x y
  simp only [Matrix.conjTranspose_apply, ghz_apply]
  by_cases h : y 0 = y 1 ∧ x 0 = x 1
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]

lemma ghz_idem (m : ℕ) : Gap48.P42.ghzCopies 2 m * Gap48.P42.ghzCopies 2 m =
    Gap48.P42.ghzCopies 2 m := by
  ext x z
  simp only [Matrix.mul_apply, ghz_apply]
  have hK : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases hx : x 0 = x 1
  · by_cases hz : z 0 = z 1
    · rw [if_pos ⟨hx, hz⟩]
      have : ∀ y : Fin 2 → Fin (2 ^ m), ((if x 0 = x 1 ∧ y 0 = y 1 then ((2 : ℂ) ^ m)⁻¹ else 0) *
          if y 0 = y 1 ∧ z 0 = z 1 then ((2 : ℂ) ^ m)⁻¹ else 0) =
          ((2 : ℂ) ^ m)⁻¹ * ((2 : ℂ) ^ m)⁻¹ * (if y 0 = y 1 then 1 else 0) := by
        intro y; by_cases hy : y 0 = y 1 <;> simp [hx, hz, hy]
      rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.mul_sum, count_diag]
      push_cast
      field_simp
    · rw [if_neg (fun h => hz h.2)]
      exact Finset.sum_eq_zero fun y _ => by simp [hz]
  · rw [if_neg (fun h => hx h.1)]
    exact Finset.sum_eq_zero fun y _ => by simp [hx]

lemma ghz_trace (m : ℕ) : (Gap48.P42.ghzCopies 2 m).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, ghz_apply, and_self]
  have : ∀ y : Fin 2 → Fin (2 ^ m), (if y 0 = y 1 then ((2 : ℂ) ^ m)⁻¹ else 0) =
      ((2 : ℂ) ^ m)⁻¹ * (if y 0 = y 1 then 1 else 0) := by
    intro y; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.mul_sum, count_diag]
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)

/-- A PPT state has overlap at most `2^{-m}` with `m` Bell pairs. -/
lemma ghz_overlap (m : ℕ) (σ : Matrix (Fin 2 → Fin (2 ^ m)) (Fin 2 → Fin (2 ^ m)) ℂ)
    (hσ : (ptm σ).PosSemidef) :
    (Gap48.P42.ghzCopies 2 m * σ).trace.re ≤ σ.trace.re / 2 ^ m := by
  rw [← trace_ptm, ptm_ghz, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h1 := re_trace_Fsw_le hσ
  rw [trace_ptm_self] at h1
  rw [show ((2 : ℂ) ^ m)⁻¹ = (((2 : ℝ) ^ m)⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end PPTAux

open PPTAux in
theorem solution {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hρ : IsDensityMatrix ρ) (hppt : (Entanglement.partialTransposeFirst ρ).PosSemidef) :
    Gap48.P42.bipartiteDistillable ρ = 0 := by
  unfold Gap48.P42.bipartiteDistillable Gap48.P42.distillableGHZ
  refine le_antisymm (iSup_le fun r => ?_) zero_le
  obtain ⟨r, hr0, hach⟩ := r
  show ENNReal.ofReal r ≤ 0
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
  by_contra hpos
  have hpos : 0 < r := lt_of_not_ge hpos
  obtain ⟨n0, hn0⟩ := hach (1/4) (by norm_num) (r/2) (by linarith)
  obtain ⟨m, σ, hconv, hdist, hrate⟩ := hn0 (max n0 1) (le_max_left _ _) (by positivity)
  obtain ⟨hD, hE, hrho, hsigma, hL⟩ := hconv
  -- the input is PPT
  have hin : PPT ⟨_, hD, Gap48.P42.partyPower (Gap48.P42.asTwoParties ρ) (max n0 1), hrho⟩ := by
    unfold PPT
    show (ptm (Gap48.P42.partyPower (Gap48.P42.asTwoParties ρ) (max n0 1))).PosSemidef
    rw [ptm_partyPower, ptm_asTwoParties]
    exact partyPower_psd (hppt.submatrix _) _
  -- hence so is the output
  have hout := locc_ppt hL hin _ (List.mem_singleton_self _)
  have hσ : (ptm σ).PosSemidef := by
    rcases hout.2 with h | h
    · norm_num at h
    · exact h
  -- at least one Bell pair is produced
  have hm : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0, Nat.cast_zero, zero_div] at hrate
    linarith
  -- overlap bounds
  have hK : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have h1 := ghz_overlap m σ hσ
  have htrσ : σ.trace.re = 1 := by rw [hsigma.2]; simp
  rw [htrσ] at h1
  have h2 : (Gap48.P42.ghzCopies 2 m * (Gap48.P42.ghzCopies 2 m - σ)).trace.re ≤
      traceNorm (Gap48.P42.ghzCopies 2 m - σ) :=
    re_trace_proj_le _ _ (ghz_herm m) (ghz_idem m)
  rw [Matrix.mul_sub, ghz_idem, Matrix.trace_sub, Complex.sub_re, ghz_trace] at h2
  have hneg : traceNorm (Gap48.P42.ghzCopies 2 m - σ) = traceNorm (σ - Gap48.P42.ghzCopies 2 m) := by
    unfold traceNorm
    rw [show Gap48.P42.ghzCopies 2 m - σ = -(σ - Gap48.P42.ghzCopies 2 m) by abel,
      Matrix.conjTranspose_neg, neg_mul_neg]
  rw [hneg] at h2
  have h3 : 1 / (2 : ℝ) ^ m ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  simp only [Complex.one_re] at h2
  linarith
