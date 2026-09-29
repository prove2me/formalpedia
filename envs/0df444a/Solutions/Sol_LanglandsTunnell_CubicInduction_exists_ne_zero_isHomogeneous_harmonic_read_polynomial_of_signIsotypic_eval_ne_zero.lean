-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8cffd5cf-72ff-5502-8f3e-2505002418e1

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero

set_option autoImplicit false

namespace WsE
namespace PN

open MvPolynomial

noncomputable section

open scoped Classical

abbrev R3 := MvPolynomial (Fin 3) ℂ
abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ
abbrev MFn := Matrix (Fin 3) (Fin 3) ℝ → ℂ

theorem f01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
theorem f02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
theorem f10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
theorem f12 : ((1 : Fin 3) = 2) = False := eq_false (by decide)
theorem f20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
theorem f21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide

def ColOrth (o : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0

theorem colOrth_iff (o : Matrix (Fin 3) (Fin 3) ℝ) : ColOrth o ↔ o.transpose * o = 1 := by
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply] using h i j
  · intro h i j
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) h
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem det_ne_zero_of_colOrth (o : Matrix (Fin 3) (Fin 3) ℝ) (h : ColOrth o) : o.det ≠ 0 := by
  have h1 := congrArg Matrix.det ((colOrth_iff o).mp h)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  intro h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

theorem colOrth_mul (o H : Matrix (Fin 3) (Fin 3) ℝ) (ho : ColOrth o) (hH : ColOrth H) : ColOrth (o * H) := by
  rw [colOrth_iff] at ho hH ⊢
  calc (o * H).transpose * (o * H) = H.transpose * (o.transpose * o) * H := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ho, Matrix.mul_one, hH]

def ej (j : Fin 3) : Fin 3 → ℝ := fun t => if t = j then 1 else 0

def refl (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r s => (if r = s then 1 else 0) - 2 * v r * v s / (∑ t : Fin 3, v t ^ 2)

theorem refl_colOrth (v : Fin 3 → ℝ) (hv : (∑ t : Fin 3, v t ^ 2) ≠ 0) : ColOrth (refl v) := by
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by simpa [Fin.sum_univ_three] using hv
  intro i j
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
    (simp [refl, Fin.sum_univ_three]; field_simp; ring)

def HH (j : Fin 3) (w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if w = ej j then 1 else refl (fun t => ej j t - w t)

theorem colOrth_one : ColOrth (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [colOrth_iff, Matrix.transpose_one, Matrix.one_mul]

theorem sum_sq_sub (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) :
    (∑ t : Fin 3, (ej j t - w t) ^ 2) = 2 * (1 - w j) := by
  simp only [Fin.sum_univ_three] at hw
  rcases fin3_cases j with rfl | rfl | rfl <;>
    (simp [Fin.sum_univ_three, ej]; linear_combination hw)

theorem ne_ej_aux (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) (hne : w ≠ ej j) :
    w j ≠ 1 := by
  intro h1
  apply hne
  have hs := sum_sq_sub j w hw
  rw [h1, sub_self, mul_zero] at hs
  have h0 : ∀ t, (ej j t - w t) ^ 2 = 0 := fun t =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg (ej j t - w t))).mp hs t (Finset.mem_univ t)
  funext t
  have := h0 t
  rw [sq_eq_zero_iff, sub_eq_zero] at this
  exact this.symm

theorem HH_colOrth (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) : ColOrth (HH j w) := by
  unfold HH
  split_ifs with h
  · exact colOrth_one
  · apply refl_colOrth
    rw [sum_sq_sub j w hw]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr (ne_ej_aux j w hw h).symm)

theorem HH_col (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) (r : Fin 3) :
    HH j w r j = w r := by
  unfold HH
  split_ifs with h
  · rw [h]; simp [ej, Matrix.one_apply]
  · have hj : (1 : ℝ) - w j ≠ 0 := sub_ne_zero.mpr (ne_ej_aux j w hw h).symm
    show (if r = j then 1 else 0) - 2 * (ej j r - w r) * (ej j j - w j) / (∑ t : Fin 3, (ej j t - w t) ^ 2) = w r
    rw [sum_sq_sub j w hw]
    have hjj : ej j j = 1 := by simp [ej]
    rw [hjj]
    by_cases hr : r = j
    · subst hr
      rw [if_pos rfl, hjj]
      field_simp
      ring
    · rw [if_neg hr]
      have : ej j r = 0 := by simp [ej, hr]
      rw [this]
      field_simp
      ring

theorem HH_det_ne_zero (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) : (HH j w).det ≠ 0 :=
  det_ne_zero_of_colOrth _ (HH_colOrth j w hw)

theorem mem_O3_iff (m : Matrix (Fin 3) (Fin 3) ℝ) : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ ↔ ColOrth m := by
  rw [Matrix.mem_orthogonalGroup_iff', colOrth_iff]

theorem det_ne_zero_of_mem_O3 {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    m.det ≠ 0 :=
  det_ne_zero_of_colOrth m ((mem_O3_iff m).1 hm)

theorem eval_smul_of_isHomogeneous {σ : Type*} {p : MvPolynomial σ ℂ} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ)
    (c : ℂ) (x : σ → ℂ) :
    eval (fun i => c * x i) p = c ^ ℓ * eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : ∑ i ∈ d.support, d i = ℓ := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl fun i _ => mul_pow c (x i) (d i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hw]
  ring

theorem exists_real_eval_ne_zero {p : MvPolynomial (Fin 3) ℂ} (hp : p ≠ 0) :
    ∃ x : Fin 3 → ℝ, eval (fun a => ((x a : ℝ) : ℂ)) p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  refine MvPolynomial.funext_set (fun _ : Fin 3 => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun z hz => ?_
  rw [map_zero]
  have hz' : ∀ a : Fin 3, ∃ r : ℝ, (r : ℂ) = z a := fun a => hz a (Set.mem_univ a)
  choose x hx using hz'
  have : z = fun a => ((x a : ℝ) : ℂ) := funext fun a => (hx a).symm
  rw [this]
  exact h x

theorem exists_unit_eval_ne_zero {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ} (hp : p ≠ 0) (hhom : p.IsHomogeneous ℓ) :
    ∃ w : Fin 3 → ℝ, (∑ t : Fin 3, w t ^ 2) = 1 ∧ eval (fun a => ((w a : ℝ) : ℂ)) p ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero hp
  have hs0 : 0 ≤ ∑ t : Fin 3, x t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg (x t)
  set n : ℝ := Real.sqrt (∑ t : Fin 3, x t ^ 2) with hn
  have hn2 : n ^ 2 = ∑ t : Fin 3, x t ^ 2 := Real.sq_sqrt hs0
  by_cases h0 : n = 0
  · have hx0 : ∀ t, x t = 0 := by
      have hsum : ∑ t : Fin 3, x t ^ 2 = 0 := by rw [← hn2, h0]; ring
      intro t
      exact pow_eq_zero_iff two_ne_zero |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (x t)).1 hsum t (Finset.mem_univ t))
    refine ⟨ej 0, by simp [ej], fun hw => hx ?_⟩
    have : (fun a : Fin 3 => ((x a : ℝ) : ℂ)) = fun a => (0 : ℂ) * ((ej 0 a : ℝ) : ℂ) := by
      funext a; rw [hx0 a]; simp
    rw [this, eval_smul_of_isHomogeneous hhom, hw, mul_zero]
  · refine ⟨fun t => n⁻¹ * x t, ?_, fun hw => hx ?_⟩
    · calc ∑ t : Fin 3, (n⁻¹ * x t) ^ 2 = n⁻¹ ^ 2 * ∑ t : Fin 3, x t ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => mul_pow _ _ _
        _ = 1 := by rw [← hn2]; field_simp
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast h0
      have : (fun a : Fin 3 => ((x a : ℝ) : ℂ)) = fun a => (n : ℂ) * (((n⁻¹ * x a : ℝ)) : ℂ) := by
        funext a; push_cast; rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [this, eval_smul_of_isHomogeneous hhom, hw, mul_zero]

theorem detC_eq (o : Matrix (Fin 3) (Fin 3) ℝ) :
    (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det = ((o.det : ℝ) : ℂ) := by
  have : (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)) = (Complex.ofRealHom : ℝ →+* ℂ).mapMatrix o := rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem eval_realise_col (o : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (q : MvPolynomial (Fin 3) ℂ) :
    eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
      (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q) =
    eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) q := by
  have hr : aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q =
      rename (fun a : Fin 3 => (a, j)) q := by
    rw [rename_eq_aeval]; rfl
  rw [hr, eval_rename]
  rfl

theorem neg_mem_O3 {r : Matrix (Fin 3) (Fin 3) ℝ} (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    -r ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hr ⊢
  rw [Matrix.transpose_neg, neg_mul_neg, hr]

theorem mod_two_eq_of_neg_one_pow_eq {m n : ℕ} (h : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n) : m % 2 = n % 2 := by
  rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n] at h
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> rcases Nat.mod_two_eq_zero_or_one n with hn' | hn' <;>
    rw [hm, hn'] at h ⊢
  all_goals norm_num at h

theorem hasDerivAt_eval {σ : Type} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (x : ℝ → σ → ℂ) (x' : σ → ℂ) (t₀ : ℝ) (hx : ∀ k, HasDerivAt (fun t => x t k) (x' k) t₀) :
    HasDerivAt (fun t => eval (x t) P) (∑ k, eval (x t₀) (pderiv k P) * x' k) t₀ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const t₀ a
  | add p q hp hq =>
    simp only [map_add]
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | skip
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  | mul_X p k hp =>
    simp only [map_mul, eval_X]
    have := hp.mul (hx k)
    convert this using 1
    all_goals first | rfl | skip
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X]
    have h1 : ∀ k' : σ, (eval (x t₀) (pderiv k' p) * x t₀ k +
        eval (x t₀) p * eval (x t₀) (Pi.single (M := fun _ => MvPolynomial σ ℂ) k' 1 k)) * x' k' =
        eval (x t₀) (pderiv k' p) * x' k' * x t₀ k + (if k = k' then eval (x t₀) p * x' k' else 0) := by
      intro k'
      rw [Pi.single_apply]
      split_ifs with h
      · rw [map_one]; ring
      · rw [map_zero]; ring
    rw [Finset.sum_congr rfl (fun k' _ => h1 k'), Finset.sum_add_distrib, Finset.sum_ite_eq,
      ← Finset.sum_mul]
    simp

def pt (o : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

def readL : R9 →ₗ[ℂ] MFn where
  toFun P := fun m => eval (pt m) P
  map_add' P Q := by funext m; simp
  map_smul' c P := by funext m; simp [smul_eq_mul]

theorem readL_apply (P : R9) (m : Matrix (Fin 3) (Fin 3) ℝ) : readL P m = eval (pt m) P := rfl

def subF (r : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → R9 :=
  fun ij => ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)

def subR (r : Fin 3 → Fin 3 → ℝ) (P : R9) : R9 := MvPolynomial.aeval (subF r) P

theorem eval_subR (r : Fin 3 → Fin 3 → ℝ) (P : R9) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    eval (pt m) (subR r P) = eval (pt (m * Matrix.of r)) P := by
  rw [subR, aeval_eq_bind₁]
  show eval₂Hom (RingHom.id ℂ) (pt m) (bind₁ (subF r) P) = _
  rw [eval₂Hom_bind₁]
  show eval (fun ij => eval (pt m) (subF r ij)) P = eval (pt (m * Matrix.of r)) P
  have hfun : (fun ij => eval (pt m) (subF r ij)) = pt (m * Matrix.of r) := by
    funext ij
    simp only [subF, map_sum, map_mul, eval_X, eval_C, pt, Matrix.mul_apply, Matrix.of_apply]
    push_cast
    rfl
  rw [hfun]

theorem readL_subR (r : Fin 3 → Fin 3 → ℝ) (P : R9) :
    (fun m => readL P (m * Matrix.of r)) = readL (subR r P) := by
  funext m; rw [readL_apply, readL_apply, eval_subR]

theorem totalDegree_subR_le (r : Fin 3 → Fin 3 → ℝ) (P : R9) : (subR r P).totalDegree ≤ P.totalDegree := by
  classical
  have hlin : ∀ ij, (subF r ij).totalDegree ≤ 1 := by
    intro ij
    refine totalDegree_finsetSum_le fun c _ => ?_
    calc (MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ) : R9).totalDegree
        ≤ (MvPolynomial.X (ij.1, c) : R9).totalDegree + (MvPolynomial.C ((r c ij.2 : ℝ) : ℂ) : R9).totalDegree :=
          totalDegree_mul _ _
      _ ≤ 1 := by rw [totalDegree_X, totalDegree_C]
  rw [subR, aeval_def, MvPolynomial.eval₂_eq]
  refine totalDegree_finsetSum_le fun d hd => ?_
  calc ((algebraMap ℂ R9) (coeff d P) * ∏ i ∈ d.support, subF r i ^ d i).totalDegree
      ≤ ((algebraMap ℂ R9) (coeff d P)).totalDegree + (∏ i ∈ d.support, subF r i ^ d i).totalDegree :=
        totalDegree_mul _ _
    _ ≤ 0 + ∑ i ∈ d.support, d i := by
        refine add_le_add ?_ ?_
        · exact (totalDegree_C _).le
        · refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (totalDegree_pow _ _).trans (by nlinarith [hlin i])
    _ ≤ P.totalDegree := by rw [zero_add]; exact le_totalDegree hd

section W0

variable (W : Submodule ℂ R9) (D : ℕ)

def W₀ : Submodule ℂ R9 := W ⊓ restrictTotalDegree (Fin 3 × Fin 3) ℂ D

scoped instance : FiniteDimensional ℂ (W₀ W D) :=
  Submodule.finiteDimensional_of_le (inf_le_right : W₀ W D ≤ restrictTotalDegree (Fin 3 × Fin 3) ℂ D)

theorem W₀_le : W₀ W D ≤ W := inf_le_left

variable {W D}

theorem subR_mem_W₀
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    {P : R9} (hP : P ∈ W₀ W D) {r : Fin 3 → Fin 3 → ℝ} (hr : ColOrth r) : subR r P ∈ W₀ W D := by
  have hP' := Submodule.mem_inf.1 hP
  refine Submodule.mem_inf.2 ⟨hrstab P hP'.1 r hr, ?_⟩
  rw [mem_restrictTotalDegree]
  exact (totalDegree_subR_le r P).trans ((mem_restrictTotalDegree _ _ _).1 hP'.2)

def Esp (W : Submodule ℂ R9) (D : ℕ) : Submodule ℂ MFn := (W₀ W D).map readL

scoped instance : FiniteDimensional ℂ (Esp W D) := by unfold Esp; infer_instance

end W0

end

end WsE.PN
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE"

namespace WsE
namespace PN

open MvPolynomial

noncomputable section

open scoped Classical Topology

def pl : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

theorem pl0 : pl 0 = (0, 1) := rfl
theorem pl1 : pl 1 = (0, 2) := rfl
theorem pl2 : pl 2 = (1, 2) := rfl

def rotArr (c₁ c₂ : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun i k =>
  if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
  if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
  if i = k then (1 : ℝ) else 0

def rotM (c : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (rotArr (pl c).1 (pl c).2 s)

theorem colOrth_rotArr01 (s : ℝ) : ColOrth (rotArr 0 1 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

theorem colOrth_rotArr02 (s : ℝ) : ColOrth (rotArr 0 2 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

theorem colOrth_rotArr12 (s : ℝ) : ColOrth (rotArr 1 2 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

theorem colOrth_rotM (c : Fin 3) (s : ℝ) : ColOrth (rotM c s) := by
  rcases fin3_cases c with h | h | h <;> subst h
  · exact colOrth_rotArr01 s
  · exact colOrth_rotArr02 s
  · exact colOrth_rotArr12 s

theorem pl_ne (c : Fin 3) : (pl c).1 ≠ (pl c).2 := by
  rcases fin3_cases c with h | h | h <;> subst h <;> decide

theorem rotM_zero (c : Fin 3) : rotM c 0 = 1 := by
  ext i k
  rcases fin3_cases c with hc | hc | hc <;> subst hc <;>
    rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases k with hk | hk | hk <;> subst hi hk <;>
    simp [rotM, rotArr, pl0, pl1, pl2, Matrix.one_apply]

def Ar (c₁ c₂ : Fin 3) (a l : Fin 3) : ℝ := if a = c₁ ∧ l = c₂ then -1 else if a = c₂ ∧ l = c₁ then 1 else 0

theorem hasDerivAt_rotArr {c₁ c₂ : Fin 3} (hne : c₁ ≠ c₂) (a l : Fin 3) :
    HasDerivAt (fun s => ((rotArr c₁ c₂ s a l : ℝ) : ℂ)) ((Ar c₁ c₂ a l : ℝ) : ℂ) 0 := by
  apply HasDerivAt.ofReal_comp
  simp only [rotArr, Ar]
  by_cases h1 : a = c₁ ∧ l = c₁
  · have h2 : ¬(a = c₁ ∧ l = c₂) := fun h => hne (h1.2.symm.trans h.2)
    have h3 : ¬(a = c₂ ∧ l = c₁) := fun h => hne (h1.1.symm.trans h.1)
    simp only [if_pos h1, if_neg h2, if_neg h3]
    simpa using Real.hasDerivAt_cos 0
  · simp only [if_neg h1]
    by_cases h2 : a = c₂ ∧ l = c₂
    · have h3 : ¬(a = c₁ ∧ l = c₂) := fun h => hne (h.1.symm.trans h2.1)
      have h4 : ¬(a = c₂ ∧ l = c₁) := fun h => hne (h.2.symm.trans h2.2)
      simp only [if_pos h2, if_neg h3, if_neg h4]
      simpa using Real.hasDerivAt_cos 0
    · simp only [if_neg h2]
      by_cases h3 : a = c₁ ∧ l = c₂
      · simp only [if_pos h3]
        convert (Real.hasDerivAt_sin 0).neg using 1 <;> first | rfl | simp
      · simp only [if_neg h3]
        by_cases h4 : a = c₂ ∧ l = c₁
        · simp only [if_pos h4]
          simpa using Real.hasDerivAt_sin 0
        · simp only [if_neg h4]
          exact hasDerivAt_const 0 _

theorem hasDerivAt_mul_rotM_entry (c : Fin 3) (m : Matrix (Fin 3) (Fin 3) ℝ) (k l : Fin 3) :
    HasDerivAt (fun s => ((((m * rotM c s) k l) : ℝ) : ℂ))
      (∑ a : Fin 3, ((m k a : ℝ) : ℂ) * ((Ar (pl c).1 (pl c).2 a l : ℝ) : ℂ)) 0 := by
  have hfun : (fun s => ((((m * rotM c s) k l) : ℝ) : ℂ)) =
      fun s => ∑ a : Fin 3, ((m k a : ℝ) : ℂ) * ((rotArr (pl c).1 (pl c).2 s a l : ℝ) : ℂ) := by
    funext s
    simp only [rotM, Matrix.mul_apply, Matrix.of_apply]
    push_cast
    rfl
  rw [hfun]
  exact HasDerivAt.fun_sum fun a _ => (hasDerivAt_rotArr (pl_ne c) a l).const_mul _

def velP (c : Fin 3) (k l : Fin 3) : R9 :=
  ∑ a : Fin 3, MvPolynomial.X (k, a) * MvPolynomial.C ((Ar (pl c).1 (pl c).2 a l : ℝ) : ℂ)

def Dder (c : Fin 3) : Derivation ℂ R9 R9 :=
  MvPolynomial.mkDerivation ℂ (fun kl : Fin 3 × Fin 3 => velP c kl.1 kl.2)

theorem mkDerivation_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    MvPolynomial.mkDerivation ℂ f P = ∑ i : σ, f i * pderiv i P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    simp only [MvPolynomial.algebraMap_eq, pderiv_C, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, mul_add]
  | mul_X p i hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X, hp, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    simp only [pderiv_mul, pderiv_X, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Fintype.sum_eq_single i (fun j hj => by
        rw [Pi.single_apply]
        simp [hj, Ne.symm hj])]
      rw [Pi.single_apply]
      simp [mul_comm]
theorem Dder_apply (c : Fin 3) (P : R9) :
    Dder c P = ∑ k : Fin 3, ∑ l : Fin 3, velP c k l * pderiv (k, l) P := by
  classical
  rw [Dder, mkDerivation_eq_sum, Fintype.sum_prod_type]

theorem Dder_X (c : Fin 3) (k l : Fin 3) : Dder c (MvPolynomial.X (k, l)) = velP c k l := by
  rw [Dder, MvPolynomial.mkDerivation_X]

theorem Dder_velP (c c' : Fin 3) (k l : Fin 3) :
    Dder c (velP c' k l) = ∑ a : Fin 3, MvPolynomial.C ((Ar (pl c').1 (pl c').2 a l : ℝ) : ℂ) * velP c k a := by
  rw [velP, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Derivation.leibniz, Dder_X, ← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, smul_zero, zero_add,
    smul_eq_mul, MvPolynomial.algebraMap_eq]

theorem readL_Dder (c : Fin 3) (P : R9) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    readL (Dder c P) m = ∑ k : Fin 3, ∑ l : Fin 3,
      (∑ a : Fin 3, ((m k a : ℝ) : ℂ) * ((Ar (pl c).1 (pl c).2 a l : ℝ) : ℂ)) * eval (pt m) (pderiv (k, l) P) := by
  simp only [readL_apply, Dder_apply, map_sum, map_mul, velP, eval_X, eval_C, pt]

theorem hasDerivAt_readL_rot (c : Fin 3) (P : R9) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun s : ℝ => readL P (m * rotM c s)) (readL (Dder c P) m) 0 := by
  classical
  have hD := hasDerivAt_eval P (fun s => pt (m * rotM c s))
    (fun kl => ∑ a : Fin 3, ((m kl.1 a : ℝ) : ℂ) * ((Ar (pl c).1 (pl c).2 a kl.2 : ℝ) : ℂ)) 0
    (fun kl => hasDerivAt_mul_rotM_entry c m kl.1 kl.2)
  simp only [rotM_zero, Matrix.mul_one] at hD
  rw [readL_Dder, ← Fintype.sum_prod_type']
  convert hD using 1
  all_goals first | rfl | skip
  · simp only [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem bracket_X (c c' : Fin 3) (k l : Fin 3) :
    ⁅Dder c, Dder c'⁆ (MvPolynomial.X (k, l)) =
      ∑ a : Fin 3, MvPolynomial.C ((Ar (pl c').1 (pl c').2 a l : ℝ) : ℂ) * velP c k a -
        ∑ a : Fin 3, MvPolynomial.C ((Ar (pl c).1 (pl c).2 a l : ℝ) : ℂ) * velP c' k a := by
  rw [Derivation.commutator_apply, Dder_X, Dder_X, Dder_velP, Dder_velP]

theorem bracket01 : ⁅Dder 0, Dder 1⁆ = Dder 2 := by
  refine MvPolynomial.derivation_ext fun kl => ?_
  obtain ⟨k, l⟩ := kl
  rw [bracket_X, Dder_X]
  simp only [velP, Ar, pl0, pl1, pl2, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false, true_and,
    false_and, and_true, and_false]
  rcases fin3_cases l with h | h | h <;> subst h <;>
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] <;> push_cast <;>
    simp only [map_zero, map_one, map_neg, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero,
      zero_sub] <;> ring

theorem bracket02 : ⁅Dder 0, Dder 2⁆ = -Dder 1 := by
  refine MvPolynomial.derivation_ext fun kl => ?_
  obtain ⟨k, l⟩ := kl
  rw [bracket_X, Derivation.neg_apply, Dder_X]
  simp only [velP, Ar, pl0, pl1, pl2, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false, true_and,
    false_and, and_true, and_false]
  rcases fin3_cases l with h | h | h <;> subst h <;>
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] <;> push_cast <;>
    simp only [map_zero, map_one, map_neg, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero,
      zero_sub] <;> ring

theorem bracket12 : ⁅Dder 1, Dder 2⁆ = Dder 0 := by
  refine MvPolynomial.derivation_ext fun kl => ?_
  obtain ⟨k, l⟩ := kl
  rw [bracket_X, Dder_X]
  simp only [velP, Ar, pl0, pl1, pl2, Fin.sum_univ_three, f01, f02, f10, f12, f20, f21, if_true, if_false, true_and,
    false_and, and_true, and_false]
  rcases fin3_cases l with h | h | h <;> subst h <;>
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false] <;> push_cast <;>
    simp only [map_zero, map_one, map_neg, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero,
      zero_sub] <;> ring

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"

end WsE.PN
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"

namespace WsE
namespace PN

open MvPolynomial

noncomputable section

open scoped Classical Topology

theorem readL_subR' (r : Matrix (Fin 3) (Fin 3) ℝ) (P : R9) :
    (fun m => readL P (m * r)) = readL (subR r P) :=
  readL_subR r P

section Ops

variable {W : Submodule ℂ R9} {D : ℕ}
  (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)

include hrstab in

theorem readL_Dder_mem {P : R9} (hP : P ∈ W₀ W D) (c : Fin 3) : readL (Dder c P) ∈ Esp W D := by
  have hclosed : IsClosed ((Esp W D : Submodule ℂ MFn) : Set MFn) := (Esp W D).closed_of_finiteDimensional
  let F : ℝ → MFn := fun t m => (t - 0)⁻¹ • (readL P (m * rotM c t) - readL P (m * rotM c 0))
  have hmem : ∀ t, F t ∈ Esp W D := by
    intro t
    have h1 : readL (subR (rotM c t) P) ∈ Esp W D :=
      Submodule.mem_map_of_mem (subR_mem_W₀ hrstab hP (colOrth_rotM c t))
    have h2 : readL (subR (rotM c 0) P) ∈ Esp W D :=
      Submodule.mem_map_of_mem (subR_mem_W₀ hrstab hP (colOrth_rotM c 0))
    have h3 := (Esp W D).smul_mem (((t - 0)⁻¹ : ℝ) : ℂ) ((Esp W D).sub_mem h1 h2)
    have : F t = (((t - 0)⁻¹ : ℝ) : ℂ) • (readL (subR (rotM c t) P) - readL (subR (rotM c 0) P)) := by
      rw [← readL_subR' (rotM c t) P, ← readL_subR' (rotM c 0) P]
      funext m
      simp only [F, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
    rw [this]
    exact h3
  have hlim : Filter.Tendsto F (𝓝[≠] 0) (𝓝 (readL (Dder c P))) := by
    rw [tendsto_pi_nhds]
    intro m
    have hd := hasDerivAt_readL_rot c P m
    rw [hasDerivAt_iff_tendsto_slope] at hd
    exact hd
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

def Lfun (c : Fin 3) (F : MFn) : MFn := fun m => deriv (fun s : ℝ => F (m * rotM c s)) 0

theorem Lfun_readL (c : Fin 3) (P : R9) : Lfun c (readL P) = readL (Dder c P) := by
  funext m
  exact (hasDerivAt_readL_rot c P m).deriv

include hrstab in

def LE (c : Fin 3) : Esp W D →ₗ[ℂ] Esp W D where
  toFun F := ⟨Lfun c (F : MFn), by
    obtain ⟨P, hP, hPF⟩ := Submodule.mem_map.1 F.2
    rw [← hPF, Lfun_readL]
    exact readL_Dder_mem hrstab hP c⟩
  map_add' F F' := by
    obtain ⟨P, hP, hPF⟩ := Submodule.mem_map.1 F.2
    obtain ⟨P', hP', hPF'⟩ := Submodule.mem_map.1 F'.2
    apply Subtype.ext
    show Lfun c ((F : MFn) + F') = Lfun c F + Lfun c F'
    rw [← hPF, ← hPF', ← map_add, Lfun_readL, Lfun_readL, Lfun_readL, map_add, map_add]
  map_smul' a F := by
    obtain ⟨P, hP, hPF⟩ := Submodule.mem_map.1 F.2
    apply Subtype.ext
    show Lfun c (a • (F : MFn)) = a • Lfun c F
    rw [← hPF, ← map_smul, Lfun_readL, Lfun_readL, Derivation.map_smul, map_smul]

theorem LE_coe (c : Fin 3) (F : Esp W D) : ((LE hrstab c F : Esp W D) : MFn) = Lfun c (F : MFn) := rfl

theorem LE_coe_of_eq (c : Fin 3) (F : Esp W D) {P : R9} (hPF : readL P = (F : MFn)) :
    ((LE hrstab c F : Esp W D) : MFn) = readL (Dder c P) := by
  rw [LE_coe, ← hPF, Lfun_readL]

theorem LE_tie (F : Esp W D) (c : Fin 3) (r : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun s : ℝ => (F : MFn) (r * rotM c s)) (((LE hrstab c F : Esp W D) : MFn) r) 0 := by
  obtain ⟨P, hP, hPF⟩ := Submodule.mem_map.1 F.2
  rw [LE_coe, Lfun, ← hPF]
  exact (hasDerivAt_readL_rot c P r).differentiableAt.hasDerivAt

theorem LE_comm (F : Esp W D) (r : Matrix (Fin 3) (Fin 3) ℝ) :
    ((LE hrstab 0 (LE hrstab 1 F) : Esp W D) : MFn) r - ((LE hrstab 1 (LE hrstab 0 F) : Esp W D) : MFn) r =
      ((LE hrstab 2 F : Esp W D) : MFn) r ∧
    ((LE hrstab 0 (LE hrstab 2 F) : Esp W D) : MFn) r - ((LE hrstab 2 (LE hrstab 0 F) : Esp W D) : MFn) r =
      - ((LE hrstab 1 F : Esp W D) : MFn) r ∧
    ((LE hrstab 1 (LE hrstab 2 F) : Esp W D) : MFn) r - ((LE hrstab 2 (LE hrstab 1 F) : Esp W D) : MFn) r =
      ((LE hrstab 0 F : Esp W D) : MFn) r := by
  obtain ⟨P, hP, hPF⟩ := Submodule.mem_map.1 F.2
  have e1 : ∀ c, ((LE hrstab c F : Esp W D) : MFn) = readL (Dder c P) := fun c => LE_coe_of_eq hrstab c F hPF
  have e2 : ∀ c c', ((LE hrstab c (LE hrstab c' F) : Esp W D) : MFn) = readL (Dder c (Dder c' P)) :=
    fun c c' => LE_coe_of_eq hrstab c _ (e1 c').symm
  simp only [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun Dd : Derivation ℂ R9 R9 => readL (Dd P) r) bracket01
    simp only [Derivation.commutator_apply, map_sub, Pi.sub_apply] at h
    exact h
  · have h := congrArg (fun Dd : Derivation ℂ R9 R9 => readL (Dd P) r) bracket02
    simp only [Derivation.commutator_apply, map_sub, Pi.sub_apply, Derivation.neg_apply, map_neg, Pi.neg_apply] at h
    exact h
  · have h := congrArg (fun Dd : Derivation ℂ R9 R9 => readL (Dd P) r) bracket12
    simp only [Derivation.commutator_apply, map_sub, Pi.sub_apply] at h
    exact h

end Ops
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"

end WsE.PN
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero.WsE.PN"

open MvPolynomial in
theorem solution
    (ε : Fin 3 → Fin 2) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (hrstab : (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W))
    (hiso : (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P))
    (hne : ∃ P ∈ W, ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) :
    ∃ (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧ p.IsHomogeneous ℓ ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) := by
  classical
  obtain ⟨P₀, hP₀W, o₀, ho₀, hne₀⟩ := hne
  have hrstab' : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, WsE.PN.ColOrth r → WsE.PN.subR r P ∈ W := hrstab
  have hP₀ : P₀ ∈ WsE.PN.W₀ W P₀.totalDegree :=
    Submodule.mem_inf.2 ⟨hP₀W, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl⟩

  have hneE : ∃ F ∈ WsE.PN.Esp W P₀.totalDegree, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0 :=
    ⟨WsE.PN.readL P₀, Submodule.mem_map_of_mem hP₀, Matrix.of o₀, (WsE.PN.mem_O3_iff _).2 ho₀, hne₀⟩
  have hstabE : ∀ F ∈ WsE.PN.Esp W P₀.totalDegree, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      (fun r => F (r * r₀)) ∈ WsE.PN.Esp W P₀.totalDegree := by
    rintro F hF r₀ hr₀
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hF
    rw [WsE.PN.readL_subR' r₀ P]
    exact Submodule.mem_map_of_mem (WsE.PN.subR_mem_W₀ hrstab' hP ((WsE.PN.mem_O3_iff r₀).1 hr₀))
  have hEX := LanglandsTunnell.CubicInduction.exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable 0
    (WsE.PN.Esp W P₀.totalDegree) hneE hstabE (WsE.PN.LE hrstab')
    (fun F c r _ => WsE.PN.LE_tie hrstab' F c r) (fun F r _ => WsE.PN.LE_comm hrstab' F r)
  obtain ⟨α, ℓ, p, hp0, hhom, hharm, F, hFE, hread⟩ := hEX
  obtain ⟨Q, hQW₀, hQF⟩ := Submodule.mem_map.1 hFE
  have hQW : Q ∈ W := WsE.PN.W₀_le W _ hQW₀
  have hFQ : ∀ r : Matrix (Fin 3) (Fin 3) ℝ, F r = MvPolynomial.eval (WsE.PN.pt r) Q := fun r => by
    rw [← hQF]; rfl

  have hα : (α : ℕ) = (ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2 := by
    obtain ⟨w, hw1, hwne⟩ := WsE.PN.exists_unit_eval_ne_zero hp0 hhom
    set r₀ : Matrix (Fin 3) (Fin 3) ℝ := WsE.PN.HH 0 w with hr₀def
    have hr₀c : WsE.PN.ColOrth r₀ := WsE.PN.HH_colOrth 0 w hw1
    have hr₀ : r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (WsE.PN.mem_O3_iff _).2 hr₀c
    have hnr₀ : -r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := WsE.PN.neg_mem_O3 hr₀
    have hdet : r₀.det ≠ 0 := WsE.PN.det_ne_zero_of_mem_O3 hr₀
    have hcol : (fun a : Fin 3 => ((r₀ a 0 : ℝ) : ℂ)) = fun a => ((w a : ℝ) : ℂ) :=
      funext fun a => by
        show ((WsE.PN.HH 0 w a 0 : ℝ) : ℂ) = _
        rw [WsE.PN.HH_col 0 w hw1 a]
    have hcoln : (fun a : Fin 3 => (((-r₀) a 0 : ℝ) : ℂ)) = fun a => (-1 : ℂ) * ((w a : ℝ) : ℂ) :=
      funext fun a => by
        show (((-WsE.PN.HH 0 w) a 0 : ℝ) : ℂ) = _
        rw [Matrix.neg_apply, WsE.PN.HH_col 0 w hw1 a]
        push_cast
        ring
    have hiso1 := hiso Q hQW (fun _ => 1) r₀ hr₀c
    have hpt : (fun ij : Fin 3 × Fin 3 =>
        (((∑ c : Fin 3, (fun a b : Fin 3 => if a = b then (-1 : ℝ) ^ (((fun _ : Fin 3 => (1 : Fin 2)) a : Fin 2) : ℕ)
          else 0) ij.1 c * r₀ c ij.2) : ℝ) : ℂ)) = WsE.PN.pt (-r₀) := by
      funext ij
      simp only [WsE.PN.pt, Matrix.neg_apply, Fin.val_one, pow_one, ite_mul, zero_mul, neg_one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_neg]
    rw [hpt] at hiso1
    have key : F (-r₀) = (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ)) * F r₀ := by
      rw [hFQ, hFQ, hiso1]
      simp only [Fin.val_one, mul_one]
      rfl
    rw [hread r₀ hr₀, hread (-r₀) hnr₀, WsE.PN.eval_realise_col, WsE.PN.eval_realise_col, hcoln, hcol,
      WsE.PN.eval_smul_of_isHomogeneous hhom, Matrix.det_neg, Fintype.card_fin] at key
    push_cast at key
    have hX : ((r₀.det : ℝ) : ℂ) ^ (α : ℕ) * MvPolynomial.eval (fun a => ((w a : ℝ) : ℂ)) p ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hdet)) hwne
    have hsign : (-1 : ℂ) ^ ((α : ℕ) + ℓ) = (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ)) := by
      apply mul_right_cancel₀ hX
      rw [← key]
      ring
    have hpar := WsE.PN.mod_two_eq_of_neg_one_pow_eq hsign
    have hα2 : (α : ℕ) < 2 := α.isLt
    omega
  refine ⟨ℓ, p, hp0, hhom, hharm, Q, hQW, fun o ho => ?_⟩
  have hoO : Matrix.of o ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (WsE.PN.mem_O3_iff _).2 ho
  have hr := hread (Matrix.of o) hoO
  rw [hFQ] at hr
  rw [← hα, WsE.PN.detC_eq]
  exact hr

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero (solution)
