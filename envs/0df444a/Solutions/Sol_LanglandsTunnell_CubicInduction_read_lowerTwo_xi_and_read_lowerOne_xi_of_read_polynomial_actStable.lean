-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/aacfa544-b31d-5c19-92e7-3457bbbb11f3

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_sum_mul_eval_sphere_eq_of_isHomogeneous
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable

set_option autoImplicit false

namespace WsF
namespace PT

noncomputable section

open MvPolynomial

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

abbrev R3 := MvPolynomial (Fin 3) ℂ

def Lsub (o : Fin 3 → Fin 3 → ℝ) : Fin 3 → R3 := fun i => ∑ c : Fin 3, C ((o i c : ℝ) : ℂ) * X c

def qo (o : Fin 3 → Fin 3 → ℝ) (p : R3) : R3 := aeval (Lsub o) p

theorem pderiv_Lsub (o : Fin 3 → Fin 3 → ℝ) (b i : Fin 3) : pderiv b (Lsub o i) = C ((o i b : ℝ) : ℂ) := by
  unfold Lsub
  rw [map_sum]
  rw [Fintype.sum_eq_single b (fun c hc => ?_)]
  · rw [pderiv_C_mul, pderiv_X_self, mul_one]
  · rw [pderiv_C_mul, pderiv_X_of_ne hc, mul_zero]

theorem pderiv_qo (o : Fin 3 → Fin 3 → ℝ) (b : Fin 3) (q : R3) :
    pderiv b (aeval (Lsub o) q) = ∑ i : Fin 3, C ((o i b : ℝ) : ℂ) * aeval (Lsub o) (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C r => simp [pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, pderiv_mul, hp, pderiv_Lsub]
    have hr : ∀ i' : Fin 3, aeval (Lsub o) (pderiv i' (p * X i)) =
        aeval (Lsub o) (pderiv i' p) * Lsub o i + (if i = i' then aeval (Lsub o) p else 0) := by
      intro i'
      classical
      rw [pderiv_mul, map_add, map_mul, map_mul, aeval_X, pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    simp_rw [hr, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_mul]
    have key : ∀ x : Fin 3, C ((o x b : ℝ) : ℂ) * aeval (Lsub o) (pderiv x p) * Lsub o i =
        C ((o x b : ℝ) : ℂ) * (aeval (Lsub o) (pderiv x p) * Lsub o i) := fun x => mul_assoc _ _ _
    have key2 : ∀ x : Fin 3, Lsub o i * (C ((o x b : ℝ) : ℂ) * aeval (Lsub o) (pderiv x p)) =
        C ((o x b : ℝ) : ℂ) * (aeval (Lsub o) (pderiv x p) * Lsub o i) := fun x => by ring
    simp only [key, key2]
    ring

theorem Lsub_isHomogeneous (o : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : (Lsub o i).IsHomogeneous 1 := by
  unfold Lsub
  exact IsHomogeneous.sum _ _ _ (fun c _ => isHomogeneous_C_mul_X _ _)

theorem qo_isHomogeneous (o : Fin 3 → Fin 3 → ℝ) {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) :
    (aeval (Lsub o) p).IsHomogeneous ℓ := by
  have := hp.aeval (Lsub o) (fun i => Lsub_isHomogeneous o i)
  rwa [one_mul] at this

theorem eval_aeval_Lsub (o : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℂ) (q : R3) :
    eval x (aeval (Lsub o) q) = eval (fun i => ∑ c : Fin 3, ((o i c : ℝ) : ℂ) * x c) q := by
  have h := congrArg (fun φ : R3 →ₐ[ℂ] ℂ => φ q) (comp_aeval (Lsub o) (aeval (R := ℂ) x))
  have h' : eval x (aeval (Lsub o) q) = eval (fun i => aeval x (Lsub o i)) q := h
  rw [h']
  exact congrArg (fun f : Fin 3 → ℂ => eval f q) (funext fun i => by simp [Lsub, map_sum, map_mul, eval_C, eval_X])

def Λ (a b j : Fin 3) : R3 →ₗ[ℂ] ℂ :=
  (aeval (R := ℂ) (fun t : Fin 3 => if t = j then (1 : ℂ) else 0)).toLinearMap.comp
    (((pderiv b : Derivation ℂ R3 R3) : R3 →ₗ[ℂ] R3).comp ((pderiv a : Derivation ℂ R3 R3) : R3 →ₗ[ℂ] R3))

theorem Λ_apply (a b j : Fin 3) (q : R3) :
    Λ a b j q = eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (pderiv b (pderiv a q)) := by
  simp [Λ, coe_aeval_eq_eval]

theorem pderiv_comm (i j : Fin 3) (p : R3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ R3 R3), (pderiv j : Derivation ℂ R3 R3)⁆ = 0 := by
    refine MvPolynomial.derivation_ext (fun k => ?_)
    rw [Derivation.commutator_apply]
    classical
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ R3 R3 => D p) h
  simp only [Derivation.commutator_apply] at h2
  have h3 : pderiv i (pderiv j p) - pderiv j (pderiv i p) = 0 := by simpa using h2
  exact sub_eq_zero.mp h3

theorem target_eq_Λ (o : Fin 3 → Fin 3 → ℝ) (p : R3) (a b j : Fin 3) :
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
        (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
          MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ))
            (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) =
      Λ a b j (aeval (Lsub o) p) := by
  rw [Λ_apply, pderiv_qo]
  simp only [map_sum, map_mul, pderiv_C_mul, pderiv_qo, eval_C, eval_X, Finset.mul_sum, eval_aeval_Lsub]
  have hre : ∀ q : R3, eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
      (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q) =
      eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) q := by
    intro q
    rw [show aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q =
        rename (fun a : Fin 3 => (a, j)) q by
      rw [MvPolynomial.rename_eq, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]; rfl]
    rw [eval_rename]
    rfl
  have hcol : (fun i : Fin 3 => ∑ c : Fin 3, ((o i c : ℝ) : ℂ) * (if c = j then (1 : ℂ) else 0)) =
      fun i : Fin 3 => ((o i j : ℝ) : ℂ) := by
    funext i
    simp
  simp only [hre, hcol]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
  rw [pderiv_comm i' i]
  ring

end

end WsF.PT

namespace WsF
namespace PT

noncomputable section

open MvPolynomial

def detC (o : Fin 3 → Fin 3 → ℝ) : ℂ := (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det

theorem detC_eq (o : Matrix (Fin 3) (Fin 3) ℝ) : detC o = ((o.det : ℝ) : ℂ) := by
  unfold detC
  have : (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)) = (Complex.ofRealHom : ℝ →+* ℂ).mapMatrix o := rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem detC_mul (o H : Matrix (Fin 3) (Fin 3) ℝ) : detC (o * H) = detC o * detC H := by
  rw [detC_eq, detC_eq, detC_eq, Matrix.det_mul]
  push_cast
  rfl

theorem det_sq_of_colOrth (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ColOrth H) : H.det * H.det = 1 := by
  have h1 := congrArg Matrix.det ((colOrth_iff H).mp hH)
  rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1

theorem detC_sq (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ColOrth H) : detC H ^ 2 = 1 := by
  rw [detC_eq, sq]
  exact_mod_cast det_sq_of_colOrth H hH

theorem detC_pow_mul_self (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : ColOrth H) (α : ℕ) :
    detC H ^ α * detC H ^ α = 1 := by
  rw [← mul_pow, ← sq, detC_sq H hH, one_pow]

theorem eval_realise_col (o : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (q : R3) :
    eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
      (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q) =
    eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) q := by
  rw [show aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q =
      rename (fun a : Fin 3 => (a, j)) q by
    rw [MvPolynomial.rename_eq, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]; rfl]
  rw [eval_rename]
  rfl

def evJ (j : Fin 3) : R3 →ₗ[ℂ] ℂ := (aeval (R := ℂ) (fun t : Fin 3 => if t = j then (1 : ℂ) else 0)).toLinearMap
def Dl (a : Fin 3) : R3 →ₗ[ℂ] R3 := ((pderiv a : Derivation ℂ R3 R3) : R3 →ₗ[ℂ] R3)

theorem evJ_apply (j : Fin 3) (q : R3) : evJ j q = eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) q := by
  simp [evJ]
theorem Dl_apply (a : Fin 3) (q : R3) : Dl a q = pderiv a q := rfl

theorem eval_ej_pderiv_qo (o : Fin 3 → Fin 3 → ℝ) (j a : Fin 3) (q : R3) :
    eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (pderiv a (aeval (Lsub o) q)) =
      ∑ i : Fin 3, ((o i a : ℝ) : ℂ) * eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) (pderiv i q) := by
  rw [pderiv_qo]
  simp only [map_sum, map_mul, eval_C, eval_aeval_Lsub]
  have hcol : (fun i : Fin 3 => ∑ c : Fin 3, ((o i c : ℝ) : ℂ) * (if c = j then (1 : ℂ) else 0)) =
      fun i : Fin 3 => ((o i j : ℝ) : ℂ) := by
    funext i; simp
  rw [hcol]

theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide

def eps (a c d : Fin 3) : ℂ :=
  (((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) * (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2

def Kx (o : Fin 3 → Fin 3 → ℝ) (b m d : Fin 3) : ℂ :=
  ∑ i' : Fin 3, ∑ c : Fin 3, eps i' c d * ((o i' b : ℝ) : ℂ) * ((o c m : ℝ) : ℂ)

set_option maxHeartbeats 16000000 in

theorem eps3 (o : Fin 3 → Fin 3 → ℝ) (b m n : Fin 3) :
    (∑ i' : Fin 3, ∑ c : Fin 3, ∑ d' : Fin 3,
      eps i' c d' * ((o i' b : ℝ) : ℂ) * ((o c m : ℝ) : ℂ) * ((o d' n : ℝ) : ℂ)) = detC o * eps b m n := by
  unfold detC
  rw [Matrix.det_fin_three]
  rcases fin3_cases b with rfl | rfl | rfl <;> rcases fin3_cases m with rfl | rfl | rfl <;>
    rcases fin3_cases n with rfl | rfl | rfl <;>
    (simp only [eps, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
        Nat.cast_ofNat, Matrix.of_apply]; ring)

theorem rowOrth_castC (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (r s : Fin 3) :
    (∑ n : Fin 3, ((o r n : ℝ) : ℂ) * ((o s n : ℝ) : ℂ)) = if r = s then 1 else 0 := by
  have h1 : (Matrix.of o).transpose * Matrix.of o = 1 := (colOrth_iff _).mp ho
  have h2 : Matrix.of o * (Matrix.of o).transpose = 1 := mul_eq_one_comm.mp h1
  have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => ((M r s : ℝ) : ℂ)) h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] at h3
  push_cast at h3
  rw [h3]
  split_ifs <;> simp

set_option maxHeartbeats 16000000 in

theorem key (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (b m d : Fin 3) :
    Kx o b m d = detC o * ∑ n : Fin 3, eps b m n * ((o d n : ℝ) : ℂ) := by
  have hr := rowOrth_castC o ho
  have r0 := hr 0 d
  have r1 := hr 1 d
  have r2 := hr 2 d
  have e3 : ∀ n : Fin 3, detC o * eps b m n =
      ∑ i' : Fin 3, ∑ c : Fin 3, ∑ d' : Fin 3,
        eps i' c d' * ((o i' b : ℝ) : ℂ) * ((o c m : ℝ) : ℂ) * ((o d' n : ℝ) : ℂ) := fun n => (eps3 o b m n).symm
  rw [Finset.mul_sum]
  have : ∀ n : Fin 3, detC o * (eps b m n * ((o d n : ℝ) : ℂ)) = (detC o * eps b m n) * ((o d n : ℝ) : ℂ) :=
    fun n => by ring
  simp only [this, e3]
  unfold Kx
  rcases fin3_cases d with rfl | rfl | rfl
  · simp only [Fin.sum_univ_three, eps, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, if_true, ne10, ne20] at r0 r1 r2 ⊢
    simp only [if_false] at r1 r2
    linear_combination (-(((o 1 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ) - ((o 2 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ))) * r0
      + (-(((o 2 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ) - ((o 0 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ))) * r1
      + (-(((o 0 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ) - ((o 1 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ))) * r2
  · simp only [Fin.sum_univ_three, eps, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, if_true, ne01, ne21] at r0 r1 r2 ⊢
    simp only [if_false] at r0 r2
    linear_combination (-(((o 1 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ) - ((o 2 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ))) * r0
      + (-(((o 2 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ) - ((o 0 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ))) * r1
      + (-(((o 0 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ) - ((o 1 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ))) * r2
  · simp only [Fin.sum_univ_three, eps, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, if_true, ne02, ne12] at r0 r1 r2 ⊢
    simp only [if_false] at r0 r1
    linear_combination (-(((o 1 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ) - ((o 2 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ))) * r0
      + (-(((o 2 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ) - ((o 0 b : ℝ) : ℂ) * ((o 2 m : ℝ) : ℂ))) * r1
      + (-(((o 0 b : ℝ) : ℂ) * ((o 1 m : ℝ) : ℂ) - ((o 1 b : ℝ) : ℂ) * ((o 0 m : ℝ) : ℂ))) * r2

def rotP (b : Fin 3) (r : R3) : R3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.C (eps b c d) * (MvPolynomial.X c * MvPolynomial.pderiv d r)

def rotL (b : Fin 3) : R3 →ₗ[ℂ] R3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, (eps b c d) • ((LinearMap.mulLeft ℂ (X c : R3)).comp (Dl d))

theorem rotL_apply (b : Fin 3) (r : R3) : rotL b r = rotP b r := by
  simp only [rotL, rotP, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Dl_apply, smul_eq_C_mul]

def Λ₂ (a b j : Fin 3) : R3 →ₗ[ℂ] ℂ :=
  (evJ j).comp ((1 / 2 : ℂ) • ((rotL b).comp (Dl a) + (rotL a).comp (Dl b)))

theorem Λ₂_apply (a b j : Fin 3) (q : R3) :
    Λ₂ a b j q = (1 / 2 : ℂ) * (eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (rotP b (pderiv a q)) +
      eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (rotP a (pderiv b q))) := by
  simp only [Λ₂, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, rotL_apply, Dl_apply,
    evJ_apply, map_add, map_smul, smul_eq_mul]

theorem eval_ej_rotP (b j : Fin 3) (r : R3) :
    eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (rotP b r) =
      ∑ d : Fin 3, eps b j d * eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (pderiv d r) := by
  unfold rotP
  simp only [map_sum, map_mul, eval_C, eval_X]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Fintype.sum_eq_single j (fun c hc => by simp [hc])]
  simp

theorem eval_ej_pderiv2_qo (o : Fin 3 → Fin 3 → ℝ) (j n a : Fin 3) (p : R3) :
    eval (fun t : Fin 3 => if t = j then (1 : ℂ) else 0) (pderiv n (pderiv a (aeval (Lsub o) p))) =
      ∑ i : Fin 3, ((o i a : ℝ) : ℂ) * ∑ d : Fin 3, ((o d n : ℝ) : ℂ) *
        eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) (pderiv d (pderiv i p)) := by
  rw [pderiv_qo]
  simp only [map_sum, pderiv_C_mul, map_mul, eval_C, eval_ej_pderiv_qo]

theorem readout2_regroup (o : Fin 3 → Fin 3 → ℝ) (p : R3) (a b j : Fin 3) :
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
        (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
          (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
          MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ))
            (∑ c : Fin 3, ∑ d : Fin 3,
              MvPolynomial.C ((((i' : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
                (((d : ℕ) : ℂ) - ((i' : ℕ) : ℂ)) / 2) *
                (MvPolynomial.X c * MvPolynomial.pderiv d (MvPolynomial.pderiv i p)))) =
      ∑ i : Fin 3, ∑ d : Fin 3, (1 / 2 : ℂ) * ((o i a : ℝ) : ℂ) *
          eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) (pderiv d (pderiv i p)) * Kx o b j d +
      ∑ i : Fin 3, ∑ d : Fin 3, (1 / 2 : ℂ) * ((o i b : ℝ) : ℂ) *
          eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) (pderiv d (pderiv i p)) * Kx o a j d := by
  simp only [map_sum, map_mul, map_add, eval_C, eval_X, aeval_X, eval_realise_col, Kx, eps]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  ring

theorem target2 (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (p : R3) (a b j : Fin 3) :
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
        (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
          (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
          MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ))
            (∑ c : Fin 3, ∑ d : Fin 3,
              MvPolynomial.C ((((i' : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
                (((d : ℕ) : ℂ) - ((i' : ℕ) : ℂ)) / 2) *
                (MvPolynomial.X c * MvPolynomial.pderiv d (MvPolynomial.pderiv i p)))) =
      detC o * Λ₂ a b j (aeval (Lsub o) p) := by
  rw [readout2_regroup]
  simp only [key o ho]
  rw [Λ₂_apply, eval_ej_rotP, eval_ej_rotP]
  simp only [eval_ej_pderiv2_qo]
  simp only [Fin.sum_univ_three]
  ring

abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

def pt (o : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

def subR (r : Fin 3 → Fin 3 → ℝ) (Q : R9) : R9 :=
  MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
    ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) Q

theorem eval_subR (o r : Fin 3 → Fin 3 → ℝ) (Q : R9) :
    eval (pt o) (subR r Q) = eval (pt (Matrix.of o * Matrix.of r)) Q := by
  have h := congrArg (fun φ : R9 →ₐ[ℂ] ℂ => φ Q)
    (comp_aeval (fun ij : Fin 3 × Fin 3 =>
      ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) (aeval (R := ℂ) (pt o)))
  have h' : eval (pt o) (subR r Q) = eval (fun ij : Fin 3 × Fin 3 => aeval (pt o)
      (∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ))) Q := h
  rw [h']
  exact congrArg (fun f : Fin 3 × Fin 3 → ℂ => eval f Q) (funext fun ij => by
    simp [pt, map_sum, map_mul, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, coe_aeval_eq_eval])

theorem realise_functional (Λ : R3 →ₗ[ℂ] ℂ) (W : Submodule ℂ R9)
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) (j : Fin 3) (α : ℕ)
    (Q : R9) (hQ : Q ∈ W)
    (hreal : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ α * eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) p) :
    ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ α * Λ (aeval (Lsub o) p) := by
  obtain ⟨N, u, c, hu, hΛ⟩ :=
    LanglandsTunnell.CubicInduction.exists_sum_mul_eval_sphere_eq_of_isHomogeneous ℓ Λ
  refine ⟨∑ n : Fin N, (c n * detC (HH j (u n)) ^ α) • subR (HH j (u n)) Q, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun n _ => Submodule.smul_mem _ _
      (hrstab Q hQ (HH j (u n)) (HH_colOrth j (u n) (hu n))))
  · intro o ho
    rw [hΛ _ (qo_isHomogeneous o hp), Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [smul_eval, eval_subR]
    have hHo : ColOrth (HH j (u n)) := HH_colOrth j (u n) (hu n)
    have hoH : ColOrth (Matrix.of o * HH j (u n)) := colOrth_mul _ _ ho hHo
    have h1 := hreal (Matrix.of o * HH j (u n)) hoH
    have hcol : eval (fun a : Fin 3 => ((u n a : ℝ) : ℂ)) (aeval (Lsub o) p) =
        eval (fun i : Fin 3 => (((Matrix.of o * HH j (u n)) i j : ℝ) : ℂ)) p := by
      rw [eval_aeval_Lsub]
      exact congrArg (fun f : Fin 3 → ℂ => eval f p) (funext fun i => by
        simp [Matrix.mul_apply, HH_col j (u n) (hu n), Complex.ofReal_sum, Complex.ofReal_mul])
    have hdet : detC o ^ α = detC (HH j (u n)) ^ α * detC (Matrix.of o * HH j (u n)) ^ α := by
      rw [detC_mul, mul_pow, mul_comm (detC (Matrix.of o) ^ α), ← mul_assoc,
        detC_pow_mul_self _ hHo, one_mul]
      rfl
    have hof : (Matrix.of (HH j (u n)) : Matrix (Fin 3) (Fin 3) ℝ) = HH j (u n) := rfl
    rw [hof, h1, hcol, hdet]
    ring

theorem conj1 (W : Submodule ℂ R9)
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) (j : Fin 3) (α : ℕ)
    (Q : R9) (hQ : Q ∈ W)
    (hreal : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ α * eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) p) :
    ∀ a b : Fin 3, ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ))
              (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) := by
  intro a b
  obtain ⟨Q', hQ', h⟩ := realise_functional (Λ a b j) W hrstab ℓ p hp j α Q hQ hreal
  refine ⟨Q', hQ', fun o ho => ?_⟩
  rw [target_eq_Λ]
  exact h o ho

theorem conj2 (W : Submodule ℂ R9)
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) (j : Fin 3) (α : ℕ)
    (Q : R9) (hQ : Q ∈ W)
    (hreal : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ α * eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) p) :
    ∀ a b : Fin 3, ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ (α + 1) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
            (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (∑ c : Fin 3, ∑ d : Fin 3,
              MvPolynomial.C ((((i' : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
                (((d : ℕ) : ℂ) - ((i' : ℕ) : ℂ)) / 2) *
                (MvPolynomial.X c * MvPolynomial.pderiv d (MvPolynomial.pderiv i p)))) := by
  intro a b
  obtain ⟨Q', hQ', h⟩ := realise_functional (Λ₂ a b j) W hrstab ℓ p hp j α Q hQ hreal
  refine ⟨Q', hQ', fun o ho => ?_⟩
  rw [target2 o ho, h o ho, pow_succ]
  have hsq : detC o * detC o = 1 := by rw [← sq]; exact detC_sq _ ho
  calc detC o ^ α * Λ₂ a b j (aeval (Lsub o) p)
      = detC o ^ α * (detC o * detC o) * Λ₂ a b j (aeval (Lsub o) p) := by rw [hsq, mul_one]
    _ = detC o ^ α * detC o * (detC o * Λ₂ a b j (aeval (Lsub o) p)) := by ring

end

end WsF.PT

namespace WsF
namespace PT

noncomputable section

open MvPolynomial

theorem sort10 (q : R3) : pderiv 0 (pderiv 1 q) = pderiv 1 (pderiv 0 q) := pderiv_comm 0 1 q
theorem sort20 (q : R3) : pderiv 0 (pderiv 2 q) = pderiv 2 (pderiv 0 q) := pderiv_comm 0 2 q
theorem sort21 (q : R3) : pderiv 1 (pderiv 2 q) = pderiv 2 (pderiv 1 q) := pderiv_comm 1 2 q

theorem max01 : max (0 : Fin 3) 1 = 1 := by decide
theorem max10 : max (1 : Fin 3) 0 = 1 := by decide
theorem max02 : max (0 : Fin 3) 2 = 2 := by decide
theorem max20 : max (2 : Fin 3) 0 = 2 := by decide
theorem max12 : max (1 : Fin 3) 2 = 2 := by decide
theorem max21 : max (2 : Fin 3) 1 = 2 := by decide
theorem min01 : min (0 : Fin 3) 1 = 0 := by decide
theorem min10 : min (1 : Fin 3) 0 = 0 := by decide
theorem min02 : min (0 : Fin 3) 2 = 0 := by decide
theorem min20 : min (2 : Fin 3) 0 = 0 := by decide
theorem min12 : min (1 : Fin 3) 2 = 1 := by decide
theorem min21 : min (2 : Fin 3) 1 = 1 := by decide
theorem lt01 : (0 : Fin 3) < 1 := by decide
theorem lt02 : (0 : Fin 3) < 2 := by decide
theorem lt12 : (1 : Fin 3) < 2 := by decide
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide
theorem nlt00 : ¬ (0 : Fin 3) < 0 := by decide
theorem nlt11 : ¬ (1 : Fin 3) < 1 := by decide
theorem nlt22 : ¬ (2 : Fin 3) < 2 := by decide

theorem rho0 : (![1, 0, -1] : Fin 3 → ℂ) 0 = 1 := rfl
theorem rho1 : (![1, 0, -1] : Fin 3 → ℂ) 1 = 0 := rfl
theorem rho2 : (![1, 0, -1] : Fin 3 → ℂ) 2 = -1 := rfl

def Xi (ν : Fin 3 → ℂ) (p : R3) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

def lower2 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

def realise (j : Fin 3) (q : R3) : R9 :=
  MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

def Mlt (ν : Fin 3 → ℂ) (c d : Fin 3) : R9 :=
  ∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))

def Vf (c d i j : Fin 3) : R9 :=
  ∑ m : Fin 3,
    (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
      else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
      else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)

def Dop (c d : Fin 3) (p : R9) : R9 :=
  ∑ i : Fin 3, ∑ j : Fin 3, Vf c d i j * MvPolynomial.pderiv (i, j) p

theorem act_eq (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : act ν c d p = Mlt ν c d * p + Dop c d p := rfl

theorem Xi_diag (ν : Fin 3 → ℂ) (p : R3) (c : Fin 3) :
    Xi ν p c c = C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p := by
  simp [Xi]

theorem Xi_off (ν : Fin 3 → ℂ) (p : R3) (c d : Fin 3) (h : c ≠ d) :
    Xi ν p c d = -(X (max c d) * pderiv (min c d) p - X (min c d) * pderiv (max c d) p) := by
  simp [Xi, h]

theorem lower2_Xi (ν : Fin 3 → ℂ) (p : R3) :
    lower2 (Xi ν p) =
      C (2 * (ν 0 - 1)) * pderiv 0 (pderiv 0 p) + C (2 * ν 1) * pderiv 1 (pderiv 1 p)
        + C (2 * (ν 2 + 1)) * pderiv 2 (pderiv 2 p)
      + C 2 * (X 0 * pderiv 1 (pderiv 1 (pderiv 0 p)) - X 1 * pderiv 1 (pderiv 0 (pderiv 0 p)))
      + C 2 * (X 0 * pderiv 2 (pderiv 2 (pderiv 0 p)) - X 2 * pderiv 2 (pderiv 0 (pderiv 0 p)))
      + C 2 * (X 1 * pderiv 2 (pderiv 2 (pderiv 1 p)) - X 2 * pderiv 2 (pderiv 1 (pderiv 1 p))) := by
  simp only [lower2, Fin.sum_univ_three]
  rw [Xi_diag, Xi_diag, Xi_diag, Xi_off ν p 0 1 ne01, Xi_off ν p 0 2 ne02, Xi_off ν p 1 0 ne10,
    Xi_off ν p 1 2 ne12, Xi_off ν p 2 0 ne20, Xi_off ν p 2 1 ne21]
  simp only [max01, max10, max02, max20, max12, max21, min01, min10, min02, min20, min12, min21,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne ne01, pderiv_X_of_ne ne10, pderiv_X_of_ne ne02, pderiv_X_of_ne ne20,
    pderiv_X_of_ne ne12, pderiv_X_of_ne ne21, zero_mul, one_mul, zero_add, sort10, sort20, sort21]
  simp only [rho0, rho1, rho2, map_mul, map_add, map_sub, map_neg, map_ofNat, map_one, add_zero]
  ring

def rot (a : Fin 3) (q : R3) : R3 :=
  ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) * (MvPolynomial.X c * MvPolynomial.pderiv d q)

def lower1 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

theorem realise_eq (j : Fin 3) (q : R3) : realise j q = rename (fun a : Fin 3 => (a, j)) q := by
  rw [realise, MvPolynomial.rename_eq, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]; rfl

theorem eval_realise (k : Fin 3 × Fin 3 → ℂ) (j : Fin 3) (q : R3) :
    eval k (realise j q) = eval (fun a => k (a, j)) q := by
  rw [realise_eq, eval_rename]; rfl

theorem act_add (ν : Fin 3 → ℂ) (c d : Fin 3) (P Q : R9) : act ν c d (P + Q) = act ν c d P + act ν c d Q := by
  simp only [act, mul_add, map_add, Finset.sum_add_distrib]
  ring

theorem act_sub (ν : Fin 3 → ℂ) (c d : Fin 3) (P Q : R9) : act ν c d (P - Q) = act ν c d P - act ν c d Q := by
  simp only [act, mul_sub, map_sub, Finset.sum_sub_distrib]
  ring

theorem act_zero (ν : Fin 3 → ℂ) (c d : Fin 3) : act ν c d 0 = 0 := by
  simp [act]

theorem act_sum {ι : Type*} (ν : Fin 3 → ℂ) (c d : Fin 3) (s : Finset ι) (f : ι → R9) :
    act ν c d (∑ x ∈ s, f x) = ∑ x ∈ s, act ν c d (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add, ih]

def detX : R9 := (Matrix.of fun i j : Fin 3 => (X (i, j) : R9)).det

theorem eval_detX (o : Fin 3 → Fin 3 → ℝ) : eval (pt o) detX = detC o := by
  unfold detX detC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [pt]

theorem act_detX_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : act ν c d (detX * P) = detX * act ν c d P :=
  LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul ν c d P

theorem act_detX_pow_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (n : ℕ) (P : R9) :
    act ν c d (detX ^ n * P) = detX ^ n * act ν c d P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_comm (detX ^ n) detX, mul_assoc, act_detX_mul, ih, ← mul_assoc]

theorem eval_act_congr_orth (ν : Fin 3 → ℂ) (c d : Fin 3) (P P' : R9)
    (h : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o → eval (pt o) P = eval (pt o) P')
    (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) :
    eval (pt o) (act ν c d P) = eval (pt o) (act ν c d P') := by
  have hP : ∀ o' : Fin 3 → Fin 3 → ℝ, ColOrth o' → eval (pt o') (P - P') = 0 := by
    intro o' ho'
    rw [map_sub, h o' ho', sub_self]
  have h0 : eval (pt o) (act ν c d (P - P')) = 0 :=
    LanglandsTunnell.CubicInduction.eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero
      ν c d (P - P') hP o ho
  rw [act_sub, map_sub] at h0
  exact sub_eq_zero.mp h0

theorem rowOrth_pt (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (r s : Fin 3) :
    (∑ a : Fin 3, pt o (r, a) * pt o (s, a)) = if r = s then 1 else 0 := by
  simp only [pt]
  exact rowOrth_castC o ho r s

theorem pderiv_pderiv_eq_zero (p : R3) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) (hℓ : ℓ ≤ 1) (i j : Fin 3) :
    pderiv i (pderiv j p) = 0 := by
  have h1 : (pderiv j p).IsHomogeneous (ℓ - 1) := hp.pderiv
  have h0 : ℓ - 1 = 0 := by omega
  rw [h0] at h1
  have h2 := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr h1)
  rw [h2, pderiv_C]

theorem lower2_Xi_eq_zero (ν : Fin 3 → ℂ) (p : R3) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) (hℓ : ℓ ≤ 1) :
    lower2 (Xi ν p) = 0 := by
  have h := pderiv_pderiv_eq_zero p ℓ hp hℓ
  rw [lower2_Xi]
  simp [h]

theorem Xi_C_apply (ν : Fin 3 → ℂ) (r : ℂ) (a b : Fin 3) :
    Xi ν (C r) a b = C (if a = b then 2 * (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) * r else 0) := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · rw [← map_mul]
  · simp

theorem lower1_Xi_C (ν : Fin 3 → ℂ) (r : ℂ) : lower1 (Xi ν (C r)) = 0 := by
  unfold lower1
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ =>
    Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun d _ => ?_))))
  rw [Xi_C_apply, pderiv_C, map_zero, mul_zero, mul_zero]

theorem pow_eq_pow_mod_two {d : ℂ} (hd : d ^ 2 = 1) (n : ℕ) : d ^ n = d ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul, hd, one_pow, one_mul]

def Qab (p : R3) (a b : Fin 3) : R9 :=
  ∑ i : Fin 3, ∑ i' : Fin 3, X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))

def Q1ab (p : R3) (a b : Fin 3) : R9 :=
  ∑ i : Fin 3, ∑ i' : Fin 3, C (1 / 2 : ℂ) * (X (i, a) * X (i', b) + X (i, b) * X (i', a)) *
    realise 0 (rot i' (pderiv i p))

theorem main_L2
    (ν : Fin 3 → ℂ) (W : Submodule ℂ R9)
    (hact : ∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W)
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (S : ℕ) (Q : R9) (hQ : Q ∈ W)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ ((ℓ + S) % 2) * eval (pt o) (realise 0 p)) :
    ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ ((ℓ - 2 + S) % 2) * eval (pt o) (realise 0 (lower2 (Xi ν p))) := by
  classical
  set α : ℕ := (ℓ + S) % 2 with hα
  have hread' : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ α * eval (fun i : Fin 3 => ((o i 0 : ℝ) : ℂ)) p := by
    intro o ho
    rw [hread o ho, eval_realise]
    rfl

  have hQT : ∀ a b : Fin 3, ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ α * eval (pt o) (Qab p a b) :=
    conj1 W hrstab ℓ p hp 0 α Q hQ hread'
  choose Gq hGqmem hGqread using hQT

  have hGfval : ∀ a b c d : Fin 3, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) (act ν c d (Gq a b)) = detC o ^ α * eval (pt o) (act ν c d (Qab p a b)) := by
    intro a b c d o ho
    have h1 : eval (pt o) (act ν c d (Gq a b)) = eval (pt o) (act ν c d (detX ^ α * Qab p a b)) :=
      eval_act_congr_orth ν c d (Gq a b) (detX ^ α * Qab p a b)
        (fun o' ho' => by rw [hGqread a b o' ho', map_mul, map_pow, eval_detX]) o ho
    rw [h1, act_detX_pow_mul, map_mul, map_pow, eval_detX]

  have hproj : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Qab p a b)) + eval (pt o) (act ν b a (Qab p a b)))) =
        eval (pt o) (realise 0 (lower2 (Xi ν p))) := by
    intro o ho
    have h6 : eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))) +
          act ν b a (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))))) =
        eval (pt o) (C (1 / 2 : ℂ) * realise 0 (lower2 (Xi ν p))) :=
      LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
        ν 0 p hharm (pt o) (rowOrth_pt o ho)
    have h7 : (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Qab p a b)) + eval (pt o) (act ν b a (Qab p a b)))) =
        2 * eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))) +
          act ν b a (X (i, a) * X (i', b) * realise 0 (pderiv i (pderiv i' p))))) := by
      have h22 : ∀ x : ℂ, (2 : ℂ) * (1 / 2 * x) = x := fun x => by ring
      simp only [Qab, act_sum, map_sum, map_add, map_mul, eval_C, Finset.mul_sum, h22]
      simp only [Finset.sum_add_distrib]
    rw [h7, h6, map_mul, eval_C]
    ring

  by_cases hℓ : 2 ≤ ℓ
  · have hpar : (ℓ - 2 + S) % 2 = α := by rw [hα]; omega
    refine ⟨∑ a : Fin 3, ∑ b : Fin 3, (act ν a b (Gq a b) + act ν b a (Gq a b)), ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
        Submodule.add_mem _ (hact _ (hGqmem a b) a b) (hact _ (hGqmem a b) b a)))
    · intro o ho
      rw [hpar, map_sum]
      simp only [map_sum, map_add, hGfval _ _ _ _ o ho]
      rw [← hproj o ho]
      simp only [Finset.mul_sum, mul_add]
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro o ho
    rw [lower2_Xi_eq_zero ν p ℓ hp (by omega), show realise 0 (0 : R3) = 0 from map_zero _]
    simp

theorem main_L1
    (ν : Fin 3 → ℂ) (W : Submodule ℂ R9)
    (hact : ∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W)
    (hrstab : ∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, ColOrth r → subR r P ∈ W)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (S : ℕ) (Q : R9) (hQ : Q ∈ W)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ ((ℓ + S) % 2) * eval (pt o) (realise 0 p)) :
    ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ ((ℓ - 1 + S) % 2) * eval (pt o) (realise 0 (lower1 (Xi ν p))) := by
  classical
  set α : ℕ := (ℓ + S) % 2 with hα
  have hread' : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q = detC o ^ α * eval (fun i : Fin 3 => ((o i 0 : ℝ) : ℂ)) p := by
    intro o ho
    rw [hread o ho, eval_realise]
    rfl
  have hQT : ∀ a b : Fin 3, ∃ Q' ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) Q' = detC o ^ (α + 1) * eval (pt o) (Q1ab p a b) :=
    conj2 W hrstab ℓ p hp 0 α Q hQ hread'
  choose Gq hGqmem hGqread using hQT
  have hGfval : ∀ a b c d : Fin 3, ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      eval (pt o) (act ν c d (Gq a b)) = detC o ^ (α + 1) * eval (pt o) (act ν c d (Q1ab p a b)) := by
    intro a b c d o ho
    have h1 : eval (pt o) (act ν c d (Gq a b)) = eval (pt o) (act ν c d (detX ^ (α + 1) * Q1ab p a b)) :=
      eval_act_congr_orth ν c d (Gq a b) (detX ^ (α + 1) * Q1ab p a b)
        (fun o' ho' => by rw [hGqread a b o' ho', map_mul, map_pow, eval_detX]) o ho
    rw [h1, act_detX_pow_mul, map_mul, map_pow, eval_detX]
  have hproj : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Q1ab p a b)) + eval (pt o) (act ν b a (Q1ab p a b)))) =
        eval (pt o) (realise 0 (lower1 (Xi ν p))) := by
    intro o ho
    have h6 : eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (C (1 / 2 : ℂ) * (X (i, a) * X (i', b) + X (i, b) * X (i', a)) *
            realise 0 (rot i' (pderiv i p))) +
          act ν b a (C (1 / 2 : ℂ) * (X (i, a) * X (i', b) + X (i, b) * X (i', a)) *
            realise 0 (rot i' (pderiv i p))))) =
        eval (pt o) (C (1 / 2 : ℂ) * realise 0 (lower1 (Xi ν p))) :=
      LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
        ν 0 p hharm (pt o) (rowOrth_pt o ho)
    have h7 : (∑ a : Fin 3, ∑ b : Fin 3, (eval (pt o) (act ν a b (Q1ab p a b)) + eval (pt o) (act ν b a (Q1ab p a b)))) =
        2 * eval (pt o) (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        C (1 / 2 : ℂ) * (act ν a b (C (1 / 2 : ℂ) * (X (i, a) * X (i', b) + X (i, b) * X (i', a)) *
            realise 0 (rot i' (pderiv i p))) +
          act ν b a (C (1 / 2 : ℂ) * (X (i, a) * X (i', b) + X (i, b) * X (i', a)) *
            realise 0 (rot i' (pderiv i p))))) := by
      have h22 : ∀ x : ℂ, (2 : ℂ) * (1 / 2 * x) = x := fun x => by ring
      simp only [Q1ab, act_sum, map_sum, map_add, map_mul, eval_C, Finset.mul_sum, h22]
      simp only [Finset.sum_add_distrib]
    rw [h7, h6, map_mul, eval_C]
    ring
  by_cases hℓ : 1 ≤ ℓ
  · have hpar : (α + 1) % 2 = (ℓ - 1 + S) % 2 := by rw [hα]; omega
    refine ⟨∑ a : Fin 3, ∑ b : Fin 3, (act ν a b (Gq a b) + act ν b a (Gq a b)), ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
        Submodule.add_mem _ (hact _ (hGqmem a b) a b) (hact _ (hGqmem a b) b a)))
    · intro o ho
      have hsq : detC o ^ 2 = 1 := detC_sq (Matrix.of o) ho
      have hd : detC o ^ ((ℓ - 1 + S) % 2) = detC o ^ (α + 1) := by
        rw [pow_eq_pow_mod_two hsq (α + 1), hpar]
      rw [hd, map_sum]
      simp only [map_sum, map_add, hGfval _ _ _ _ o ho]
      rw [← hproj o ho]
      simp only [Finset.mul_sum, mul_add]
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro o ho
    have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    have hpC : p = C (p.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr hp)
    rw [hpC, lower1_Xi_C, show realise 0 (0 : R3) = 0 from map_zero _]
    simp

end

end WsF.PT

theorem solution
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) →
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (((ℓ - 2) + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (lower₂ (Ξ ν p)))) ∧
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (((ℓ - 1) + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (lower₁ (Ξ ν p)))) := by
  intro act Ξ lower₂ lower₁ hact hrstab hread
  obtain ⟨Q, hQ, hreadQ⟩ := hread
  exact ⟨WsF.PT.main_L2 ν W hact hrstab ℓ p hp hharm (∑ a : Fin 3, (ε a : ℕ)) Q hQ hreadQ,
    WsF.PT.main_L1 ν W hact hrstab ℓ p hp hharm (∑ a : Fin 3, (ε a : ℕ)) Q hQ hreadQ⟩

end S_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable (solution)
