-- Prove2me | solution 1 for MTT.Cohomology.reflection_class
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T16:19:42.04693+00:00
-- url     : https://prove2.me/submissions/b65c560e-ff07-4802-bc88-856b821148e6

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MTT.Cohomology


namespace P2MSE

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### The coefficient action is a monoid homomorphism -/

theorem act_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A P = MvPolynomial.bind₁ (fun i : Fin 2 =>
      ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P := rfl

theorem act_one (P : Binary R) : act 1 P = P := by
  rw [act_apply]
  have h : (fun i : Fin 2 => ∑ a : Fin 2, ((1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) •
      MvPolynomial.X a) = fun i : Fin 2 => (MvPolynomial.X i : Binary R) := by
    funext i
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h, MvPolynomial.bind₁_X_left, AlgHom.id_apply]

theorem act_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act (A * B) P = act A (act B P) := by
  simp only [act_apply]
  rw [MvPolynomial.bind₁_bind₁]
  have hfun : (fun i : Fin 2 => (MvPolynomial.bind₁
        (fun j : Fin 2 => (∑ a : Fin 2, (A a j : R) • MvPolynomial.X a : Binary R)))
        (∑ a : Fin 2, (B a i : R) • MvPolynomial.X a : Binary R))
      = fun i : Fin 2 => (∑ a : Fin 2, ((A * B) a i : R) • MvPolynomial.X a : Binary R) := by
    funext i
    rw [map_sum]
    simp only [map_smul, MvPolynomial.bind₁_X_right, Fin.sum_univ_two, Matrix.mul_apply]
    match_scalars <;> push_cast <;> ring
  rw [hfun]

theorem act_add (A : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Binary R) :
    act A (P + Q) = act A P + act A Q := map_add _ _ _

theorem reflection_add (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (φ + ψ) = reflection φ + reflection ψ := by
  funext D; simp [reflection, act_add]

theorem reflection_smul (c : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (c • φ) = c • reflection φ := by
  funext D; simp [reflection]

end P2MSE

namespace P2MRC

open MvPolynomial

/-! ### The fractional-linear action in coordinates -/

theorem frac_infty (g : Matrix (Fin 2) (Fin 2) ℤ) :
    fractional g OnePoint.infty
      = if g 1 0 = 0 then OnePoint.infty else ((((g 0 0 : ℤ) : ℚ) / ((g 1 0 : ℤ) : ℚ)) : Cusp) :=
  rfl

theorem frac_coe (g : Matrix (Fin 2) (Fin 2) ℤ) (r : ℚ) :
    fractional g ((r : ℚ) : Cusp)
      = if ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) = 0 then OnePoint.infty
        else (((((g 0 0 : ℤ) : ℚ) * r + ((g 0 1 : ℤ) : ℚ)) /
          (((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ))) : Cusp) :=
  rfl

/-- Left multiplication by a matrix with bottom row `(0,1)` composes with the action. -/
theorem frac_upper_comp (a b : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional !![a, b; 0, 1] (fractional g x) = fractional (!![a, b; 0, 1] * g) x := by
  have u00 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a := by simp
  have u01 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = b := by simp
  have u10 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  have u11 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simp
  have e00 : (!![a, b; 0, 1] * g) 0 0 = a * g 0 0 + b * g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (!![a, b; 0, 1] * g) 0 1 = a * g 0 1 + b * g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (!![a, b; 0, 1] * g) 1 0 = g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (!![a, b; 0, 1] * g) 1 1 = g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  induction x using OnePoint.rec with
  | infty =>
      rw [frac_infty g, frac_infty (!![a, b; 0, 1] * g), e00, e10]
      by_cases h : g 1 0 = 0
      · rw [if_pos h, if_pos h, frac_infty, u10, if_pos rfl]
      · rw [if_neg h, if_neg h, frac_coe, u10, u11, u00, u01, if_neg (by norm_num)]
        have hq : ((g 1 0 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h
        congr 1
        push_cast
        rw [zero_mul, zero_add, div_one]
        field_simp
  | coe r =>
      rw [frac_coe g r, frac_coe (!![a, b; 0, 1] * g) r, e00, e01, e10, e11]
      by_cases h : ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) = 0
      · rw [if_pos h, if_pos h, frac_infty, u10, if_pos rfl]
      · have hD : ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) ≠ 0 := h
        rw [if_neg h, if_neg h, frac_coe, u10, u11, u00, u01, if_neg (by norm_num)]
        congr 1
        push_cast
        rw [zero_mul, zero_add, div_one, eq_div_iff hD, add_mul, mul_assoc,
          div_mul_cancel₀ _ hD]
        ring

/-- The reflection matrix. -/
abbrev Jm : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

/-- Right multiplication by the reflection matrix composes with the action. -/
theorem frac_comp_J (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional g (fractional Jm x) = fractional (g * Jm) x := by
  have e00 : (g * Jm) 0 0 = -g 0 0 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * Jm) 0 1 = g 0 1 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * Jm) 1 0 = -g 1 0 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * Jm) 1 1 = g 1 1 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  induction x using OnePoint.rec with
  | infty =>
      rw [frac_infty Jm]
      norm_num [Jm]
      rw [frac_infty g, frac_infty (g * Jm), e00, e10]
      by_cases h : g 1 0 = 0
      · rw [if_pos h, if_pos (by simp [h])]
      · rw [if_neg h, if_neg (by simpa using h)]
        push_cast
        rw [neg_div_neg_eq]
  | coe r =>
      rw [frac_coe Jm r]
      norm_num [Jm]
      rw [frac_coe g (-r), frac_coe (g * Jm) r, e00, e01, e10, e11]
      by_cases h : ((g 1 0 : ℤ) : ℚ) * (-r) + ((g 1 1 : ℤ) : ℚ) = 0
      · rw [if_pos h, if_pos (by push_cast; push_cast at h; linear_combination h)]
      · rw [if_neg h, if_neg (by push_cast; push_cast at h ⊢; intro hc; exact h (by
          linear_combination hc))]
        congr 1
        push_cast
        ring

end P2MRC


namespace P2MRC

open MvPolynomial P2MSE

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ### `fractional` restricted to `SL(2,ℤ)` is the cusp action -/

theorem cuspAct_infty (g : SL2) :
    cuspAct g OnePoint.infty
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_infty_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_coe (g : SL2) (r : ℚ) :
    cuspAct g ((r : ℚ) : Cusp)
      = if (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) = 0 then OnePoint.infty
        else (((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℚ)) /
          ((((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_some_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem frac_eq_cuspAct (g : SL2) (x : Cusp) :
    fractional (g : Matrix (Fin 2) (Fin 2) ℤ) x = cuspAct g x := by
  induction x using OnePoint.rec with
  | infty => rw [frac_infty, cuspAct_infty]
  | coe r => rw [frac_coe, cuspAct_coe]

/-! ### Conjugation by the reflection -/

theorem Jm_mul_Jm : Jm * Jm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply]

theorem det_Jm : Jm.det = -1 := by simp [Jm, Matrix.det_fin_two_of]

/-- `J γ J`, an element of `SL(2,ℤ)` again. -/
def conjJ (g : SL2) : SL2 :=
  ⟨Jm * (g : Matrix (Fin 2) (Fin 2) ℤ) * Jm, by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, det_Jm]; ring⟩

theorem conjJ_val (g : SL2) :
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) = Jm * (g : Matrix (Fin 2) (Fin 2) ℤ) * Jm := rfl

theorem frac_J_cuspAct (g : SL2) (x : Cusp) :
    fractional Jm (cuspAct g x) = cuspAct (conjJ g) (fractional Jm x) := by
  rw [← frac_eq_cuspAct, ← frac_eq_cuspAct, conjJ_val]
  show fractional !![(-1 : ℤ), 0; 0, 1] (fractional (g : Matrix (Fin 2) (Fin 2) ℤ) x) = _
  rw [frac_upper_comp, frac_comp_J, mul_assoc, mul_assoc, Jm_mul_Jm, mul_one]

/-! ### The reflection preserves the space of classes -/

variable {R : Type*} [CommRing R] {n : ℕ}

theorem act_mem_sym (A : Matrix (Fin 2) (Fin 2) ℤ) {P : Binary R}
    (hP : P ∈ MTT.Cohomology.Sym R n) : act A P ∈ MTT.Cohomology.Sym R n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  have hg : ∀ i : Fin 2,
      (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R).IsHomogeneous 1 := by
    intro i
    have hmem : (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R)
        ∈ MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X _ _)
    exact hmem
  have h := hP.aeval (g := fun i : Fin 2 =>
    (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R)) hg
  rw [one_mul] at h
  exact h

end P2MRC


namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

theorem conjJ_entries (g : SL2) :
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [conjJ_val, Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail]

theorem conjJ_mem_Gamma1 {g : SL2} (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    conjJ g ∈ CongruenceSubgroup.Gamma1 N := by
  obtain ⟨h00, h10, h11⟩ := conjJ_entries g
  rw [CongruenceSubgroup.Gamma1_mem] at hg ⊢
  refine ⟨by rw [h00]; exact hg.1, by rw [h11]; exact hg.2.1, ?_⟩
  rw [h10]
  push_cast
  rw [hg.2.2, neg_zero]

theorem conjJ_mem_Gamma0 {g : SL2} (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    conjJ g ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨-, h10, -⟩ := conjJ_entries g
  rw [CongruenceSubgroup.Gamma0_mem] at hg ⊢
  rw [h10]
  push_cast
  rw [hg, neg_zero]

/-- The key conjugation identity on the coefficient action. -/
theorem act_conj (g : SL2) (P : Binary R) :
    act Jm (act (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) P)
      = act ((g : Matrix (Fin 2) (Fin 2) ℤ) * Jm) P := by
  rw [← act_mul, conjJ_val, ← mul_assoc, ← mul_assoc, Jm_mul_Jm, one_mul]

/-- The reflection of a class is a class. -/
theorem reflection_mem (φ : Hc N n R) : reflection φ.val ∈ Hc N n R := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun γ x y => ?_⟩
  · exact act_mem_sym _ (φ.2.1 _ _)
  · show act Jm _ + act Jm _ = act Jm _
    rw [← map_add]
    exact congrArg _ (φ.2.2.1 _ _ _)
  · show act Jm (φ.val (fractional Jm (cuspAct γ.val x), fractional Jm (cuspAct γ.val y)))
      = act (γ.val : Matrix (Fin 2) (Fin 2) ℤ)
          (act Jm (φ.val (fractional Jm x, fractional Jm y)))
    rw [frac_J_cuspAct, frac_J_cuspAct,
      φ.2.2.2 ⟨conjJ γ.val, conjJ_mem_Gamma1 γ.2⟩ (fractional Jm x) (fractional Jm y),
      act_conj, act_mul]

/-- The reflection preserves the nebentype law. -/
theorem reflection_char (φ : Hc N n R) (e : ZMod N → R)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y)
        = e ((γ.val : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) •
          act (γ.val : Matrix (Fin 2) (Fin 2) ℤ) (φ.val (x, y)))
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = e ((γ.val : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) •
        act (γ.val : Matrix (Fin 2) (Fin 2) ℤ) (reflection φ.val (x, y)) := by
  obtain ⟨-, -, h11⟩ := conjJ_entries γ.val
  show act Jm (φ.val (fractional Jm (cuspAct γ.val x), fractional Jm (cuspAct γ.val y)))
    = _ • act (γ.val : Matrix (Fin 2) (Fin 2) ℤ)
        (act Jm (φ.val (fractional Jm x, fractional Jm y)))
  rw [frac_J_cuspAct, frac_J_cuspAct,
    h ⟨conjJ γ.val, conjJ_mem_Gamma0 γ.2⟩ (fractional Jm x) (fractional Jm y),
    h11, map_smul, act_conj, act_mul]

end P2MRC


namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- The unipotent matrices, all of which lie in `Γ₁(N)`. -/
abbrev Um (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, t; 0, 1]

def USL (t : ℤ) : SL2 := ⟨Um t, by simp [Um, Matrix.det_fin_two_of]⟩

theorem USL_val (t : ℤ) : ((USL t : SL2) : Matrix (Fin 2) (Fin 2) ℤ) = Um t := rfl

theorem USL_mem (N : ℕ) (t : ℤ) : USL t ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [USL_val, Um]

theorem frac_J_comp (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional Jm (fractional g x) = fractional (Jm * g) x :=
  frac_upper_comp (-1) 0 g x

theorem frac_U_comp (t : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional (Um t) (fractional g x) = fractional (Um t * g) x :=
  frac_upper_comp 1 t g x

/-- The reflection turns the slash operator by `A` into the one by `A'`, provided the two
conjugation identities hold with a unipotent correction `Um t ∈ Γ₁(N)`. -/
theorem slash_refl_key (φ : Hc N n R) (t : ℤ) (A A' : Matrix (Fin 2) (Fin 2) ℤ)
    (h1 : A * Jm = Um t * (Jm * A'))
    (h2 : Jm * A.adjugate * Um t = A'.adjugate * Jm) :
    reflection (slash A φ.val) = slash A' (reflection φ.val) := by
  funext D
  have hcusp : ∀ x : Cusp, fractional A (fractional Jm x)
      = cuspAct (USL t) (fractional (Jm * A') x) := by
    intro x
    rw [frac_comp_J, h1, ← frac_U_comp, ← frac_eq_cuspAct, USL_val]
  show act Jm (act A.adjugate (φ.val (fractional A (fractional Jm D.1),
      fractional A (fractional Jm D.2))))
    = act A'.adjugate (act Jm (φ.val (fractional Jm (fractional A' D.1),
      fractional Jm (fractional A' D.2))))
  rw [hcusp, hcusp, φ.2.2.2 ⟨USL t, USL_mem N t⟩ _ _]
  show act Jm (act A.adjugate (act (Um t) _)) = _
  rw [← act_mul, ← act_mul, h2, act_mul, frac_J_comp, frac_J_comp]

/-! ### The reindexing of the Hecke coset representatives -/

def sigmaFin (l : ℕ) (b : Fin l) : Fin l :=
  ⟨if b.val = 0 then 0 else l - b.val, by
    have hb := b.isLt
    split <;> omega⟩

theorem sigmaFin_val (l : ℕ) (b : Fin l) :
    (sigmaFin l b).val = if b.val = 0 then 0 else l - b.val := rfl

theorem sigmaFin_involutive (l : ℕ) : Function.Involutive (sigmaFin l) := by
  intro b
  have hb := b.isLt
  apply Fin.ext
  rw [sigmaFin_val, sigmaFin_val]
  by_cases h : b.val = 0
  · simp [h]
  · rw [if_neg h, if_neg (by omega : ¬ (l - b.val = 0))]
    omega

def sigmaEquiv (l : ℕ) : Fin l ≃ Fin l :=
  Function.Involutive.toPerm _ (sigmaFin_involutive l)

end P2MRC


namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

theorem reflection_zero : reflection (0 : (Cusp × Cusp) → Binary R) = 0 := by
  funext D; show act Jm 0 = 0; rw [map_zero]

theorem reflection_sum {ι : Type*} (s : Finset ι) (f : ι → (Cusp × Cusp) → Binary R) :
    reflection (∑ b ∈ s, f b) = ∑ b ∈ s, reflection (f b) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, reflection_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, reflection_add, ih]

/-! ### The three coset identities -/

theorem refl_slash_b (φ : Hc N n R) (l : ℕ) (b : Fin l) :
    reflection (slash !![1, (b.val : ℤ); 0, (l : ℤ)] φ.val)
      = slash !![1, ((sigmaFin l b).val : ℤ); 0, (l : ℤ)] (reflection φ.val) := by
  by_cases h : b.val = 0
  · have hb0 : ((b.val : ℕ) : ℤ) = 0 := by rw [h]; rfl
    have hs0 : (((sigmaFin l b).val : ℕ) : ℤ) = 0 := by
      rw [sigmaFin_val, if_pos h]; rfl
    rw [hb0, hs0]
    refine slash_refl_key φ 0 _ _ ?_ ?_ <;>
      (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of])
  · have hs : (((sigmaFin l b).val : ℕ) : ℤ) = (l : ℤ) - ((b.val : ℕ) : ℤ) := by
      rw [sigmaFin_val, if_neg h]
      have hb := b.isLt
      omega
    rw [hs]
    refine slash_refl_key φ 1 _ _ ?_ ?_ <;>
      (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of] <;> ring)

theorem refl_slash_diag (φ : Hc N n R) (l : ℕ) :
    reflection (slash !![(l : ℤ), 0; 0, 1] φ.val)
      = slash !![(l : ℤ), 0; 0, 1] (reflection φ.val) := by
  refine slash_refl_key φ 0 _ _ ?_ ?_ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of])

/-- The reflection commutes with the prime Hecke operator. -/
theorem reflection_primeHecke (e : R) (l : ℕ) (φ : Hc N n R) :
    reflection (primeHecke e l φ.val) = primeHecke e l (reflection φ.val) := by
  have hsum : (∑ b : Fin l, reflection (slash !![1, (b.val : ℤ); 0, (l : ℤ)] φ.val))
      = ∑ b : Fin l, slash !![1, (b.val : ℤ); 0, (l : ℤ)] (reflection φ.val) :=
    Fintype.sum_equiv (sigmaEquiv l) _ _ (fun b => refl_slash_b φ l b)
  simp only [primeHecke]
  rw [reflection_add, reflection_smul, reflection_sum, refl_slash_diag, hsum]

end P2MRC


open P2MRC in
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) :
    (∃ ψ : Hc N n R, ψ.val = reflection φ.val) ∧
    (∀ (e : R) (l : ℕ), reflection (primeHecke e l φ.val)
        = primeHecke e l (reflection φ.val)) ∧
    (∀ (e : ZMod N → R),
      (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x, y))) →
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection φ.val (x, y))) :=
  ⟨⟨⟨reflection φ.val, reflection_mem φ⟩, rfl⟩,
   fun e l => reflection_primeHecke e l φ,
   fun e h γ x y => reflection_char φ e h γ x y⟩

