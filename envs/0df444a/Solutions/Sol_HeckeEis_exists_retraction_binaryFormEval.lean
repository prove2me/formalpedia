-- Prove2me | solution 1 for HeckeEis.exists_retraction_binaryFormEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1ec1989d-e087-518b-82da-30e489d1ae19

import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep
import Theorems.Thm_HeckeEis_binaryFormEval_binaryFormRepSL
import Theorems.Thm_HeckeEis_binaryFormEval_binaryFormAlphaAdj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_retraction_binaryFormEval

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "redMat projLineAct projLineAct_of_isUnit projLineAct_one projLineAct_mul projLineAct_coe_mul projLineRepSL projLineAlphaAdj BinaryForm binaryFormRepSL binaryFormAlphaAdj evalRow binaryFormEval binaryFormEval_binaryFormRepSL binaryFormEval_binaryFormAlphaAdj"
p2m_open "HeckeEis"

open MvPolynomial ModularCurve
open scoped MatrixGroups

section Points

variable (p : ℕ) [hp : Fact p.Prime]

def ptInf : ProjectiveLine (ZMod p) := ⟦⟨((1 : ZMod p), 0), isUnimodularRow_one_left 0⟩⟧

def ptFin (x : ZMod p) : ProjectiveLine (ZMod p) := ⟦⟨(x, 1), isUnimodularRow_one_right x⟩⟧

def rowInf : UnimodularRow (ZMod p) := ⟨((1 : ZMod p), 0), isUnimodularRow_one_left 0⟩
def rowFin (x : ZMod p) : UnimodularRow (ZMod p) := ⟨(x, 1), isUnimodularRow_one_right x⟩

theorem ptFin_injective : Function.Injective (ptFin p) := by
  intro x y h
  obtain ⟨u, h1, h2⟩ := Quotient.exact h
  change (u : ZMod p) * x = y at h1
  change (u : ZMod p) * 1 = 1 at h2
  rw [mul_one] at h2
  rw [← h1, h2, one_mul]

theorem ptFin_ne_ptInf (x : ZMod p) : ptFin p x ≠ ptInf p := by
  intro h
  obtain ⟨u, -, h2⟩ := Quotient.exact h
  change (u : ZMod p) * 1 = 0 at h2
  exact u.ne_zero (by simpa using h2)

theorem eq_ptInf_or_ptFin (P : ProjectiveLine (ZMod p)) : P = ptInf p ∨ ∃ x, P = ptFin p x := by
  induction P using Quotient.inductionOn with
  | h v =>
    obtain ⟨⟨a, c⟩, hac⟩ := v
    by_cases hc : c = 0
    · left
      subst hc
      obtain ⟨x, y, hxy⟩ := hac
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hxy
      apply Quotient.sound
      refine ⟨(Units.mk0 a ha)⁻¹, ?_, ?_⟩
      · change ((Units.mk0 a ha : (ZMod p)ˣ)⁻¹ : ZMod p) * a = 1
        simp [inv_mul_cancel₀ ha]
      · change ((Units.mk0 a ha)⁻¹ : ZMod p) * 0 = 0
        rw [mul_zero]
    · right
      refine ⟨a * c⁻¹, Quotient.sound ⟨(Units.mk0 c hc)⁻¹, ?_, ?_⟩⟩
      · change ((Units.mk0 c hc : (ZMod p)ˣ)⁻¹ : ZMod p) * a = a * c⁻¹
        simp [mul_comm]
      · change ((Units.mk0 c hc : (ZMod p)ˣ)⁻¹ : ZMod p) * c = 1
        simp [inv_mul_cancel₀ hc]

def ptEquiv : Option (ZMod p) ≃ ProjectiveLine (ZMod p) :=
  Equiv.ofBijective (fun o => o.elim (ptInf p) (ptFin p)) <| by
    constructor
    · rintro (_ | x) (_ | y) h
      · rfl
      · exact absurd h.symm (ptFin_ne_ptInf p y)
      · exact absurd h (ptFin_ne_ptInf p x)
      · rw [ptFin_injective p h]
    · intro P
      rcases eq_ptInf_or_ptFin p P with h | ⟨x, h⟩
      · exact ⟨none, h.symm⟩
      · exact ⟨some x, h.symm⟩

@[reducible] def fintypeProjectiveLine : Fintype (ProjectiveLine (ZMod p)) := Fintype.ofEquiv _ (ptEquiv p)

attribute [local instance] fintypeProjectiveLine

theorem sum_projectiveLine {M : Type*} [AddCommMonoid M] (f : ProjectiveLine (ZMod p) → M) :
    ∑ P, f P = f (ptInf p) + ∑ x : ZMod p, f (ptFin p x) := by
  rw [← Equiv.sum_comp (ptEquiv p), Fintype.sum_option]
  rfl

theorem projLineAct_bijective_coe (g : SL(2, ℤ)) :
    Function.Bijective (projLineAct p (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
  refine Finite.injective_iff_bijective.mp (Function.LeftInverse.injective
    (g := projLineAct p ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) fun P => ?_)
  rw [← projLineAct_coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, projLineAct_one]

theorem projLineAct_bijective_diag (ℓ : ℕ) (hℓ : p.Coprime ℓ) :
    Function.Bijective (projLineAct p !![(ℓ : ℤ), 0; 0, 1]) := by

  set u : (ZMod p)ˣ := ZMod.unitOfCoprime ℓ hℓ.symm with hu
  set m : ℤ := (((u⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℤ) with hm
  have hmul : redMat p (!![(ℓ : ℤ), 0; 0, 1] * !![m, 0; 0, 1]) = 1 := by
    have hml : (ℓ : ZMod p) * (m : ZMod p) = 1 := by
      rw [hm, Int.cast_natCast, ZMod.natCast_zmod_val,
        ← ZMod.coe_unitOfCoprime ℓ hℓ.symm, ← hu, Units.mul_inv]
    have hml' : ((ℓ : ℤ) : ZMod p) * (m : ZMod p) = 1 := by rw [Int.cast_natCast]; exact hml
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [redMat, Matrix.map_apply, hml, hml']
  have hdet : IsUnit (redMat p !![(ℓ : ℤ), 0; 0, 1]).det := by
    have h1 : (redMat p !![(ℓ : ℤ), 0; 0, 1]).det = (ℓ : ZMod p) := by
      simp [redMat, Matrix.det_fin_two, Matrix.map_apply]
    rw [h1]; exact (ZMod.isUnit_iff_coprime ℓ p).mpr hℓ.symm
  have hdet' : IsUnit (redMat p !![m, 0; 0, 1]).det := by
    have hml : (ℓ : ZMod p) * (m : ZMod p) = 1 := by
      rw [hm, Int.cast_natCast, ZMod.natCast_zmod_val,
        ← ZMod.coe_unitOfCoprime ℓ hℓ.symm, ← hu, Units.mul_inv]
    have h1 : (redMat p !![m, 0; 0, 1]).det = (m : ZMod p) := by
      simp [redMat, Matrix.det_fin_two, Matrix.map_apply]
    rw [h1]
    exact ⟨⟨(m : ZMod p), (ℓ : ZMod p), by rw [mul_comm]; exact hml, hml⟩, rfl⟩
  refine Finite.injective_iff_bijective.mp (Function.LeftInverse.injective
    (g := projLineAct p !![m, 0; 0, 1]) fun P => ?_)
  rw [← projLineAct_mul p _ _ hdet hdet', show projLineAct p (!![(ℓ : ℤ), 0; 0, 1] * !![m, 0; 0, 1]) = id from ?_]
  · rfl
  · funext Q
    have h1 : IsUnit (redMat p (!![(ℓ : ℤ), 0; 0, 1] * !![m, 0; 0, 1])).det := by rw [hmul, Matrix.det_one]; exact isUnit_one
    rw [projLineAct_of_isUnit p _ h1]
    have : ProjectiveLine.vecMul (redMat p (!![(ℓ : ℤ), 0; 0, 1] * !![m, 0; 0, 1])) h1
        = ProjectiveLine.vecMul (R := ZMod p) 1 (by rw [Matrix.det_one]; exact isUnit_one) := by
      congr 1
    rw [this, ProjectiveLine.vecMul_one]
    rfl

end Points

section Split

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

attribute [local instance] fintypeProjectiveLine

def lagr (x : ZMod p) : MvPolynomial (Fin 2) K :=
  X 1 ^ (p - 1) - (X 0 - C (ZMod.castHom (dvd_refl p) K x) * X 1) ^ (p - 1)

theorem lagr_isHomogeneous (x : ZMod p) : (lagr p K x).IsHomogeneous (p - 1) := by
  apply MvPolynomial.IsHomogeneous.sub
  · simpa using (MvPolynomial.isHomogeneous_X K (1 : Fin 2)).pow (p - 1)
  · simpa using ((MvPolynomial.isHomogeneous_X K (0 : Fin 2)).sub
      ((MvPolynomial.isHomogeneous_X K (1 : Fin 2)).C_mul _)).pow (p - 1)

def lagrF (x : ZMod p) : BinaryForm K (p - 1) :=
  ⟨lagr p K x, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (lagr_isHomogeneous p K x)⟩

theorem one_lt_p : 1 < p := hp.out.one_lt

theorem evalRow_lagr_fin (x y : ZMod p) :
    evalRow p K (lagr p K x) (rowFin p y) = if y = x then 1 else 0 := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_p p)
  simp only [evalRow, rowFin, lagr, map_sub, map_pow, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_one, mul_one, one_pow]
  rw [← map_sub, ← map_pow]
  by_cases h : y = x
  · subst h
    rw [sub_self, zero_pow hp1, map_zero, sub_zero, if_pos rfl]
  · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h), map_one, sub_self, if_neg h]

theorem evalRow_lagr_inf (x : ZMod p) : evalRow p K (lagr p K x) (rowInf p) = -1 := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_p p)
  simp [evalRow, rowInf, lagr, zero_pow hp1]

def lagrMap : (ProjectiveLine (ZMod p) → K) →ₗ[K] BinaryForm K (p - 1) :=
  ∑ x : ZMod p, (LinearMap.proj (ptFin p x) : (ProjectiveLine (ZMod p) → K) →ₗ[K] K).smulRight (lagrF p K x)

theorem lagrMap_apply (f : ProjectiveLine (ZMod p) → K) :
    lagrMap p K f = ∑ x : ZMod p, f (ptFin p x) • lagrF p K x := by
  simp [lagrMap, LinearMap.sum_apply, LinearMap.smulRight_apply]

def sumMap : (ProjectiveLine (ZMod p) → K) →ₗ[K] K :=
  ∑ P : ProjectiveLine (ZMod p), LinearMap.proj P

theorem sumMap_apply (f : ProjectiveLine (ZMod p) → K) : sumMap p K f = ∑ P, f P := by
  simp [sumMap, LinearMap.sum_apply]

def proj0 : (ProjectiveLine (ZMod p) → K) →ₗ[K] (ProjectiveLine (ZMod p) → K) :=
  LinearMap.id - (sumMap p K).smulRight (fun _ => (1 : K))

theorem proj0_apply (f : ProjectiveLine (ZMod p) → K) : proj0 p K f = f - (∑ P, f P) • fun _ => (1 : K) := by
  simp [proj0, sumMap_apply]

theorem sum_one_projectiveLine : (∑ _P : ProjectiveLine (ZMod p), (1 : K)) = 1 := by
  rw [sum_projectiveLine, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    CharP.cast_eq_zero, add_zero]

theorem sumMap_proj0 (f : ProjectiveLine (ZMod p) → K) : sumMap p K (proj0 p K f) = 0 := by
  rw [sumMap_apply, proj0_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ]
  rw [nsmul_eq_mul, ← Finset.card_univ, show ((Finset.univ : Finset (ProjectiveLine (ZMod p))).card : K)
    = ∑ _P : ProjectiveLine (ZMod p), (1 : K) from by simp, sum_one_projectiveLine, one_mul, sub_self]

theorem binaryFormEval_lagrMap_fin (f : ProjectiveLine (ZMod p) → K) (y : ZMod p) :
    binaryFormEval p K (lagrMap p K f) (ptFin p y) = f (ptFin p y) := by
  rw [lagrMap_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  have : ∀ x, binaryFormEval p K (lagrF p K x) (ptFin p y) = if y = x then 1 else 0 := fun x =>
    evalRow_lagr_fin p K x y
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem binaryFormEval_lagrMap_inf (f : ProjectiveLine (ZMod p) → K) :
    binaryFormEval p K (lagrMap p K f) (ptInf p) = -∑ x : ZMod p, f (ptFin p x) := by
  rw [lagrMap_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  have : ∀ x, binaryFormEval p K (lagrF p K x) (ptInf p) = -1 := fun x => evalRow_lagr_inf p K x
  simp only [this, mul_neg, mul_one, Finset.sum_neg_distrib]

theorem binaryFormEval_lagrMap_of_sum_eq_zero (g : ProjectiveLine (ZMod p) → K) (hg : ∑ P, g P = 0) :
    binaryFormEval p K (lagrMap p K g) = g := by
  funext P
  rcases eq_ptInf_or_ptFin p P with rfl | ⟨y, rfl⟩
  · rw [binaryFormEval_lagrMap_inf]
    rw [sum_projectiveLine] at hg
    linear_combination (-1 : K) * hg
  · exact binaryFormEval_lagrMap_fin p K g y

theorem sum_pow_cast (i : ℕ) (hi : i ≤ p - 1) :
    (∑ x : ZMod p, (ZMod.castHom (dvd_refl p) K x) ^ i) = if i = p - 1 then -1 else 0 := by
  have hcast : (∑ x : ZMod p, (ZMod.castHom (dvd_refl p) K x) ^ i)
      = ZMod.castHom (dvd_refl p) K (∑ x : ZMod p, x ^ i) := by
    rw [map_sum]; simp only [map_pow]
  rw [hcast]
  rcases hi.lt_or_eq with hlt | rfl
  · rw [FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) _ (by rwa [ZMod.card]), map_zero, if_neg hlt.ne]
  · rw [if_pos rfl]
    have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_p p)
    have : (∑ x : ZMod p, x ^ (p - 1)) = ∑ x : ZMod p, (if x = 0 then 0 else 1) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x = 0
      · rw [hx, zero_pow hp1, if_pos rfl]
      · rw [ZMod.pow_card_sub_one_eq_one hx, if_neg hx]
    rw [this, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.cast_sub (one_lt_p p).le, Nat.cast_one, ZMod.natCast_self, zero_sub, map_neg, map_one]

theorem prod_support_eq (d : Fin 2 →₀ ℕ) (y : Fin 2 → K) :
    (∏ i ∈ d.support, y i ^ d i) = y 0 ^ d 0 * y 1 ^ d 1 := by
  rw [Finset.prod_subset (Finset.subset_univ d.support) (fun i _ hi => by
    have h0 : d i = 0 := by simpa [Finsupp.mem_support_iff] using hi
    rw [h0, pow_zero]), Fin.prod_univ_two]

theorem evalRow_rowFin_eq (F : MvPolynomial (Fin 2) K) (x : ZMod p) :
    evalRow p K F (rowFin p x) = ∑ d ∈ F.support, coeff d F * (ZMod.castHom (dvd_refl p) K x) ^ (d 0) := by
  unfold evalRow rowFin
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [prod_support_eq]
  simp

theorem evalRow_rowInf_eq (F : MvPolynomial (Fin 2) K) :
    evalRow p K F (rowInf p) = ∑ d ∈ F.support, coeff d F * (0 : K) ^ (d 1) := by
  unfold evalRow rowInf
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [prod_support_eq]
  simp

theorem deg_of_mem_support {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ F.support) : d 0 + d 1 = n := by
  have h := hF (MvPolynomial.mem_support_iff.mp hd)
  have hdeg : ∑ i ∈ d.support, d i = n := by
    simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h
  rwa [Finset.sum_subset (Finset.subset_univ d.support) (fun i _ hi => by
    simpa [Finsupp.mem_support_iff] using hi), Fin.sum_univ_two] at hdeg

theorem eq_of_mem_support {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n)
    {d d' : Fin 2 →₀ ℕ} (hd : d ∈ F.support) (hd' : d' ∈ F.support) (h0 : d 0 = d' 0) : d = d' := by
  have h1 : d 1 = d' 1 := by
    have := deg_of_mem_support K hF hd; have := deg_of_mem_support K hF hd'; omega
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem evalRow_inf_add_sum_fin {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous (p - 1)) :
    evalRow p K F (rowInf p) + ∑ x : ZMod p, evalRow p K F (rowFin p x) = 0 := by
  simp only [evalRow_rowInf_eq, evalRow_rowFin_eq]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun d hd => ?_
  have h01 := deg_of_mem_support K hF hd
  rw [← Finset.mul_sum, ← mul_add, sum_pow_cast p K (d 0) (by omega)]
  by_cases h1 : d 1 = 0
  · rw [h1, pow_zero, if_pos (by omega), add_neg_cancel, mul_zero]
  · rw [zero_pow h1, if_neg (by omega), add_zero, mul_zero]

theorem eq_zero_of_evalRow_rowFin_eq_zero {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous (p - 1))
    (h : ∀ x : ZMod p, evalRow p K F (rowFin p x) = 0) : F = 0 := by
  classical
  set f : Polynomial K := ∑ d ∈ F.support, Polynomial.C (coeff d F) * Polynomial.X ^ (d 0) with hf
  have heval : ∀ x : ZMod p, Polynomial.eval (ZMod.castHom (dvd_refl p) K x) f = 0 := by
    intro x
    rw [hf, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← evalRow_rowFin_eq]
    exact h x
  have hdeg : f.natDegree < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_) (Nat.sub_lt hp.out.pos one_pos)
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := deg_of_mem_support K hF hd
    omega
  have hf0 : f = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero f (ZMod.castHom (dvd_refl p) K).injective heval hdeg
  have hcoeff : ∀ d ∈ F.support, coeff d F = 0 := by
    intro d hd
    have hc : f.coeff (d 0) = coeff d F := by
      rw [hf, Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single_of_mem d hd (fun d' hd' hne => if_neg (fun h0 => hne
        (eq_of_mem_support K hF hd' hd h0.symm)))]
      rw [if_pos rfl]
    rw [← hc, hf0, Polynomial.coeff_zero]
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hd : d ∈ F.support
  · exact hcoeff d hd
  · simpa [MvPolynomial.mem_support_iff] using hd

theorem binaryFormEval_injective' : Function.Injective (binaryFormEval p K) := by
  refine (injective_iff_map_eq_zero _).mpr fun F hF => ?_
  apply Subtype.ext
  refine eq_zero_of_evalRow_rowFin_eq_zero p K ((MvPolynomial.mem_homogeneousSubmodule _ _).mp F.2) fun x => ?_
  have := congrFun hF (ptFin p x)
  exact this

theorem sum_binaryFormEval (F : BinaryForm K (p - 1)) : (∑ P, binaryFormEval p K F P) = 0 := by
  rw [sum_projectiveLine]
  exact evalRow_inf_add_sum_fin p K ((MvPolynomial.mem_homogeneousSubmodule _ _).mp F.2)

def retraction : (ProjectiveLine (ZMod p) → K) →ₗ[K] BinaryForm K (p - 1) :=
  lagrMap p K ∘ₗ proj0 p K

theorem binaryFormEval_retraction (h : ProjectiveLine (ZMod p) → K) :
    binaryFormEval p K (retraction p K h) = proj0 p K h :=
  binaryFormEval_lagrMap_of_sum_eq_zero p K _ (by rw [← sumMap_apply]; exact sumMap_proj0 p K h)

theorem retraction_comp_binaryFormEval : retraction p K ∘ₗ binaryFormEval p K = LinearMap.id := by
  refine LinearMap.ext fun F => binaryFormEval_injective' p K ?_
  rw [LinearMap.comp_apply, binaryFormEval_retraction, proj0_apply, sum_binaryFormEval, zero_smul, sub_zero,
    LinearMap.id_apply]

theorem proj0_comp_bijective (σ : ProjectiveLine (ZMod p) → ProjectiveLine (ZMod p)) (hσ : Function.Bijective σ)
    (f : ProjectiveLine (ZMod p) → K) : proj0 p K (f ∘ σ) = proj0 p K f ∘ σ := by
  rw [proj0_apply, proj0_apply]
  have hs : (∑ P, (f ∘ σ) P) = ∑ P, f P := hσ.sum_comp f
  rw [hs]
  funext P
  rfl

theorem projLineRepSL_eq_comp (g : SL(2, ℤ)) (f : ProjectiveLine (ZMod p) → K) :
    projLineRepSL p K g f = f ∘ projLineAct p (g : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem projLineAlphaAdj_eq_comp (ℓ : ℕ) (f : ProjectiveLine (ZMod p) → K) :
    projLineAlphaAdj p K ℓ f = f ∘ projLineAct p !![(ℓ : ℤ), 0; 0, 1] := rfl

theorem retraction_equivariant (g : SL(2, ℤ)) :
    retraction p K ∘ₗ projLineRepSL p K g = binaryFormRepSL K (p - 1) g ∘ₗ retraction p K := by
  refine LinearMap.ext fun f => binaryFormEval_injective' p K ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, binaryFormEval_retraction,
    ← LinearMap.comp_apply (f := binaryFormEval p K), binaryFormEval_binaryFormRepSL, LinearMap.comp_apply,
    binaryFormEval_retraction, projLineRepSL_eq_comp, projLineRepSL_eq_comp,
    proj0_comp_bijective p K _ (projLineAct_bijective_coe p g)]

theorem retraction_alpha (ℓ : ℕ) (hℓ : p.Coprime ℓ) :
    retraction p K ∘ₗ projLineAlphaAdj p K ℓ = binaryFormAlphaAdj K (p - 1) ℓ ∘ₗ retraction p K := by
  refine LinearMap.ext fun f => binaryFormEval_injective' p K ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, binaryFormEval_retraction,
    ← LinearMap.comp_apply (f := binaryFormEval p K), binaryFormEval_binaryFormAlphaAdj p K ℓ hℓ,
    LinearMap.comp_apply, binaryFormEval_retraction, projLineAlphaAdj_eq_comp, projLineAlphaAdj_eq_comp,
    proj0_comp_bijective p K _ (projLineAct_bijective_diag p ℓ hℓ)]

theorem exists_retraction_binaryFormEval' :
    ∃ r : (ProjectiveLine (ZMod p) → K) →ₗ[K] BinaryForm K (p - 1),
      r ∘ₗ binaryFormEval p K = LinearMap.id ∧
      (∀ g : SL(2, ℤ), r ∘ₗ projLineRepSL p K g = binaryFormRepSL K (p - 1) g ∘ₗ r) ∧
      (∀ ℓ : ℕ, p.Coprime ℓ → r ∘ₗ projLineAlphaAdj p K ℓ = binaryFormAlphaAdj K (p - 1) ℓ ∘ₗ r) :=
  ⟨retraction p K, retraction_comp_binaryFormEval p K, retraction_equivariant p K, retraction_alpha p K⟩

end Split

end HeckeEis

open scoped MatrixGroups in
theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ∃ r : (ModularCurve.ProjectiveLine (ZMod p) → K) →ₗ[K] HeckeEis.BinaryForm K (p - 1),
      r ∘ₗ HeckeEis.binaryFormEval p K = LinearMap.id ∧
      (∀ g : SL(2, ℤ), r ∘ₗ HeckeEis.projLineRepSL p K g = HeckeEis.binaryFormRepSL K (p - 1) g ∘ₗ r) ∧
      (∀ ℓ : ℕ, p.Coprime ℓ →
        r ∘ₗ HeckeEis.projLineAlphaAdj p K ℓ = HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ ∘ₗ r) :=
  HeckeEis.exists_retraction_binaryFormEval' p K

end

end S_HeckeEis_exists_retraction_binaryFormEval
end P2MW
export P2MW.S_HeckeEis_exists_retraction_binaryFormEval (solution)
