-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pairing_pow_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:59.762223+00:00
-- url     : https://prove2.me/submissions/c76547a5-68e0-49cd-8e11-16a4df4c7817

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportional
import Theorems.Thm_ReciprocityTheory_PGsh_cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.PGsh MvPolynomial
namespace GlobalTheory.DetPowPairing
section General
variable {C : Type} [CommRing C] {κ : Type}
end General
variable {C : Type} [CommRing C] {n : ℕ}
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_eq_sum_factorial (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing F G =
      ∑ A ∈ F.support, coeff A F * (A.prod fun _ e => (e.factorial : C)) * coeff A G := by
  rw [_root_.GlobalTheory.DetPowPairing.pairing, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem exists_cayOp_pow_cayDet_pow (n k Y : ℕ) :
    ∃ c : ℕ, (_root_.ReciprocityTheory.PGsh.cayOp n C ^ k) (_root_.ReciprocityTheory.PGsh.cayDet n C ^ Y) = c • _root_.ReciprocityTheory.PGsh.cayDet n C ^ (Y - k) := by
  induction k generalizing Y with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (Y - 1)
    have hC := _root_.ReciprocityTheory.PGsh.cayley
    unfold _root_.ReciprocityTheory.PGsh.CayleyStatement at hC
    refine ⟨(∏ j ∈ Finset.range n, (Y + j)) * c, ?_⟩
    rw [pow_succ, Module.End.mul_apply, hC, map_nsmul, hc, smul_smul]
    have : Y - 1 - k = Y - (k + 1) := by omega
    rw [this]
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_eq_sum_of_support_subset (F G : MvPolynomial κ C)
    (S : Finset (κ →₀ ℕ)) (hS : F.support ⊆ S) :
    _root_.GlobalTheory.DetPowPairing.pairing F G =
      ∑ A ∈ S, coeff A F * (A.prod fun _ e => (e.factorial : C)) * coeff A G := by
  rw [pairing_eq_sum_factorial]
  refine Finset.sum_subset hS fun A _ hA => ?_
  have h : coeff A F = 0 := by simpa using hA
  rw [h]; ring
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_comm' (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing F G = _root_.GlobalTheory.DetPowPairing.pairing G F := by
  classical
  rw [pairing_eq_sum_of_support_subset F G (F.support ∪ G.support)
      Finset.subset_union_left,
    pairing_eq_sum_of_support_subset G F (F.support ∪ G.support)
      Finset.subset_union_right]
  exact Finset.sum_congr rfl fun _ _ => by ring
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_monomial_eq_coeff_mul_prod_factorial_mul (F : MvPolynomial κ C) (A : κ →₀ ℕ) (b : C) :
    _root_.GlobalTheory.DetPowPairing.pairing F (monomial A b) =
      coeff A F * (A.prod fun _ e => (e.factorial : C)) * b := by
  classical
  rw [pairing_eq_sum_of_support_subset F _ (insert A F.support)
      (Finset.subset_insert _ _), Finset.sum_eq_single A]
  · rw [coeff_monomial, if_pos rfl]
  · intro B _ hB
    rw [coeff_monomial, if_neg (Ne.symm hB)]; ring
  · intro h; exact absurd (Finset.mem_insert_self _ _) h
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem prod_factorial_add_single_one_eq_succ_mul_prod_factorial (B : κ →₀ ℕ) (x : κ) :
    ((B + Finsupp.single x 1).prod fun _ e => (e.factorial : C)) =
      ((B x + 1 : ℕ) : C) * (B.prod fun _ e => (e.factorial : C)) := by
  classical
  have h1 : (B + Finsupp.single x 1).support ⊆ insert x B.support := by
    intro y hy
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      have hxy' : x ≠ y := Ne.symm hxy
      simpa [Finsupp.single_apply, hxy'] using hy
  rw [Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset B (Finset.subset_insert x B.support) _ (fun _ _ => by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self x B.support),
    ← Finset.mul_prod_erase _ (fun y => ((B y).factorial : C)) (Finset.mem_insert_self x B.support)]
  have h2 : ∏ y ∈ (insert x B.support).erase x, (((B + Finsupp.single x 1 : κ →₀ ℕ) y).factorial : C) =
      ∏ y ∈ (insert x B.support).erase x, ((B y).factorial : C) := by
    refine Finset.prod_congr rfl fun y hy => ?_
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hxy : x ≠ y := Ne.symm hyx
    simp [Finsupp.single_apply, hxy]
  rw [h2]
  simp [Nat.factorial_succ]
  ring
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_X_mul_eq_pairing_pderiv (x : κ) (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing (X x * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F (pderiv x G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial A b =>
    rw [pairing_monomial_eq_coeff_mul_prod_factorial_mul, pderiv_monomial, pairing_monomial_eq_coeff_mul_prod_factorial_mul,
      coeff_X_mul']
    by_cases hx : A x = 0
    · have : x ∉ A.support := by simpa using hx
      rw [if_neg this, hx]; simp
    · rw [if_pos (by simpa using hx)]
      have hA : A = (A - Finsupp.single x 1) + Finsupp.single x 1 := by
        ext y
        by_cases hy : x = y
        · subst hy; simp; omega
        · simp [Finsupp.single_apply, hy]
      have hAx : (A - Finsupp.single x 1 : κ →₀ ℕ) x + 1 = A x := by simp; omega
      have hf : (A.prod fun _ e => (e.factorial : C)) =
          ((A x : ℕ) : C) * ((A - Finsupp.single x 1).prod fun _ e => (e.factorial : C)) := by
        conv_lhs => rw [hA]
        rw [prod_factorial_add_single_one_eq_succ_mul_prod_factorial, hAx]
      rw [hf]; ring
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_list_prod_X_mul_eq_pairing_list_prod_pderiv {ι : Type} (g : ι → κ) (L : List ι)
    (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing ((L.map fun j => X (g j)).prod * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F
        ((L.map fun j => ((pderiv (g j) : Derivation C (MvPolynomial κ C) (MvPolynomial κ C)).toLinearMap :
          Module.End C (MvPolynomial κ C))).prod G) := by
  induction L generalizing F with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, mul_left_comm, ih,
      pairing_X_mul_eq_pairing_pderiv, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl
open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem pairing_cayDet_mul' (n : ℕ) (F G : MvPolynomial (Fin n × Fin n) C) :
    _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n C * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F (_root_.ReciprocityTheory.PGsh.cayOp n C G) := by
  unfold _root_.ReciprocityTheory.PGsh.cayDet _root_.ReciprocityTheory.PGsh.cayOp _root_.ReciprocityTheory.PGsh.cayMono
  rw [Matrix.det_apply, Finset.sum_mul, pairing_comm', map_sum,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, smul_mul_assoc, map_zsmul, LinearMap.smul_apply, map_zsmul,
    pairing_comm']
  congr 1
  have hprod : ∏ i, Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i =
      ((List.finRange n).map fun j => X (σ j, j)).prod := by
    rw [Fin.prod_univ_def]; rfl
  rw [hprod, pairing_list_prod_X_mul_eq_pairing_list_prod_pderiv (fun j => (σ j, j))]
open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem pairing_cayDet_pow_mul (n k : ℕ) (F G : MvPolynomial (Fin n × Fin n) C) :
    _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n C ^ k * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F ((_root_.ReciprocityTheory.PGsh.cayOp n C ^ k) G) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, ih, pairing_cayDet_mul', pow_succ', Module.End.mul_apply]
end GlobalTheory.DetPowPairing
end

set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowPairing
variable {C : Type} [CommRing C] {n : ℕ}
open MvPolynomial
variable {C : Type} [CommRing C] {n : ℕ}
namespace GlobalTheory.DetPowPairing
namespace _root_.GlobalTheory.DetPowPairing
theorem _root_.solution :
  (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * Q)) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M)) = (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y))) := by
  intro C _ _ n₀ M Y Q hMY _
  simp only [← pairing_eq_sum_factorial]
  obtain ⟨c, hc⟩ := exists_cayOp_pow_cayDet_pow (C := C) n₀ (Y - M) Y
  have hYM : Y - (Y - M) = M := by omega
  rw [hYM] at hc
  have e1 : _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * Q) =
      c * _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) Q := by
    rw [pairing_comm', pairing_cayDet_pow_mul, hc, map_nsmul,
      pairing_comm', nsmul_eq_mul]
  have e2 : _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) =
      c * _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) := by
    have hsplit : _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y = _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M := by
      rw [← pow_add]; congr 1; omega
    nth_rewrite 1 [hsplit]
    rw [pairing_cayDet_pow_mul, hc, map_nsmul, nsmul_eq_mul]
  rw [e1, e2]; ring
end _root_.GlobalTheory.DetPowPairing
end GlobalTheory.DetPowPairing
