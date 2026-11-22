-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:02:01.659817+00:00
-- url     : https://prove2.me/submissions/76ebae61-bc8c-4d13-a225-fef5987d87c5

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders
open Finset

namespace BNSAux

set_option linter.unusedSectionVars false
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- recursive per-coordinate probability -/
noncomputable def pr (F : Type) [Field F] [Fintype F] [DecidableEq F] : ℕ → F → ℝ
  | 0, c => if c = 0 then 1 else 0
  | n+1, c => ((Fintype.card F : ℝ)⁻¹) ^ 2 * ∑ a : F, ∑ b : F, pr F n (c * (a - b))

lemma pr_nonneg : ∀ (n : ℕ) (c : F), 0 ≤ pr F n c
  | 0, c => by unfold pr; split_ifs <;> norm_num
  | n+1, c => by
      unfold pr
      exact mul_nonneg (by positivity) (sum_nonneg fun a _ => sum_nonneg fun b _ => pr_nonneg n _)

lemma addChar_sum {ι : Type} (s : Finset ι) (ψ : AddChar F ℂ) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma sum_prod_pairs {w : ℕ} (f : Fin w → F → F → ℝ) :
    ∑ u : Fin w → F, ∑ u' : Fin w → F, ∏ t, f t (u t) (u' t) =
      ∏ t, ∑ a : F, ∑ b : F, f t a b := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [Fintype.prod_sum]

lemma char_lin_sum {w : ℕ} (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (z : Fin w → F) :
    ∑ u : Fin w → F, ψ (∑ t, z t * u t) =
      ∏ t, (if z t = 0 then (Fintype.card F : ℂ) else 0) := by
  have hp := AddChar.IsPrimitive.of_ne_one hψ
  simp_rw [addChar_sum]
  rw [← Fintype.prod_sum (fun t a => ψ (z t * a))]
  refine prod_congr rfl fun t _ => ?_
  have := AddChar.sum_mulShift (ψ := ψ) (z t) hp
  simp_rw [mul_comm (z t)]
  rw [this]; split_ifs <;> simp


lemma base_case {w : ℕ} (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (z : Fin w → F)
    (φ : Fin 1 → (Fin 1 → Fin w → F) → ℂ)
    (hb : ∀ i y, ‖φ i y‖ ≤ 1)
    (hc : ∀ i y y', (∀ j, j ≠ i → y j = y' j) → φ i y = φ i y') :
    ‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ≤
      ((Fintype.card F : ℝ) ^ w) * ∏ t, pr F 0 (z t) := by
  have hconst : ∀ y, φ 0 y = φ 0 (fun _ _ => 0) := fun y =>
    hc 0 y _ (fun j hj => absurd (Subsingleton.elim j 0) hj)
  have e : ∑ y : Fin 1 → Fin w → F, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t) =
      φ 0 (fun _ _ => 0) * ∑ u : Fin w → F, ψ (∑ t, z t * u t) := by
    rw [mul_sum, ← (Equiv.funUnique (Fin 1) (Fin w → F)).symm.sum_comp]
    refine sum_congr rfl fun u _ => ?_
    simp only [Fin.prod_univ_one, hconst]
    rfl
  rw [e, char_lin_sum ψ hψ, norm_mul, norm_prod]
  calc ‖φ 0 (fun _ _ => 0)‖ * ∏ t, ‖(if z t = 0 then (Fintype.card F : ℂ) else 0)‖
      ≤ 1 * ∏ t, ‖(if z t = 0 then (Fintype.card F : ℂ) else 0)‖ :=
        mul_le_mul_of_nonneg_right (hb _ _) (prod_nonneg fun _ _ => norm_nonneg _)
    _ = ((Fintype.card F : ℝ) ^ w) * ∏ t, pr F 0 (z t) := by
        rw [one_mul, ← Fin.prod_const w (Fintype.card F : ℝ), ← prod_mul_distrib]
        refine prod_congr rfl fun t _ => ?_
        unfold pr
        split_ifs <;> simp


theorem bns {w : ℕ} (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : ∀ (n : ℕ) (z : Fin w → F)
    (φ : Fin (n+1) → (Fin (n+1) → Fin w → F) → ℂ),
    (∀ i y, ‖φ i y‖ ≤ 1) →
    (∀ i y y', (∀ j, j ≠ i → y j = y' j) → φ i y = φ i y') →
    ‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ^ (2 ^ n) ≤
      (((Fintype.card F : ℝ) ^ w) ^ (n+1)) ^ (2 ^ n) * ∏ t, pr F n (z t)
  | 0, z, φ, hb, hc => by
      simpa using base_case ψ hψ z φ hb hc
  | n+1, z, φ, hb, hc => by
      set N : ℝ := (Fintype.card F : ℝ) ^ w with hN
      set M : ℝ := N ^ (n+1) with hM
      have hN0 : 0 ≤ N := by positivity
      have hM0 : 0 ≤ M := by positivity
      let G : (Fin w → F) → (Fin (n+1) → Fin w → F) → ℂ := fun u y0 =>
        (∏ i : Fin (n+1), φ i.succ (Fin.cons u y0)) * ψ (∑ t, z t * (u t * ∏ i, y0 i t))
      have h1 : ∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t) =
          ∑ y0 : Fin (n+1) → Fin w → F, φ 0 (Fin.cons 0 y0) * ∑ u, G u y0 := by
        rw [← (Fin.consEquiv (fun _ : Fin (n+2) => Fin w → F)).sum_comp,
          Fintype.sum_prod_type, sum_comm]
        refine sum_congr rfl fun y0 _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun u _ => ?_
        show (∏ i, φ i (Fin.cons u y0)) * ψ (∑ t, z t * ∏ i, (Fin.cons u y0 : Fin (n+2) → Fin w → F) i t) = _
        rw [Fin.prod_univ_succ]
        simp only [Fin.prod_univ_succ (fun i => (Fin.cons u y0 : Fin (n+2) → Fin w → F) i _),
          Fin.cons_zero, Fin.cons_succ, G]
        have : φ 0 (Fin.cons u y0) = φ 0 (Fin.cons 0 y0) := by
          refine hc 0 _ _ fun j hj => ?_
          obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
          simp
        rw [this]; ring
      -- the inner correlation
      let I : (Fin w → F) → (Fin w → F) → ℂ := fun u u' =>
        ∑ y0 : Fin (n+1) → Fin w → F, G u y0 * (starRingEnd ℂ) (G u' y0)
      have h2 : ‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ≤
          ∑ y0 : Fin (n+1) → Fin w → F, ‖∑ u, G u y0‖ := by
        rw [h1]
        refine (norm_sum_le _ _).trans (sum_le_sum fun y0 _ => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb _ _)
      have hcard : (Fintype.card (Fin (n+1) → Fin w → F) : ℝ) = M := by
        simp [hM, hN, ← pow_mul]
      have h3 : ‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ^ 2 ≤
          M * ∑ y0 : Fin (n+1) → Fin w → F, ‖∑ u, G u y0‖ ^ 2 := by
        refine (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans ?_
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (n+1) → Fin w → F)))
          (f := fun y0 => ‖∑ u, G u y0‖)
        rwa [card_univ, hcard] at this
      have h4 : ∀ y0, ‖∑ u, G u y0‖ ^ 2 = (∑ u, ∑ u', G u y0 * (starRingEnd ℂ) (G u' y0)).re := by
        intro y0
        rw [← sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq]
      have h5 : ∑ y0 : Fin (n+1) → Fin w → F, ‖∑ u, G u y0‖ ^ 2 ≤ ∑ u, ∑ u', ‖I u u'‖ := by
        simp_rw [h4]
        rw [← Complex.re_sum]
        have : ∑ y0 : Fin (n+1) → Fin w → F, ∑ u, ∑ u', G u y0 * (starRingEnd ℂ) (G u' y0) =
            ∑ u, ∑ u', I u u' := by
          rw [sum_comm]; refine sum_congr rfl fun u _ => ?_; rw [sum_comm]
        rw [this]
        refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (sum_le_sum fun u _ => ?_))
        exact norm_sum_le _ _
      have h6 : ∀ u u', ‖I u u'‖ ^ (2 ^ n) ≤ M ^ (2 ^ n) * ∏ t, pr F n (z t * (u t - u' t)) := by
        intro u u'
        let φ' : Fin (n+1) → (Fin (n+1) → Fin w → F) → ℂ := fun i y0 =>
          φ i.succ (Fin.cons u y0) * (starRingEnd ℂ) (φ i.succ (Fin.cons u' y0))
        have hb' : ∀ i y, ‖φ' i y‖ ≤ 1 := by
          intro i y
          simp only [φ', norm_mul, RCLike.norm_conj]
          exact mul_le_one₀ (hb _ _) (norm_nonneg _) (hb _ _)
        have hc' : ∀ i y y', (∀ j, j ≠ i → y j = y' j) → φ' i y = φ' i y' := by
          intro i y y' hyy
          have key : ∀ v : Fin w → F, φ i.succ (Fin.cons v y) = φ i.succ (Fin.cons v y') := by
            intro v
            refine hc _ _ _ fun j hj => ?_
            refine Fin.cases (by simp) (fun j hj => ?_) j hj
            simp only [Fin.cons_succ]
            exact hyy j fun h => hj (by rw [h])
          simp only [φ', key]
        have hI : I u u' = ∑ y0, (∏ i, φ' i y0) *
            ψ (∑ t, (z t * (u t - u' t)) * ∏ i, y0 i t) := by
          refine sum_congr rfl fun y0 _ => ?_
          simp only [G, φ', map_mul, map_prod, prod_mul_distrib]
          rw [← AddChar.map_neg_eq_conj]
          have : ψ (∑ t, z t * (u t * ∏ i, y0 i t)) * ψ (-∑ t, z t * (u' t * ∏ i, y0 i t)) =
              ψ (∑ t, (z t * (u t - u' t)) * ∏ i, y0 i t) := by
            rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sum_sub_distrib]
            congr 1; refine sum_congr rfl fun t _ => ?_; ring
          rw [← this]; ring
        rw [hI]
        exact bns ψ hψ n _ φ' hb' hc'
      -- assemble
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
      have hpairs : ∑ u : Fin w → F, ∑ u' : Fin w → F, ∏ t, pr F n (z t * (u t - u' t)) =
          N ^ 2 * ∏ t, pr F (n+1) (z t) := by
        rw [sum_prod_pairs (fun t a b => pr F n (z t * (a - b)))]
        have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        rw [hN, ← pow_mul, mul_comm w 2, pow_mul, ← Fin.prod_const w ((Fintype.card F : ℝ) ^ 2),
          ← prod_mul_distrib]
        refine prod_congr rfl fun t _ => ?_
        simp only [pr]
        field_simp
      have hcard2 : ((univ : Finset ((Fin w → F) × (Fin w → F))).card : ℝ) = N ^ 2 := by
        simp [hN, Fintype.card_prod]; ring
      have h7 : (∑ u, ∑ u', ‖I u u'‖) ^ (2 ^ n) ≤ (N ^ 2) ^ m * (M ^ (2 ^ n) *
          (N ^ 2 * ∏ t, pr F (n+1) (z t))) := by
        rw [← Fintype.sum_prod_type', hm]
        refine (pow_sum_le_card_mul_sum_pow (fun _ _ => norm_nonneg _) m).trans ?_
        rw [hcard2]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hpairs, mul_sum, Fintype.sum_prod_type]
        refine sum_le_sum fun u _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun u' _ => ?_
        rw [← hm]; exact h6 u u'
      have hprod0 : 0 ≤ ∏ t, pr F (n+1) (z t) := prod_nonneg fun _ _ => pr_nonneg _ _
      calc ‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ^ (2 ^ (n+1))
          = (‖∑ y, (∏ i, φ i y) * ψ (∑ t, z t * ∏ i, y i t)‖ ^ 2) ^ (2 ^ n) := by
            rw [← pow_mul, pow_succ, mul_comm]
        _ ≤ (M * ∑ u, ∑ u', ‖I u u'‖) ^ (2 ^ n) :=
            pow_le_pow_left₀ (by positivity) (h3.trans (mul_le_mul_of_nonneg_left h5 hM0)) _
        _ = M ^ (2 ^ n) * (∑ u, ∑ u', ‖I u u'‖) ^ (2 ^ n) := mul_pow _ _ _
        _ ≤ M ^ (2 ^ n) * ((N ^ 2) ^ m * (M ^ (2 ^ n) * (N ^ 2 * ∏ t, pr F (n+1) (z t)))) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = (N ^ (n+1+1)) ^ (2 ^ (n+1)) * ∏ t, pr F (n+1) (z t) := by
            rw [hM, hm, pow_succ 2 n, hm]; ring


lemma pr_zero : ∀ n : ℕ, pr F n 0 = 1
  | 0 => by simp [pr]
  | n+1 => by
      simp only [pr, zero_mul, pr_zero n, sum_const, card_univ, nsmul_eq_mul, mul_one]
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

lemma pr_ne_zero : ∀ (n : ℕ) (c : F), c ≠ 0 →
    pr F n c = 1 - (1 - 1 / (Fintype.card F : ℝ)) ^ n
  | 0, c, hc => by simp [pr, hc]
  | n+1, c, hc => by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      set v := 1 - (1 - 1 / (Fintype.card F : ℝ)) ^ n with hv
      have h1 : ∀ a b : F, pr F n (c * (a - b)) = if a = b then 1 else v := by
        intro a b
        split_ifs with hab
        · rw [hab, sub_self, mul_zero, pr_zero]
        · exact pr_ne_zero n _ (mul_ne_zero hc (sub_ne_zero.mpr hab))
      have h2 : ∀ a : F, ∑ b : F, pr F n (c * (a - b)) = (Fintype.card F : ℝ) * v + (1 - v) := by
        intro a
        simp_rw [h1]
        have : ∀ b : F, (if a = b then (1:ℝ) else v) = v + if a = b then 1 - v else 0 := by
          intro b; split_ifs <;> ring
        simp_rw [this, sum_add_distrib, sum_ite_eq, sum_const, card_univ, nsmul_eq_mul]
        simp
      simp only [pr, h2, sum_const, card_univ, nsmul_eq_mul, hv, pow_succ]
      generalize (1 - 1 / (Fintype.card F : ℝ)) ^ n = x
      field_simp
      ring

end BNSAux

open NOFSeparation750.CodedGIP in
theorem solution (k w a : ℕ) (hk : 2 ≤ k) (_hw : 1 ≤ w) (_ha : 1 ≤ a)
    (F : Type) [Field F] [Fintype F] (_hF : Fintype.card F = 2 ^ a)
    (B : Set (Fin k → Fin w → F)) (hB : IsCylinderIntersection B) (τ : F) :
    |uniformMass (B ∩ {y | gip y = τ}) - uniformMass B / (Fintype.card F : ℝ)| ≤
      (1 - 1 / (Fintype.card F : ℝ)) *
        Real.rpow (1 - (1 - 1 / (Fintype.card F : ℝ)) ^ (k - 1))
          ((w : ℝ) / (2 : ℝ) ^ (k - 1)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨C, hC, rfl⟩ := hB
  simp only [Nat.add_sub_cancel]
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set Q : ℝ := (Fintype.card (Fin (n+1) → Fin w → F) : ℝ) with hQ
  have hQ0 : 0 < Q := by rw [hQ]; exact_mod_cast Fintype.card_pos
  have hmass : ∀ A : Set (Fin (n+1) → Fin w → F),
      uniformMass A = (∑ y, if y ∈ A then (1:ℝ) else 0) / Q := by
    intro A
    unfold uniformMass
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
  set φ : Fin (n+1) → (Fin (n+1) → Fin w → F) → ℂ := fun i y => if y ∈ C i then 1 else 0
  have hφB : ∀ y, (∏ i, φ i y) = if y ∈ ⋂ i, C i then 1 else 0 := by
    intro y
    by_cases hy : y ∈ ⋂ i, C i
    · rw [if_pos hy]; refine prod_eq_one fun i _ => ?_
      simp only [φ, if_pos (Set.mem_iInter.mp hy i)]
    · rw [if_neg hy]
      obtain ⟨i, hi⟩ : ∃ i, y ∉ C i := by simpa [Set.mem_iInter] using hy
      exact prod_eq_zero (mem_univ i) (by simp [φ, hi])
  set S : AddChar F ℂ → ℂ := fun ψ =>
    ∑ y, (∏ i, φ i y) * ψ (∑ t, (fun _ => (1:F)) t * ∏ i, y i t)
  have hgip : ∀ y : Fin (n+1) → Fin w → F, gip y = ∑ t, (fun _ => (1:F)) t * ∏ i, y i t := by
    intro y; simp [gip]
  have key : (∑ y, if y ∈ (⋂ i, C i) ∩ {y | gip y = τ} then (1:ℂ) else 0) -
      (∑ y, if y ∈ ⋂ i, C i then (1:ℂ) else 0) / q =
      (1 / q) * ∑ ψ ∈ univ.erase (1 : AddChar F ℂ), ψ (-τ) * S ψ := by
    have hpt : ∀ y : Fin (n+1) → Fin w → F,
        (if y ∈ (⋂ i, C i) ∩ {y | gip y = τ} then (1:ℂ) else 0) =
          (1 / q) * ∑ ψ : AddChar F ℂ, ψ (-τ) * ((∏ i, φ i y) * ψ (gip y)) := by
      intro y
      have := AddChar.sum_apply_eq_ite (gip y - τ)
      simp_rw [← mul_assoc, mul_comm _ (∏ i, φ i y), mul_assoc, ← AddChar.map_add_eq_mul,
        ← mul_sum, neg_add_eq_sub, this, hφB]
      have hc0 : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      by_cases h1 : y ∈ ⋂ i, C i <;> by_cases h2 : gip y = τ <;>
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, h1, h2, sub_self, if_true, if_false,
          and_true, and_false, sub_eq_zero, hq, Complex.ofReal_natCast] <;>
        field_simp <;> simp
    simp_rw [hpt, ← mul_sum]
    rw [sum_comm, ← add_sum_erase _ _ (mem_univ (1 : AddChar F ℂ))]
    simp only [AddChar.one_apply, one_mul, mul_one, hφB, mul_add]
    have hY : ∑ x ∈ univ.erase (1 : AddChar F ℂ), ∑ x_1 : Fin (n+1) → Fin w → F,
        x (-τ) * ((if x_1 ∈ ⋂ i, C i then (1:ℂ) else 0) * x (gip x_1)) =
        ∑ ψ ∈ univ.erase 1, ψ (-τ) * S ψ := by
      refine sum_congr rfl fun ψ _ => ?_
      simp only [S, mul_sum, hgip, hφB]
    rw [hY]; ring
  set P : ℝ := Real.rpow (1 - (1 - 1 / q) ^ n) ((w : ℝ) / (2 : ℝ) ^ n) with hP
  have hpr1 : BNSAux.pr F n 1 = 1 - (1 - 1 / q) ^ n := BNSAux.pr_ne_zero n 1 one_ne_zero
  have hpr0 : 0 ≤ BNSAux.pr F n 1 := BNSAux.pr_nonneg n 1
  have hbound : ∀ ψ ∈ univ.erase (1 : AddChar F ℂ), ‖S ψ‖ ≤ Q * P := by
    intro ψ hψ
    have hψ1 : ψ ≠ 1 := (mem_erase.mp hψ).1
    have h := BNSAux.bns ψ hψ1 n (fun _ => (1:F)) φ
      (fun i y => by simp only [φ]; split_ifs <;> simp)
      (fun i y y' hyy => by simp only [φ, hC i y y' hyy])
    have hQe : ((Fintype.card F : ℝ) ^ w) ^ (n+1) = Q := by
      simp [hQ, ← pow_mul]
    rw [hQe, prod_const, card_univ, Fintype.card_fin] at h
    have hK : (0:ℝ) < 2 ^ n := by positivity
    have hS0 : 0 ≤ ‖S ψ‖ := norm_nonneg _
    have e1 : ‖S ψ‖ = (‖S ψ‖ ^ (2 ^ n)) ^ ((1:ℝ) / 2 ^ n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
      push_cast
      rw [mul_one_div_cancel hK.ne', Real.rpow_one]
    rw [e1]
    calc (‖S ψ‖ ^ (2 ^ n)) ^ ((1:ℝ) / 2 ^ n)
        ≤ (Q ^ (2 ^ n) * BNSAux.pr F n 1 ^ w) ^ ((1:ℝ) / 2 ^ n) :=
          Real.rpow_le_rpow (by positivity) h (by positivity)
      _ = Q * P := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast Q,
            ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast (BNSAux.pr F n 1), ← Real.rpow_mul hpr0]
          push_cast
          rw [mul_one_div_cancel hK.ne', Real.rpow_one, hP, hpr1]
          congr 2
          ring
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by rw [← hpr1]; exact hpr0) _
  have hcardE : ((univ.erase (1 : AddChar F ℂ)).card : ℝ) = q - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, AddChar.card_eq, hq]
    have : 1 ≤ Fintype.card F := Fintype.card_pos
    push_cast [this]; ring
  have final : ‖(((∑ y, if y ∈ (⋂ i, C i) ∩ {y | gip y = τ} then (1:ℂ) else 0) -
        (∑ y, if y ∈ ⋂ i, C i then (1:ℂ) else 0) / q) / Q : ℂ)‖ ≤ (1 - 1 / q) * P := by
    rw [key, norm_div, norm_mul]
    have hnq : ‖((1:ℂ) / (q:ℂ))‖ = 1 / q := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    have hnQ : ‖(Q:ℂ)‖ = Q := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    rw [hnq, hnQ]
    have hsum : ‖∑ ψ ∈ univ.erase (1 : AddChar F ℂ), ψ (-τ) * S ψ‖ ≤ (q - 1) * (Q * P) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ ψ ∈ univ.erase (1 : AddChar F ℂ), ‖ψ (-τ) * S ψ‖
          ≤ ∑ ψ ∈ univ.erase (1 : AddChar F ℂ), Q * P := by
            refine sum_le_sum fun ψ hψ => ?_
            rw [norm_mul, AddChar.norm_apply, one_mul]; exact hbound ψ hψ
        _ = (q - 1) * (Q * P) := by rw [sum_const, nsmul_eq_mul, hcardE]
    rw [div_le_iff₀ hQ0]
    calc 1 / q * ‖∑ ψ ∈ univ.erase (1 : AddChar F ℂ), ψ (-τ) * S ψ‖
        ≤ 1 / q * ((q - 1) * (Q * P)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (1 - 1 / q) * P * Q := by field_simp
  rw [hmass, hmass, ← Real.norm_eq_abs, ← Complex.norm_real]
  convert final using 2
  push_cast [Complex.ofReal_sum, apply_ite]
  ring
