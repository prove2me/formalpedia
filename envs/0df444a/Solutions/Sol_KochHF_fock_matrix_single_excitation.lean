-- Prove2me | solution 1 for KochHF.fock_matrix_single_excitation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T17:18:03.099995+00:00
-- url     : https://prove2.me/submissions/f53e8158-87e8-4ace-823b-85cd8b804752

import Mathlib
import Definitions.Def_KochHF_FockSpace
import Definitions.Def_KochHF_Hamiltonian


open Matrix KochHF

namespace KochHFAux

variable {K : ℕ}

lemma fermiSign_sq (i : Fin K) (S : Finset (Fin K)) : fermiSign i S * fermiSign i S = 1 := by
  unfold fermiSign; rw [← pow_add, ← two_mul, pow_mul]; simp

lemma star_fermiSign (i : Fin K) (S : Finset (Fin K)) : star (fermiSign i S) = fermiSign i S := by
  unfold fermiSign; simp

lemma fermiSign_insert (i j : Fin K) (S : Finset (Fin K)) (hj : j ∉ S) :
    fermiSign i (insert j S) = (if i < j then -1 else 1) * fermiSign i S := by
  unfold fermiSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hj])]; ring
  · ring

lemma fermiSign_erase (i j : Fin K) (S : Finset (Fin K)) (hj : j ∈ S) :
    fermiSign i S = (if i < j then -1 else 1) * fermiSign i (S.erase j) := by
  conv_lhs => rw [← Finset.insert_erase hj]
  exact fermiSign_insert i j _ (by simp)

lemma mulVec_basisState (A : FockOp K) (S T : Finset (Fin K)) :
    (A *ᵥ basisState S) T = A T S := by
  simp [basisState, mulVec, dotProduct, Pi.single_apply]

lemma basisState_apply (S T : Finset (Fin K)) :
    basisState S T = if T = S then 1 else 0 := by
  simp [basisState, Pi.single_apply]

lemma op_ext {A B : FockOp K} (h : ∀ S, A *ᵥ basisState S = B *ᵥ basisState S) : A = B := by
  ext T S
  have := congrFun (h S) T
  rwa [mulVec_basisState, mulVec_basisState] at this

lemma cdag_basis (i : Fin K) (S : Finset (Fin K)) :
    cdag i *ᵥ basisState S = if i ∈ S then 0 else fermiSign i S • basisState (insert i S) := by
  funext T
  rw [mulVec_basisState]
  simp only [cdag, of_apply]
  split_ifs with h1 h2 h2 <;> simp_all [basisState_apply]

lemma cann_basis (i : Fin K) (S : Finset (Fin K)) :
    cann i *ᵥ basisState S =
      if i ∈ S then fermiSign i (S.erase i) • basisState (S.erase i) else 0 := by
  funext T
  rw [mulVec_basisState]
  simp only [cann, conjTranspose_apply, cdag, of_apply]
  split_ifs with h1 h2 h2
  · obtain ⟨h1, rfl⟩ := h1
    simp [basisState_apply, star_fermiSign, h1]
  · obtain ⟨h1, rfl⟩ := h1
    simp at h2
  · simp only [star_zero, Pi.smul_apply, basisState_apply, smul_eq_mul]
    split_ifs with h3
    · subst h3; exact absurd ⟨by simp, (Finset.insert_erase h2).symm⟩ h1
    · simp
  · simp

lemma cdag_cdag_basis (i j : Fin K) (S : Finset (Fin K)) :
    (cdag i * cdag j + cdag j * cdag i) *ᵥ basisState S = 0 := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, cdag_basis j, cdag_basis i]
  by_cases hij : i = j
  · subst hij
    split_ifs with h <;> simp_all [mulVec_smul, cdag_basis]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mulVec_smul, cdag_basis, hij, Ne.symm hij, smul_smul]
  rw [Finset.insert_comm, ← add_smul]
  rw [fermiSign_insert i j S hj, fermiSign_insert j i S hi]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.not_gt]; left; ring
  · exact absurd h hij
  · simp [h, h.not_gt]; left; ring

lemma cdag_anticomm (i j : Fin K) : cdag i * cdag j + cdag j * cdag i = 0 :=
  op_ext fun S => by rw [cdag_cdag_basis, zero_mulVec]

lemma cann_anticomm (i j : Fin K) : cann i * cann j + cann j * cann i = 0 := by
  have := congrArg conjTranspose (cdag_anticomm i j)
  simpa [cann, conjTranspose_add, conjTranspose_mul, add_comm] using this

lemma cann_cdag_basis (i j : Fin K) (S : Finset (Fin K)) :
    (cann i * cdag j + cdag j * cann i) *ᵥ basisState S =
      (if i = j then 1 else 0) • basisState S := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, cdag_basis j, cann_basis i]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ S
    · simp [hi, mulVec_smul, cdag_basis, smul_smul, fermiSign_sq, Finset.insert_erase hi]
    · simp [hi, mulVec_smul, cann_basis, smul_smul, fermiSign_sq]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mulVec_smul, cdag_basis, cann_basis, hij, Ne.symm hij, smul_smul]
  rw [Finset.erase_insert_of_ne (Ne.symm hij), ← add_smul]
  rw [fermiSign_insert i j _ (by simp [hj]), fermiSign_erase j i S hi]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.not_gt]; left; ring
  · exact absurd h hij
  · simp [h, h.not_gt]; left; ring

lemma cann_cdag_anticomm (i j : Fin K) :
    cann i * cdag j + cdag j * cann i = if i = j then 1 else 0 :=
  op_ext fun S => by
    rw [cann_cdag_basis]; split_ifs <;> simp

lemma cann_vacuum (i : Fin K) : cann i *ᵥ vacuum K = 0 := by
  have : vacuum K = basisState ∅ := rfl
  rw [this, cann_basis]; simp

lemma cdagOrb_conjTranspose (φ : Fin K → ℂ) : (cdagOrb φ)ᴴ = cannOrb φ := by
  simp [cdagOrb, cannOrb, conjTranspose_sum, conjTranspose_smul, cann]

lemma cannOrb_conjTranspose (φ : Fin K → ℂ) : (cannOrb φ)ᴴ = cdagOrb φ := by
  rw [← cdagOrb_conjTranspose, conjTranspose_conjTranspose]

lemma bilin_anticomm (a b : Fin K → ℂ) (A B : Fin K → FockOp K) :
    (∑ μ, a μ • A μ) * (∑ ν, b ν • B ν) + (∑ ν, b ν • B ν) * (∑ μ, a μ • A μ) =
      ∑ μ, ∑ ν, (a μ * b ν) • (A μ * B ν + B ν * A μ) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp [mul_comm]

lemma cannOrb_anticomm (φ χ : Fin K → ℂ) :
    cannOrb φ * cannOrb χ + cannOrb χ * cannOrb φ = 0 := by
  unfold cannOrb
  rw [bilin_anticomm]
  simp [cann_anticomm]

lemma cdagOrb_anticomm (φ χ : Fin K → ℂ) :
    cdagOrb φ * cdagOrb χ + cdagOrb χ * cdagOrb φ = 0 := by
  unfold cdagOrb
  rw [bilin_anticomm]
  simp [cdag_anticomm]

lemma cannOrb_cdagOrb_anticomm (φ χ : Fin K → ℂ) :
    cannOrb φ * cdagOrb χ + cdagOrb χ * cannOrb φ = orbInner φ χ • (1 : FockOp K) := by
  unfold cannOrb cdagOrb
  rw [bilin_anticomm]
  simp only [cann_cdag_anticomm, smul_ite, smul_zero]
  simp [orbInner, dotProduct, Finset.sum_smul]

lemma cannOrb_vacuum (φ : Fin K → ℂ) : cannOrb φ *ᵥ vacuum K = 0 := by
  simp [cannOrb, sum_mulVec, smul_mulVec, cann_vacuum]

lemma fockInner_vacuum : fockInner (vacuum K) (vacuum K) = 1 := by
  simp [fockInner, vacuum, dotProduct, Pi.single_apply]

end KochHFAux

namespace KochHFAux

end KochHFAux

open Matrix KochHF

namespace KochHFAux

variable {K : ℕ}

lemma matEl_basis_diag (S : Finset (Fin K)) (A : FockOp K) :
    matEl (basisState S) A (basisState S) = A S S := by
  simp [matEl, basisState, dotProduct, mulVec, Pi.single_apply]

lemma fockInner_basis (S T : Finset (Fin K)) (c d : ℂ) :
    fockInner (c • basisState S) (d • basisState T) = if S = T then star c * d else 0 := by
  simp only [fockInner, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have : star (basisState S) ⬝ᵥ basisState T = if S = T then 1 else 0 := by
    simp only [basisState, dotProduct, Pi.star_apply, Pi.single_apply]
    split_ifs with h
    · subst h; simp
    · refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs <;> simp_all
  rw [this]
  split_ifs <;> simp [mul_comm]

lemma entry_eq_fockInner (S : Finset (Fin K)) (A B : FockOp K) :
    (A * B) S S = star ((Aᴴ *ᵥ basisState S)) ⬝ᵥ (B *ᵥ basisState S) := by
  rw [← matEl_basis_diag S (A * B)]
  simp only [matEl, star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec]

lemma ann2_basis (z w : Fin K) (S : Finset (Fin K)) :
    cann z *ᵥ (cann w *ᵥ basisState S) =
      if w ∈ S ∧ z ∈ S ∧ z ≠ w then
        (fermiSign w (S.erase w) * fermiSign z ((S.erase w).erase z)) •
          basisState ((S.erase w).erase z)
      else 0 := by
  rw [cann_basis]
  by_cases hw : w ∈ S
  · rw [if_pos hw, mulVec_smul, cann_basis]
    by_cases hz : z ∈ S ∧ z ≠ w
    · rw [if_pos (Finset.mem_erase.mpr ⟨hz.2, hz.1⟩), if_pos ⟨hw, hz⟩, smul_smul]
    · rw [if_neg (by simpa [and_comm] using hz), if_neg (by tauto), smul_zero]
  · rw [if_neg hw, mulVec_zero, if_neg (by tauto)]

lemma one_body_diag (x w : Fin K) (S : Finset (Fin K)) :
    (cdag x * cann w) S S = if w ∈ S ∧ x = w then 1 else 0 := by
  rw [← mulVec_basisState (cdag x * cann w) S S, ← mulVec_mulVec, cann_basis]
  by_cases hw : w ∈ S
  · rw [if_pos hw, mulVec_smul, cdag_basis]
    by_cases hx : x = w
    · subst hx
      simp [hw, Finset.insert_erase hw, basisState_apply, fermiSign_sq]
    · by_cases hxS : x ∈ S.erase w
      · rw [if_pos hxS]; simp [hx]
      · rw [if_neg hxS]
        have hne : insert x (S.erase w) ≠ S := by
          intro h
          have : x ∈ S := h ▸ Finset.mem_insert_self _ _
          exact hxS (Finset.mem_erase.mpr ⟨hx, this⟩)
        simp [basisState_apply, Ne.symm hne, hx]
  · rw [if_neg hw]; simp [hw]

lemma erase2_eq_cases {x y w z : Fin K} {S : Finset (Fin K)} (hx : x ∈ S) (hy : y ∈ S)
    (hw : w ∈ S) (hxy : y ≠ x)
    (h : (S.erase x).erase y = (S.erase w).erase z) :
    (x = w ∧ y = z) ∨ (x = z ∧ y = w) := by
  have hx' : x ∉ (S.erase w).erase z := by rw [← h]; simp
  have hy' : y ∉ (S.erase w).erase z := by rw [← h]; simp
  have hw' : w ∉ (S.erase x).erase y := by rw [h]; simp
  simp only [Finset.mem_erase, not_and, ne_eq] at hx' hy' hw'
  by_cases h1 : x = w
  · left; refine ⟨h1, ?_⟩
    by_contra h2
    exact hy' h2 (fun h3 => hxy (h3.trans h1.symm)) hy
  · right
    have hxz : x = z := by by_contra h2; exact hx' h2 h1 hx
    refine ⟨hxz, ?_⟩
    by_contra h2
    exact hw' (fun h3 => h2 h3.symm) (fun h3 => h1 h3.symm) hw

lemma two_body_diag (x y z w : Fin K) (S : Finset (Fin K)) :
    (cdag x * cdag y * cann z * cann w) S S =
      if w ∈ S ∧ z ∈ S ∧ z ≠ w then
        (if x = w ∧ y = z then 1 else 0) - (if x = z ∧ y = w then 1 else 0)
      else 0 := by
  have e : cdag x * cdag y * cann z * cann w = (cdag x * cdag y) * (cann z * cann w) := by
    simp only [mul_assoc]
  rw [e, entry_eq_fockInner, conjTranspose_mul]
  simp only [cann]
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change star (cann y *ᵥ (cann x *ᵥ basisState S)) ⬝ᵥ (cann z *ᵥ (cann w *ᵥ basisState S)) = _
  rw [ann2_basis, ann2_basis]
  change fockInner _ _ = _
  by_cases h1 : w ∈ S ∧ z ∈ S ∧ z ≠ w
  swap
  · rw [if_neg h1, if_neg h1]; simp [fockInner]
  rw [if_pos h1, if_pos h1]
  by_cases h2 : x ∈ S ∧ y ∈ S ∧ y ≠ x
  swap
  · rw [if_neg h2]
    have e1 : ¬ (x = w ∧ y = z) := by
      rintro ⟨rfl, rfl⟩; exact h2 ⟨h1.1, h1.2.1, h1.2.2⟩
    have e2 : ¬ (x = z ∧ y = w) := by
      rintro ⟨rfl, rfl⟩; exact h2 ⟨h1.2.1, h1.1, fun h => h1.2.2 h.symm⟩
    rw [if_neg e1, if_neg e2]; simp [fockInner]
  rw [if_pos h2, fockInner_basis]
  obtain ⟨hw, hz, hzw⟩ := h1
  obtain ⟨hx, hy, hyx⟩ := h2
  by_cases hA : (S.erase x).erase y = (S.erase w).erase z
  · rw [if_pos hA]
    rcases erase2_eq_cases hx hy hw hyx hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => hzw h.1.symm)]
      simp only [star_mul', star_fermiSign]
      have := fermiSign_sq x (S.erase x)
      have := fermiSign_sq y ((S.erase x).erase y)
      linear_combination (fermiSign y ((S.erase x).erase y) * fermiSign y ((S.erase x).erase y))
        * (fermiSign_sq x (S.erase x)) + fermiSign_sq y ((S.erase x).erase y)
    · rw [if_neg (fun h => hzw h.1), if_pos ⟨rfl, rfl⟩]
      simp only [star_mul', star_fermiSign]
      rw [fermiSign_erase x y (S.erase x) (Finset.mem_erase.mpr ⟨hyx, hy⟩),
        fermiSign_erase y x (S.erase y) (Finset.mem_erase.mpr ⟨fun h => hyx h.symm, hx⟩),
        Finset.erase_right_comm]
      have h3 := fermiSign_sq x ((S.erase y).erase x)
      have h4 := fermiSign_sq y ((S.erase y).erase x)
      rcases lt_or_gt_of_ne hyx with h | h
      · simp only [if_pos h, if_neg h.not_gt]
        linear_combination (-(fermiSign y ((S.erase y).erase x) *
          fermiSign y ((S.erase y).erase x))) * h3 - h4
      · simp only [if_pos h, if_neg h.not_gt]
        linear_combination (-(fermiSign y ((S.erase y).erase x) *
          fermiSign y ((S.erase y).erase x))) * h3 - h4
  · rw [if_neg hA]
    have e1 : ¬ (x = w ∧ y = z) := by rintro ⟨rfl, rfl⟩; exact hA rfl
    have e2 : ¬ (x = z ∧ y = w) := by
      rintro ⟨rfl, rfl⟩; exact hA (Finset.erase_right_comm)
    rw [if_neg e1, if_neg e2]; simp

lemma entry_ite (p : Prop) [Decidable p] (A : FockOp K) (S : Finset (Fin K)) :
    (if p then A else 0) S S = if p then A S S else 0 := by
  split_ifs <;> rfl

lemma hamiltonian_diag (T : Matrix (Fin K) (Fin K) ℂ) (U : Fin K → Fin K → Fin K → Fin K → ℂ)
    (S : Finset (Fin K)) :
    hamiltonian T U S S = ∑ m ∈ S, T m m + ∑ m ∈ S, ∑ m' ∈ S.filter (· < m), hfDelta U m m' := by
  unfold hamiltonian
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, entry_ite,
    one_body_diag, two_body_diag]
  congr 1
  · rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq', Finset.sum_ite_mem]
  · have key : ∀ n n' m m' : Fin K,
        (if n' < n ∧ m' < m then (U n n' m m' - U n n' m' m) *
          (if m ∈ S ∧ m' ∈ S ∧ m' ≠ m then
            ((if n = m ∧ n' = m' then (1 : ℂ) else 0) - if n = m' ∧ n' = m then 1 else 0)
          else 0) else 0) =
        if n = m ∧ n' = m' then
          (if m ∈ S ∧ m' ∈ S ∧ m' < m then hfDelta U m m' else 0) else 0 := by
      intro n n' m m'
      by_cases h1 : n = m ∧ n' = m'
      · obtain ⟨rfl, rfl⟩ := h1
        by_cases hlt : n' < n
        · by_cases hS : n ∈ S ∧ n' ∈ S
          · simp [hlt, hS.1, hS.2, hlt.ne, hfDelta]
          · by_cases hn : n ∈ S <;> simp_all
        · simp [hlt]
      · rw [if_neg h1]
        by_cases hc : n' < n ∧ m' < m
        · rw [if_pos hc]
          have h2 : ¬ (n = m' ∧ n' = m) := by
            rintro ⟨rfl, rfl⟩; exact lt_asymm hc.1 hc.2
          simp [h1, h2]
        · simp [hc, h1]
    simp only [key]
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => (show
      (∑ m, ∑ m', if n = m ∧ n' = m' then
        (if m ∈ S ∧ m' ∈ S ∧ m' < m then hfDelta U m m' else 0) else 0) =
      (if n ∈ S ∧ n' ∈ S ∧ n' < n then hfDelta U n n' else 0) by
        simp [ite_and, Finset.sum_ite_eq])]
    simp only [ite_and]
    simp [Finset.sum_ite_mem, Finset.sum_filter]

end KochHFAux

open Matrix KochHF

namespace KochHFAux

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {K : ℕ}

lemma matEl_add (ψ φ : FockVec K) (A B : FockOp K) :
    matEl ψ (A + B) φ = matEl ψ A φ + matEl ψ B φ := by
  simp [matEl, add_mulVec, dotProduct_add]

lemma matEl_sub (ψ φ : FockVec K) (A B : FockOp K) :
    matEl ψ (A - B) φ = matEl ψ A φ - matEl ψ B φ := by
  simp [matEl, sub_mulVec, dotProduct_sub]

lemma matEl_smul (ψ φ : FockVec K) (c : ℂ) (A : FockOp K) :
    matEl ψ (c • A) φ = c * matEl ψ A φ := by
  simp [matEl, smul_mulVec, dotProduct_smul]

/-- The matrix element as a real-linear map. -/
noncomputable def matElLin (ψ φ : FockVec K) : FockOp K →ₗ[ℝ] ℂ where
  toFun A := matEl ψ A φ
  map_add' A B := matEl_add ψ φ A B
  map_smul' c A := by
    simp only [RingHom.id_apply]
    rw [← Complex.coe_smul, matEl_smul]; rfl

lemma real_smul_eq (A : FockOp K) (t : ℝ) :
    (Complex.I * t) • A = t • (Complex.I • A) := by
  rw [mul_comm, ← smul_smul, Complex.coe_smul]

lemma neg_real_smul_eq (A : FockOp K) (t : ℝ) :
    (-(Complex.I * t)) • A = t • (-(Complex.I • A)) := by
  rw [neg_smul, real_smul_eq, smul_neg]

lemma hasDerivAt_conj_exp (A H : FockOp K) (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => NormedSpace.exp ((Complex.I * t) • A) * H *
        NormedSpace.exp ((-(Complex.I * t)) • A))
      (NormedSpace.exp ((Complex.I * t) • A) * (Complex.I • A) * H *
          NormedSpace.exp ((-(Complex.I * t)) • A) +
        NormedSpace.exp ((Complex.I * t) • A) * H *
          (NormedSpace.exp ((-(Complex.I * t)) • A) * (-(Complex.I • A)))) t := by
  simp only [real_smul_eq, neg_real_smul_eq]
  have hU := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • A) t
  have hV := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(Complex.I • A)) t
  exact HasDerivAt.fun_mul (HasDerivAt.mul_const hU H) hV

end KochHFAux

open Matrix KochHF

namespace KochHFAux

variable {K : ℕ}

lemma cann_cann_swap (i j : Fin K) : cann i * cann j = -(cann j * cann i) := by
  rw [eq_neg_iff_add_eq_zero]; exact cann_anticomm i j

lemma cann_cdag_swap' (i j : Fin K) :
    cann i * cdag j = (if i = j then 1 else 0) - cdag j * cann i := by
  rw [← cann_cdag_anticomm]; abel

lemma cann_kill (n j : Fin K) (w : FockVec K) (hw : cann n *ᵥ w = 0) :
    cann n *ᵥ (cann j *ᵥ w) = 0 := by
  rw [mulVec_mulVec, cann_cann_swap, neg_mulVec, ← mulVec_mulVec, hw, mulVec_zero, neg_zero]

lemma one_body_reduce (n a b : Fin K) (v : FockVec K) (hv : cann n *ᵥ v = 0) :
    (cann n * (cdag a * cann b)) *ᵥ v = (if n = a then 1 else 0 : ℂ) • (cann b *ᵥ v) := by
  have h2 := cann_kill n b v hv
  rw [← mul_assoc, cann_cdag_swap']
  split_ifs <;> simp [sub_mul, sub_mulVec, neg_mulVec, mul_assoc, ← mulVec_mulVec, h2]

lemma two_body_reduce (n a a' b' b : Fin K) (v : FockVec K) (hv : cann n *ᵥ v = 0) :
    (cann n * (cdag a * cdag a' * cann b' * cann b)) *ᵥ v =
      (if n = a then 1 else 0 : ℂ) • ((cdag a' * cann b' * cann b) *ᵥ v) -
      (if n = a' then 1 else 0 : ℂ) • ((cdag a * cann b' * cann b) *ᵥ v) := by
  have h3 := cann_kill n b' _ (cann_kill n b v hv)
  have e : cann n * (cdag a * cdag a' * cann b' * cann b) =
      (if n = a then 1 else 0 : FockOp K) * (cdag a' * cann b' * cann b) -
      cdag a * ((if n = a' then 1 else 0 : FockOp K) * (cann b' * cann b)) +
      cdag a * cdag a' * (cann n * cann b' * cann b) := by
    have e1 := cann_cdag_swap' n a
    have e2 := cann_cdag_swap' n a'
    calc cann n * (cdag a * cdag a' * cann b' * cann b)
        = (cann n * cdag a) * cdag a' * cann b' * cann b := by noncomm_ring
      _ = _ := by
        rw [e1, sub_mul, sub_mul, sub_mul, mul_assoc (cdag a) (cann n) (cdag a'), e2]
        noncomm_ring
  rw [e]
  split_ifs <;> simp [add_mulVec, sub_mulVec, neg_mulVec, mul_assoc, ← mulVec_mulVec, h3]

lemma matEl_finsum {ι : Type*} (s : Finset ι) (ψ φ : FockVec K) (A : ι → FockOp K) :
    matEl ψ (∑ i ∈ s, A i) φ = ∑ i ∈ s, matEl ψ (A i) φ := by
  simp [matEl, sum_mulVec, dotProduct_sum]

lemma matEl_ite_zero (ψ φ : FockVec K) (p : Prop) [Decidable p] (A : FockOp K) :
    matEl ψ (if p then A else 0) φ = if p then matEl ψ A φ else 0 := by
  split_ifs <;> simp [matEl]

section
variable (S : Finset (Fin K)) (n m : Fin K) (hn : n ∉ S)
include hn

lemma cann_basis_zero : cann n *ᵥ basisState S = 0 := by
  rw [cann_basis, if_neg hn]

lemma L1 (a b : Fin K) :
    matEl (basisState S) (cdag m * cann n * (cdag a * cann b)) (basisState S) =
      (if n = a then 1 else 0) * (cdag m * cann b) S S := by
  rw [← matEl_basis_diag S (cdag m * cann b), matEl, matEl, mul_assoc, ← mulVec_mulVec,
    one_body_reduce n a b _ (cann_basis_zero S n hn), mulVec_smul, dotProduct_smul,
    smul_eq_mul, mulVec_mulVec]

lemma L2 (a a' b' b : Fin K) :
    matEl (basisState S) (cdag m * cann n * (cdag a * cdag a' * cann b' * cann b))
        (basisState S) =
      (if n = a then 1 else 0) * (cdag m * cdag a' * cann b' * cann b) S S -
      (if n = a' then 1 else 0) * (cdag m * cdag a * cann b' * cann b) S S := by
  rw [← matEl_basis_diag S (cdag m * cdag a' * cann b' * cann b),
    ← matEl_basis_diag S (cdag m * cdag a * cann b' * cann b), matEl, matEl, matEl, mul_assoc,
    ← mulVec_mulVec, two_body_reduce n a a' b' b _ (cann_basis_zero S n hn), mulVec_sub,
    mulVec_smul, mulVec_smul, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, mulVec_mulVec, mulVec_mulVec]
  simp only [mul_assoc]

end

lemma keyGen (S : Finset (Fin K)) (m : Fin K) (hm : m ∈ S) (R : Fin K → Prop) [DecidablePred R]
    (V : Fin K → Fin K → Fin K → ℂ) (x b b' : Fin K) :
    (if R x ∧ b' < b then V x b b' *
      (if b ∈ S ∧ b' ∈ S ∧ b' ≠ b then
        ((if m = b ∧ x = b' then (1 : ℂ) else 0) - if m = b' ∧ x = b then 1 else 0) else 0)
      else 0) =
    (if b = m ∧ b' = x then (if R x ∧ x < m ∧ x ∈ S then V x m x else 0) else 0) -
    (if b = x ∧ b' = m then (if R x ∧ m < x ∧ x ∈ S then V x x m else 0) else 0) := by
  by_cases h1 : b = m ∧ b' = x
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hx : b' = b
    · subst hx; simp
    · have hx' : ¬ (b = b' ∧ b' = b) := fun h => hx h.2
      simp only [hx', if_false, sub_zero, if_pos (And.intro rfl rfl), hm, true_and, ne_eq, hx,
        not_false_eq_true, and_true]
      by_cases hR : R b' <;> by_cases hlt : b' < b <;> by_cases hS : b' ∈ S <;> simp [hR, hlt, hS]
  · by_cases h2 : b = x ∧ b' = m
    · obtain ⟨rfl, rfl⟩ := h2
      have h1' : ¬ (b' = b ∧ b = b') := fun h => h1 ⟨h.2, h.1.symm ▸ rfl⟩
      by_cases hx : b' = b
      · subst hx; simp
      · simp only [if_neg h1, if_pos (And.intro rfl rfl), zero_sub, hm, true_and, ne_eq, hx,
          not_false_eq_true, and_true, h1', if_false, zero_sub, if_true]
        by_cases hR : R b <;> by_cases hlt : b' < b <;> by_cases hS : b ∈ S <;> simp [hR, hlt, hS]
    · have h1' : ¬ (m = b ∧ x = b') := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have h2' : ¬ (m = b' ∧ x = b) := fun h => h2 ⟨h.2.symm, h.1.symm⟩
      simp [h1, h2, h1', h2']

theorem main_fock_matrix_single_excitation {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) (n m : Fin K) (hn : n ∉ S) (hm : m ∈ S) :
    matEl (basisState S) (cdag m * cann n * hamiltonian T U) (basisState S) =
      fockMatrix T U S n m := by
  unfold hamiltonian
  rw [mul_add, matEl_add]
  simp only [Finset.mul_sum, mul_smul_comm, matEl_finsum, matEl_smul, L1 S n m hn, one_body_diag]
  have e2 : ∀ a a' b b' : Fin K,
      matEl (basisState S) (cdag m * cann n * (if a' < a ∧ b' < b then
        (U a a' b b' - U a a' b' b) • (cdag a * cdag a' * cann b' * cann b) else 0))
        (basisState S) =
      (if a' < a ∧ b' < b then (U a a' b b' - U a a' b' b) *
        ((if n = a then 1 else 0) *
          (if b ∈ S ∧ b' ∈ S ∧ b' ≠ b then
            ((if m = b ∧ a' = b' then (1 : ℂ) else 0) - if m = b' ∧ a' = b then 1 else 0) else 0)
        ) else 0) -
      (if a' < a ∧ b' < b then (U a a' b b' - U a a' b' b) *
        ((if n = a' then 1 else 0) *
          (if b ∈ S ∧ b' ∈ S ∧ b' ≠ b then
            ((if m = b ∧ a = b' then (1 : ℂ) else 0) - if m = b' ∧ a = b then 1 else 0) else 0)
        ) else 0) := by
    intro a a' b b'
    by_cases hc : a' < a ∧ b' < b
    · rw [if_pos hc, if_pos hc, if_pos hc, mul_smul_comm, matEl_smul, L2 S n m hn,
        two_body_diag, two_body_diag]; ring
    · rw [if_neg hc, if_neg hc, if_neg hc]; simp [matEl]
  simp only [e2, Finset.sum_sub_distrib]
  have hT : (∑ x, ∑ x_1, T x x_1 * ((if n = x then 1 else 0) * if x_1 ∈ S ∧ m = x_1 then 1 else 0))
      = T n m := by
    rw [Finset.sum_eq_single n (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    rw [Finset.sum_eq_single m (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp [hm]
  have kP := fun x b b' => keyGen S m hm (fun y => y < n)
    (fun x b b' => U n x b b' - U n x b' b) x b b'
  have kQ := fun x b b' => keyGen S m hm (fun y => n < y)
    (fun x b b' => U x n b b' - U x n b' b) x b b'
  try simp only at kP kQ
  have hP : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3,
      if x_1 < x ∧ x_3 < x_2 then
        (U x x_1 x_2 x_3 - U x x_1 x_3 x_2) *
          ((if n = x then 1 else 0) *
            if x_2 ∈ S ∧ x_3 ∈ S ∧ x_3 ≠ x_2 then
              (if m = x_2 ∧ x_1 = x_3 then 1 else 0) - if m = x_3 ∧ x_1 = x_2 then 1 else 0
            else 0)
      else 0) = ∑ x, ((if x < n ∧ x < m ∧ x ∈ S then U n x m x - U n x x m else 0) -
        if x < n ∧ m < x ∧ x ∈ S then U n x x m - U n x m x else 0) := by
    rw [Finset.sum_eq_single n (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true, one_mul]
    simp only [kP]
    simp only [Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hQ : (∑ x, ∑ x_1, ∑ x_2, ∑ x_3,
      if x_1 < x ∧ x_3 < x_2 then
        (U x x_1 x_2 x_3 - U x x_1 x_3 x_2) *
          ((if n = x_1 then 1 else 0) *
            if x_2 ∈ S ∧ x_3 ∈ S ∧ x_3 ≠ x_2 then
              (if m = x_2 ∧ x = x_3 then 1 else 0) - if m = x_3 ∧ x = x_2 then 1 else 0
            else 0)
      else 0) = ∑ x, ((if n < x ∧ x < m ∧ x ∈ S then U x n m x - U x n x m else 0) -
        if n < x ∧ m < x ∧ x ∈ S then U x n x m - U x n m x else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single n (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
    simp only [if_true, one_mul]
    simp only [kQ]
    simp only [Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hT, hP, hQ, ← Finset.sum_sub_distrib]
  unfold fockMatrix
  rw [add_right_inj]
  have hR : ∑ m' ∈ S, (U n m' m m' - U n m' m' m) =
      ∑ x, if x ∈ S then U n x m x - U n x x m else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  rw [hR]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 := hU x n m x
  have h2 := hU x n x m
  have hxn : x ∈ S → x ≠ n := fun hx h => hn (h ▸ hx)
  rcases lt_trichotomy x n with hxn' | rfl | hxn'
  · rcases lt_trichotomy x m with hxm | rfl | hxm
    · by_cases hS : x ∈ S <;> simp [hS, hxn', hxm, not_lt_of_gt hxn', not_lt_of_gt hxm]
    · by_cases hS : x ∈ S <;> simp [hS, hxn', not_lt_of_gt hxn']
    · by_cases hS : x ∈ S <;> simp [hS, hxn', hxm, not_lt_of_gt hxn', not_lt_of_gt hxm]
  · simp [hn]
  · rcases lt_trichotomy x m with hxm | rfl | hxm
    · by_cases hS : x ∈ S <;> simp [hS, hxn', hxm, not_lt_of_gt hxn', not_lt_of_gt hxm, h1, h2]
    · by_cases hS : x ∈ S <;> simp [hS, hxn', not_lt_of_gt hxn']
    · by_cases hS : x ∈ S <;> simp [hS, hxn', hxm, not_lt_of_gt hxn', not_lt_of_gt hxm, h1, h2]

end KochHFAux

open Matrix KochHF

theorem solution {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) (n m : Fin K) (hn : n ∉ S) (hm : m ∈ S) :
    matEl (basisState S) (cdag m * cann n * hamiltonian T U) (basisState S) =
      fockMatrix T U S n m := by
  exact KochHFAux.main_fock_matrix_single_excitation T U hU S n m hn hm
