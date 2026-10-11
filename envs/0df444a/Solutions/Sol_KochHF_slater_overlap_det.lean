-- Prove2me | solution 1 for KochHF.slater_overlap_det
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T16:57:38.11898+00:00
-- url     : https://prove2.me/submissions/7f89c291-9dd3-44ad-abe1-36e8dc72f919

import Mathlib
import Definitions.Def_KochHF_FockSpace


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

/-! ### Linearity of `cdagOrb` and `cannOrb` -/

lemma cdagOrb_add (φ ψ : Fin K → ℂ) : cdagOrb (φ + ψ) = cdagOrb φ + cdagOrb ψ := by
  simp [cdagOrb, add_smul, Finset.sum_add_distrib]

lemma cdagOrb_smul (c : ℂ) (φ : Fin K → ℂ) : cdagOrb (c • φ) = c • cdagOrb φ := by
  simp [cdagOrb, Finset.smul_sum, smul_smul]

lemma cdagOrb_zero : cdagOrb (0 : Fin K → ℂ) = 0 := by
  simp [cdagOrb]

lemma cdagOrb_sub (φ ψ : Fin K → ℂ) : cdagOrb (φ - ψ) = cdagOrb φ - cdagOrb ψ := by
  simp [cdagOrb, sub_smul, Finset.sum_sub_distrib]

lemma cdagOrb_sum {ι : Type*} (s : Finset ι) (f : ι → Fin K → ℂ) :
    cdagOrb (∑ i ∈ s, f i) = ∑ i ∈ s, cdagOrb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cdagOrb_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cdagOrb_add, ih]

lemma cannOrb_add (φ ψ : Fin K → ℂ) : cannOrb (φ + ψ) = cannOrb φ + cannOrb ψ := by
  simp [cannOrb, add_smul, Finset.sum_add_distrib]

lemma cannOrb_smul (c : ℂ) (φ : Fin K → ℂ) : cannOrb (c • φ) = star c • cannOrb φ := by
  simp [cannOrb, Finset.smul_sum, smul_smul]

lemma cannOrb_zero : cannOrb (0 : Fin K → ℂ) = 0 := by
  simp [cannOrb]

lemma cannOrb_sub (φ ψ : Fin K → ℂ) : cannOrb (φ - ψ) = cannOrb φ - cannOrb ψ := by
  simp [cannOrb, sub_smul, Finset.sum_sub_distrib]

lemma cannOrb_sum {ι : Type*} (s : Finset ι) (f : ι → Fin K → ℂ) :
    cannOrb (∑ i ∈ s, f i) = ∑ i ∈ s, cannOrb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cannOrb_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cannOrb_add, ih]

lemma orbInner_conj (φ χ : Fin K → ℂ) : star (orbInner φ χ) = orbInner χ φ := by
  simp [orbInner, dotProduct, mul_comm]

lemma orbInner_add_right (φ χ ψ : Fin K → ℂ) :
    orbInner φ (χ + ψ) = orbInner φ χ + orbInner φ ψ := by
  simp [orbInner, dotProduct_add]

lemma orbInner_sub_right (φ χ ψ : Fin K → ℂ) :
    orbInner φ (χ - ψ) = orbInner φ χ - orbInner φ ψ := by
  simp [orbInner, dotProduct_sub]

lemma orbInner_smul_right (φ χ : Fin K → ℂ) (c : ℂ) :
    orbInner φ (c • χ) = c * orbInner φ χ := by
  simp [orbInner, dotProduct_smul]

lemma orbInner_sum_right {ι : Type*} (s : Finset ι) (φ : Fin K → ℂ) (f : ι → Fin K → ℂ) :
    orbInner φ (∑ i ∈ s, f i) = ∑ i ∈ s, orbInner φ (f i) := by
  simp [orbInner, dotProduct_sum]

/-! ### Elementary consequences of the anticommutation relations -/

lemma cdagOrb_mul_self (φ : Fin K → ℂ) : cdagOrb φ * cdagOrb φ = 0 := by
  have h := cdagOrb_anticomm φ φ
  rw [← two_smul ℂ] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

lemma cannOrb_cdagOrb_swap (χ φ : Fin K → ℂ) :
    cannOrb χ * cdagOrb φ = orbInner χ φ • (1 : FockOp K) - cdagOrb φ * cannOrb χ := by
  rw [← cannOrb_cdagOrb_anticomm]; abel

lemma cdagOrb_cdagOrb_swap (χ φ : Fin K → ℂ) :
    cdagOrb χ * cdagOrb φ = - (cdagOrb φ * cdagOrb χ) := by
  rw [eq_neg_iff_add_eq_zero]; exact cdagOrb_anticomm χ φ

/-! ### Slater determinants -/

lemma slater_zero (α : Fin 0 → Fin K → ℂ) : slater α = vacuum K := by
  simp [slater]

lemma slater_succ {N : ℕ} (α : Fin (N + 1) → Fin K → ℂ) :
    slater α = cdagOrb (α (Fin.last N)) *ᵥ slater (fun i => α (Fin.castSucc i)) := by
  unfold slater
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.prod_cons, mulVec_mulVec]

lemma cannOrb_slater_succ {N : ℕ} (χ : Fin K → ℂ) (α : Fin (N + 1) → Fin K → ℂ) :
    cannOrb χ *ᵥ slater α =
      orbInner χ (α (Fin.last N)) • slater (fun i => α (Fin.castSucc i)) -
        cdagOrb (α (Fin.last N)) *ᵥ (cannOrb χ *ᵥ slater (fun i => α (Fin.castSucc i))) := by
  rw [slater_succ, mulVec_mulVec, cannOrb_cdagOrb_swap, sub_mulVec, smul_mulVec, one_mulVec,
    mulVec_mulVec]

lemma cannOrb_slater_of_orth {N : ℕ} (χ : Fin K → ℂ) (α : Fin N → Fin K → ℂ)
    (h : ∀ i, orbInner χ (α i) = 0) : cannOrb χ *ᵥ slater α = 0 := by
  induction N with
  | zero => rw [slater_zero, cannOrb_vacuum]
  | succ N ih =>
    rw [cannOrb_slater_succ, h, ih _ (fun i => h _)]
    simp

lemma cdagOrb_mem_slater {N : ℕ} (α : Fin N → Fin K → ℂ) (k : Fin N) :
    cdagOrb (α k) *ᵥ slater α = 0 := by
  induction N with
  | zero => exact k.elim0
  | succ N ih =>
    rw [slater_succ, mulVec_mulVec]
    by_cases hk : k = Fin.last N
    · subst hk; rw [cdagOrb_mul_self, zero_mulVec]
    · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [cdagOrb_cdagOrb_swap, neg_mulVec, ← mulVec_mulVec,
        ih (fun i => α (Fin.castSucc i)) k']
      simp

lemma cdagOrb_span_slater {N : ℕ} (α : Fin N → Fin K → ℂ) (φ : Fin K → ℂ)
    (hφ : φ ∈ Submodule.span ℂ (Set.range α)) : cdagOrb φ *ᵥ slater α = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hφ
  rw [cdagOrb_sum, sum_mulVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cdagOrb_smul, smul_mulVec, cdagOrb_mem_slater, smul_zero]

/-- Orthonormality of a family of orbitals. -/
def Orthonormal' {N : ℕ} (α : Fin N → Fin K → ℂ) : Prop :=
  ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0

lemma Orthonormal'.castSucc {N : ℕ} {α : Fin (N + 1) → Fin K → ℂ} (hα : Orthonormal' α) :
    Orthonormal' (fun i => α (Fin.castSucc i)) := by
  intro i j; rw [hα]; simp [Fin.castSucc_inj]

/-- Number-operator identity: `c†_{α_k} c_{α_l} |Φ⟩ = δ_{kl} |Φ⟩` for orthonormal orbitals. -/
lemma cdag_cann_slater {N : ℕ} (α : Fin N → Fin K → ℂ) (hα : Orthonormal' α) (k l : Fin N) :
    cdagOrb (α k) *ᵥ (cannOrb (α l) *ᵥ slater α) = (if k = l then 1 else 0) • slater α := by
  induction N with
  | zero => exact k.elim0
  | succ N ih =>
    set α' := fun i => α (Fin.castSucc i) with hα'
    have hα'o := hα.castSucc
    by_cases hl : l = Fin.last N
    · subst hl
      have h0 : cannOrb (α (Fin.last N)) *ᵥ slater α' = 0 :=
        cannOrb_slater_of_orth _ _ fun i => by
          rw [hα, if_neg (fun h => Fin.castSucc_ne_last i h.symm)]
      rw [cannOrb_slater_succ, h0, hα]
      simp only [if_true, one_smul, mulVec_zero, sub_zero]
      by_cases hk : k = Fin.last N
      · subst hk; rw [← slater_succ]; simp
      · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
        rw [if_neg hk]
        simp only [zero_smul]
        exact cdagOrb_mem_slater α' k'
    · obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.mpr hl
      rw [cannOrb_slater_succ, hα]
      simp only [Fin.castSucc_ne_last, if_false, zero_smul, zero_sub, mulVec_neg]
      by_cases hk : k = Fin.last N
      · subst hk
        rw [mulVec_mulVec, cdagOrb_mul_self, zero_mulVec, neg_zero, if_neg (Ne.symm hl)]
        simp
      · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
        rw [mulVec_mulVec, cdagOrb_cdagOrb_swap, neg_mulVec, neg_neg, ← mulVec_mulVec]
        have := ih α' hα'o k' l'
        simp only [hα'] at this
        rw [this, mulVec_smul, ← slater_succ]
        simp [Fin.castSucc_inj]

end KochHFAux

open Matrix KochHF

namespace KochHFAux

variable {K : ℕ}

lemma castSucc_succAbove_last' {N : ℕ} (k : Fin (N + 1)) :
    (Fin.castSucc k).succAbove (Fin.last N) = Fin.last (N + 1) := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_last])]
  simp

/-- Laplace-type expansion of an annihilator acting on a Slater determinant (Eq. (42)). -/
lemma cannOrb_slater_laplace {N : ℕ} (χ : Fin K → ℂ) (α : Fin (N + 1) → Fin K → ℂ) :
    cannOrb χ *ᵥ slater α = ∑ k : Fin (N + 1),
      ((-1 : ℂ) ^ ((k : ℕ) + N) * orbInner χ (α k)) • slater (fun i => α (k.succAbove i)) := by
  induction N with
  | zero =>
    rw [cannOrb_slater_succ]
    simp [slater_zero, cannOrb_vacuum]
  | succ N ih =>
    rw [cannOrb_slater_succ, ih]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    rw [mulVec_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succAbove_last]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVec_smul, ← neg_smul]
      congr 1
      · rw [← add_assoc, pow_succ]; ring
      · rw [slater_succ]
        congr 1
        · rw [castSucc_succAbove_last']
        · congr 1
          funext i
          rw [Fin.castSucc_succAbove_castSucc]
    · rw [show (N + 1 + (N + 1)) = 2 * (N + 1) by ring, pow_mul]
      simp

lemma fockInner_mulVec (u w : FockVec K) (A : FockOp K) :
    fockInner u (A *ᵥ w) = fockInner (Aᴴ *ᵥ u) w := by
  simp only [fockInner, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

lemma fockInner_sum_left {ι : Type*} (s : Finset ι) (u : ι → FockVec K) (w : FockVec K) :
    fockInner (∑ i ∈ s, u i) w = ∑ i ∈ s, fockInner (u i) w := by
  simp [fockInner, star_sum, sum_dotProduct]

lemma fockInner_smul_left (c : ℂ) (u w : FockVec K) :
    fockInner (c • u) w = star c * fockInner u w := by
  simp [fockInner, star_smul, smul_dotProduct]

lemma fockInner_smul_right (c : ℂ) (u w : FockVec K) :
    fockInner u (c • w) = c * fockInner u w := by
  simp [fockInner, dotProduct_smul]

theorem main_slater_overlap_det {K N : ℕ} (α β : Fin N → Fin K → ℂ) :
    fockInner (slater α) (slater β) = (Matrix.of fun i j => orbInner (α i) (β j)).det := by
  induction N with
  | zero => simp [slater_zero, fockInner, vacuum, dotProduct, Pi.single_apply]
  | succ N ih =>
    rw [slater_succ β, fockInner_mulVec, cdagOrb_conjTranspose, cannOrb_slater_laplace,
      fockInner_sum_left, det_succ_column _ (Fin.last N)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fockInner_smul_left, ih]
    simp only [star_mul', star_pow, star_neg, star_one, orbInner_conj, of_apply, Fin.val_last,
      Fin.succAbove_last]
    congr 1

end KochHFAux

open Matrix KochHF

theorem solution {K N : ℕ} (α β : Fin N → Fin K → ℂ) :
    fockInner (slater α) (slater β) = (Matrix.of fun i j => orbInner (α i) (β j)).det := by
  exact KochHFAux.main_slater_overlap_det α β
