-- Prove2me | solution 1 for KochHF.slater_one_body_density
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T16:59:21.225757+00:00
-- url     : https://prove2.me/submissions/348fc279-336e-4b30-934d-4537d4a0d241

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

lemma occProj_mem_span {N : ℕ} (α : Fin N → Fin K → ℂ) (φ : Fin K → ℂ) :
    occProj α φ ∈ Submodule.span ℂ (Set.range α) :=
  Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

lemma orbInner_occProj {N : ℕ} (α : Fin N → Fin K → ℂ) (hα : Orthonormal' α)
    (φ : Fin K → ℂ) (i : Fin N) : orbInner (α i) (occProj α φ) = orbInner (α i) φ := by
  unfold occProj
  rw [orbInner_sum_right]
  simp only [orbInner_smul_right, hα i, mul_ite, mul_one, mul_zero]
  simp

lemma orbInner_sub_occProj {N : ℕ} (α : Fin N → Fin K → ℂ) (hα : Orthonormal' α)
    (φ : Fin K → ℂ) (i : Fin N) : orbInner (α i) (φ - occProj α φ) = 0 := by
  rw [orbInner_sub_right, orbInner_occProj α hα, sub_self]

lemma cannOrb_slater_of_orth' {N : ℕ} (χ : Fin K → ℂ) (α : Fin N → Fin K → ℂ)
    (h : ∀ i, orbInner (α i) χ = 0) : cannOrb χ *ᵥ slater α = 0 :=
  cannOrb_slater_of_orth χ α fun i => by rw [← orbInner_conj, h, star_zero]

theorem main_slater_projection_rules {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (φ : Fin K → ℂ) :
    cannOrb φ *ᵥ slater α = cannOrb (occProj α φ) *ᵥ slater α ∧
    cdagOrb φ *ᵥ slater α = cdagOrb (φ - occProj α φ) *ᵥ slater α := by
  constructor
  · have h := cannOrb_slater_of_orth' (φ - occProj α φ) α (orbInner_sub_occProj α hα φ)
    rw [cannOrb_sub, sub_mulVec, sub_eq_zero] at h
    exact h
  · rw [cdagOrb_sub, sub_mulVec, cdagOrb_span_slater α _ (occProj_mem_span α φ), sub_zero]

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

lemma matEl_mul_left (ψ φ : FockVec K) (A B : FockOp K) :
    matEl ψ (A * B) φ = star (Aᴴ *ᵥ ψ) ⬝ᵥ (B *ᵥ φ) := by
  simp only [matEl, star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec]

lemma matEl_conjTranspose (ψ : FockVec K) (A : FockOp K) :
    matEl ψ Aᴴ ψ = star (matEl ψ A ψ) := by
  simp only [matEl]
  rw [dotProduct_mulVec, ← star_mulVec, star_dotProduct]

lemma matEl_sum {ι : Type*} (s : Finset ι) (ψ φ : FockVec K) (A : ι → FockOp K) :
    matEl ψ (∑ i ∈ s, A i) φ = ∑ i ∈ s, matEl ψ (A i) φ := by
  simp [matEl, sum_mulVec, dotProduct_sum]

lemma cdagOrb_single (a : Fin K) : cdagOrb (Pi.single a (1 : ℂ)) = cdag a := by
  simp [cdagOrb, Pi.single_apply]

lemma cannOrb_single (a : Fin K) : cannOrb (Pi.single a (1 : ℂ)) = cann a := by
  simp [cannOrb, Pi.single_apply]

lemma oneBodyOp_add (M₁ M₂ : Matrix (Fin K) (Fin K) ℂ) :
    oneBodyOp (M₁ + M₂) = oneBodyOp M₁ + oneBodyOp M₂ := by
  simp [oneBodyOp, add_smul, Finset.sum_add_distrib]

lemma oneBodyOp_smul (c : ℂ) (M : Matrix (Fin K) (Fin K) ℂ) :
    oneBodyOp (c • M) = c • oneBodyOp M := by
  simp [oneBodyOp, Finset.smul_sum, smul_smul]

lemma oneBodyOp_rankOne (φ χ : Fin K → ℂ) :
    oneBodyOp (Matrix.of fun a b => φ a * star (χ b)) = cdagOrb φ * cannOrb χ := by
  simp only [oneBodyOp, cdagOrb, cannOrb, Finset.sum_mul, Finset.mul_sum, of_apply,
    smul_mul_smul_comm]
  exact Finset.sum_comm

/-- The commutator functional `M ↦ ⟨Φ|[M̂, H]|Φ⟩`. -/
noncomputable def commFun (Φ : FockVec K) (H : FockOp K) (M : Matrix (Fin K) (Fin K) ℂ) : ℂ :=
  matEl Φ (oneBodyOp M * H - H * oneBodyOp M) Φ

lemma commFun_add (Φ : FockVec K) (H : FockOp K) (M₁ M₂ : Matrix (Fin K) (Fin K) ℂ) :
    commFun Φ H (M₁ + M₂) = commFun Φ H M₁ + commFun Φ H M₂ := by
  simp only [commFun, oneBodyOp_add, add_mul, mul_add]
  rw [← matEl_add]; congr 1; abel

lemma commFun_smul (Φ : FockVec K) (H : FockOp K) (c : ℂ) (M : Matrix (Fin K) (Fin K) ℂ) :
    commFun Φ H (c • M) = c * commFun Φ H M := by
  simp only [commFun, oneBodyOp_smul, smul_mul_assoc, mul_smul_comm, ← smul_sub, matEl_smul]

lemma commFun_eq_sum (Φ : FockVec K) (H : FockOp K) (M : Matrix (Fin K) (Fin K) ℂ) :
    commFun Φ H M = ∑ a, ∑ b, M a b *
      matEl Φ (cdagOrb (Pi.single a 1) * cannOrb (Pi.single b 1) * H -
        H * (cdagOrb (Pi.single a 1) * cannOrb (Pi.single b 1))) Φ := by
  simp only [commFun, oneBodyOp, cdagOrb_single, cannOrb_single, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib, matEl_sum, smul_mul_assoc, mul_smul_comm,
    ← smul_sub, matEl_smul]

lemma commFun_herm_iff (Φ : FockVec K) (H : FockOp K) :
    (∀ M : Matrix (Fin K) (Fin K) ℂ, M.IsHermitian → commFun Φ H M = 0) ↔
      ∀ M, commFun Φ H M = 0 := by
  refine ⟨fun h M => ?_, fun h M _ => h M⟩
  have h₁ : (M + Mᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  have h₂ : ((-Complex.I) • (M - Mᴴ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      star_neg, Complex.star_def, Complex.conj_I, ← neg_sub M, smul_neg, neg_smul, neg_neg]
  have hM : (2 : ℂ) • M = (M + Mᴴ) + Complex.I • ((-Complex.I) • (M - Mᴴ)) := by
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul, two_smul]
    abel
  have key : (2 : ℂ) * commFun Φ H M = 0 := by
    rw [← commFun_smul, hM, commFun_add, commFun_smul, h _ h₁, h _ h₂]
    simp
  simpa using key

section Brillouin

variable {N : ℕ} (α : Fin N → Fin K → ℂ)

/-- Scalar action of an occupied-occupied excitation on the Slater determinant. -/
lemma occ_occ_scalar (hα : Orthonormal' α) (a b : Fin N → ℂ) :
    (cdagOrb (∑ k, a k • α k) * cannOrb (∑ l, b l • α l)) *ᵥ slater α =
      (∑ k, a k * star (b k)) • slater α := by
  rw [cdagOrb_sum, cannOrb_sum, Finset.sum_mul, sum_mulVec, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, sum_mulVec]
  simp only [cdagOrb_smul, cannOrb_smul, smul_mul_smul_comm, smul_mulVec, ← mulVec_mulVec,
    cdag_cann_slater α hα]
  simp

lemma occProj_eq_sum (φ : Fin K → ℂ) :
    occProj α φ = ∑ k, orbInner (α k) φ • α k := rfl

/-- The key decomposition: the commutator matrix element for `c†_φ c_χ` vanishes
under the Brillouin condition. -/
lemma comm_elem_zero (H : FockOp K) (hH : H.IsHermitian) (hα : Orthonormal' α)
    (hcond : ∀ φo φv : Fin K → ℂ, φo ∈ Submodule.span ℂ (Set.range α) →
      (∀ i, orbInner (α i) φv = 0) →
      matEl (slater α) (cdagOrb φo * cannOrb φv * H) (slater α) = 0)
    (φ χ : Fin K → ℂ) :
    matEl (slater α) (cdagOrb φ * cannOrb χ * H - H * (cdagOrb φ * cannOrb χ)) (slater α) = 0 := by
  obtain ⟨hc, hd⟩ := main_slater_projection_rules α hα φ
  obtain ⟨hc', hd'⟩ := main_slater_projection_rules α hα χ
  have hφo := occProj_mem_span α φ
  have hχo := occProj_mem_span α χ
  have hφv := orbInner_sub_occProj α hα φ
  have hχv := orbInner_sub_occProj α hα χ
  -- first term
  have T1 : matEl (slater α) (cdagOrb φ * cannOrb χ * H) (slater α) =
      matEl (slater α) (cdagOrb (occProj α φ) * cannOrb (occProj α χ) * H) (slater α) := by
    rw [mul_assoc, matEl_mul_left, cdagOrb_conjTranspose, hc, ← cdagOrb_conjTranspose,
      ← matEl_mul_left, ← mul_assoc]
    have hsplit : χ = occProj α χ + (χ - occProj α χ) := by abel
    conv_lhs => rw [hsplit, cannOrb_add, mul_add, add_mul, matEl_add,
      hcond _ _ hφo hχv, add_zero]
  -- second term
  have T2 : matEl (slater α) (H * (cdagOrb φ * cannOrb χ)) (slater α) =
      matEl (slater α) (H * (cdagOrb (occProj α φ) * cannOrb (occProj α χ))) (slater α) := by
    have hsplit : φ = occProj α φ + (φ - occProj α φ) := by abel
    have e1 : matEl (slater α) (H * (cdagOrb φ * cannOrb χ)) (slater α) =
        matEl (slater α) (H * (cdagOrb φ * cannOrb (occProj α χ))) (slater α) := by
      simp only [matEl, ← mulVec_mulVec, hc']
    rw [e1]
    conv_lhs => rw [hsplit, cdagOrb_add, add_mul, mul_add, matEl_add]
    have : matEl (slater α) (H * (cdagOrb (φ - occProj α φ) * cannOrb (occProj α χ))) (slater α) = 0 := by
      have h0 := hcond _ _ hχo hφv
      have e : (H * (cdagOrb (φ - occProj α φ) * cannOrb (occProj α χ))) =
          (cdagOrb (occProj α χ) * cannOrb (φ - occProj α φ) * H)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_mul, hH.eq, cdagOrb_conjTranspose,
          cannOrb_conjTranspose]
      rw [e, matEl_conjTranspose, h0, star_zero]
    rw [this, add_zero]
  rw [matEl_sub, T1, T2, ← matEl_sub]
  -- scalar part
  have hY := occ_occ_scalar α hα (fun k => orbInner (α k) φ) (fun k => orbInner (α k) χ)
  have hY' := occ_occ_scalar α hα (fun k => orbInner (α k) χ) (fun k => orbInner (α k) φ)
  rw [← occProj_eq_sum, ← occProj_eq_sum] at hY hY'
  rw [matEl_sub, matEl_mul_left, conjTranspose_mul, cdagOrb_conjTranspose,
    cannOrb_conjTranspose, hY']
  simp only [matEl, ← mulVec_mulVec]
  rw [← mulVec_mulVec] at hY
  rw [hY, mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
  rw [star_sum]
  simp only [star_mul', star_star, smul_eq_mul]
  rw [sub_eq_zero]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Brillouin

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

namespace KochHFAux

variable {K : ℕ}

lemma slater_norm {N : ℕ} (α : Fin N → Fin K → ℂ) (hα : Orthonormal' α) :
    fockInner (slater α) (slater α) = 1 := by
  rw [main_slater_overlap_det]
  have : (Matrix.of fun i j => orbInner (α i) (α j)) = 1 := by
    ext i j; simpa [one_apply] using hα i j
  rw [this, det_one]

theorem main_slater_one_body_density {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (n m : Fin K) :
    matEl (slater α) (cdag n * cann m) (slater α) =
      orbInner (Pi.single m 1) (occProj α (Pi.single n 1)) := by
  obtain ⟨hc, -⟩ := main_slater_projection_rules α hα (Pi.single n 1)
  obtain ⟨hc', -⟩ := main_slater_projection_rules α hα (Pi.single m 1)
  rw [← cdagOrb_single, ← cannOrb_single, matEl_mul_left, cdagOrb_conjTranspose, hc, hc',
    ← cdagOrb_conjTranspose, ← matEl_mul_left]
  have hY := occ_occ_scalar α hα (fun k => orbInner (α k) (Pi.single n 1))
    (fun k => orbInner (α k) (Pi.single m 1))
  rw [← occProj_eq_sum, ← occProj_eq_sum] at hY
  rw [matEl, hY, dotProduct_smul]
  change _ * fockInner (slater α) (slater α) = _
  rw [slater_norm α hα, mul_one, occProj_eq_sum, orbInner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [orbInner_smul_right, ← orbInner_conj (α k)]

end KochHFAux

open Matrix KochHF

theorem solution {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (n m : Fin K) :
    matEl (slater α) (cdag n * cann m) (slater α) =
      orbInner (Pi.single m 1) (occProj α (Pi.single n 1)) := by
  exact KochHFAux.main_slater_one_body_density α hα n m
