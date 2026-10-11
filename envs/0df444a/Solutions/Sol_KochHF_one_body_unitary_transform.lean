-- Prove2me | solution 1 for KochHF.one_body_unitary_transform
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T16:53:16.985282+00:00
-- url     : https://prove2.me/submissions/d11df897-13b1-420a-b699-285eba436652

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

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {K : ℕ}

lemma const_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (h : ∀ s, HasDerivAt F 0 s) (x y : ℝ) : F x = F y :=
  is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) x y

/-- `Y ↦ Y *ᵥ v` as a real-linear map. -/
noncomputable def mulVecRLin (v : FockVec K) : FockOp K →ₗ[ℝ] FockVec K where
  toFun Y := Y *ᵥ v
  map_add' A B := add_mulVec A B v
  map_smul' c A := by simp [smul_mulVec]

lemma exp_mulVec_of_mulVec_eq_zero (X : FockOp K) (v : FockVec K) (hX : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp (t • X) *ᵥ v = v := by
  let L := LinearMap.toContinuousLinearMap (mulVecRLin v)
  have h : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) *ᵥ v) 0 s := by
    intro s
    have h1 := L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s)
    refine h1.congr_deriv ?_
    show (NormedSpace.exp (s • X) * X) *ᵥ v = 0
    rw [← mulVec_mulVec, hX, mulVec_zero]
  have := const_of_hasDerivAt_zero _ h t 0
  simpa using this

lemma oneBodyOp_vacuum (M : Matrix (Fin K) (Fin K) ℂ) : oneBodyOp M *ᵥ vacuum K = 0 := by
  simp [oneBodyOp, sum_mulVec, smul_mulVec, ← mulVec_mulVec, cann_vacuum]

lemma comm_cdag_cann_cdag (a b c : Fin K) :
    cdag a * cann b * cdag c - cdag c * (cdag a * cann b) =
      (if b = c then 1 else 0) • cdag a := by
  have h1 : cann b * cdag c = (if b = c then 1 else 0) - cdag c * cann b := by
    rw [← cann_cdag_anticomm]; abel
  have h2 : cdag a * cdag c = -(cdag c * cdag a) := by
    rw [eq_neg_iff_add_eq_zero]; exact cdag_anticomm a c
  rw [mul_assoc, h1, mul_sub, ← mul_assoc, h2]
  split_ifs <;> simp [mul_assoc]

/-- `Φ_γ(E) = Σ_a E_{aγ} c†_a`. -/
noncomputable def colCdag (γ : Fin K) (E : Matrix (Fin K) (Fin K) ℂ) : FockOp K :=
  ∑ a, E a γ • cdag a

lemma comm_oneBody_cdag (M : Matrix (Fin K) (Fin K) ℂ) (c : Fin K) :
    oneBodyOp M * cdag c - cdag c * oneBodyOp M = ∑ a, M a c • cdag a := by
  simp only [oneBodyOp, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    smul_mul_assoc, mul_smul_comm, ← smul_sub, comm_cdag_cann_cdag]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [smul_smul]

lemma comm_oneBody_colCdag (M E : Matrix (Fin K) (Fin K) ℂ) (γ : Fin K) :
    oneBodyOp M * colCdag γ E - colCdag γ E * oneBodyOp M = colCdag γ (M * E) := by
  simp only [colCdag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm,
    smul_mul_assoc, ← smul_sub, comm_oneBody_cdag, Finset.smul_sum, smul_smul, mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

lemma colCdag_add (γ : Fin K) (E F : Matrix (Fin K) (Fin K) ℂ) :
    colCdag γ (E + F) = colCdag γ E + colCdag γ F := by
  simp [colCdag, add_smul, Finset.sum_add_distrib]

lemma colCdag_smul (γ : Fin K) (c : ℂ) (E : Matrix (Fin K) (Fin K) ℂ) :
    colCdag γ (c • E) = c • colCdag γ E := by
  simp [colCdag, Finset.smul_sum, smul_smul]

lemma colCdag_one (γ : Fin K) : colCdag γ (1 : Matrix (Fin K) (Fin K) ℂ) = cdag γ := by
  simp [colCdag, one_apply]

noncomputable def colCdagLin (γ : Fin K) : Matrix (Fin K) (Fin K) ℂ →ₗ[ℝ] FockOp K where
  toFun := colCdag γ
  map_add' := colCdag_add γ
  map_smul' c E := by
    simp only [RingHom.id_apply]
    rw [← Complex.coe_smul, colCdag_smul, Complex.coe_smul]

lemma real_smul_eq' {E : Type*} [AddCommGroup E] [Module ℂ E] (A : E) (t : ℝ) :
    (Complex.I * t) • A = t • (Complex.I • A) := by
  rw [mul_comm, ← smul_smul, Complex.coe_smul]

lemma exp_mul_exp_neg (x : FockOp K) :
    NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.refl x).neg_right
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h.symm

lemma exp_neg_mul_exp (x : FockOp K) :
    NormedSpace.exp (-x) * NormedSpace.exp x = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.refl x).neg_left
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm

theorem main_one_body_unitary_transform {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ)
    (hM : M.IsHermitian) (t : ℝ) (γ : Fin K) :
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) *ᵥ vacuum K = vacuum K ∧
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * cdag γ *
        NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M) =
      ∑ a, NormedSpace.exp ((Complex.I * t) • M) a γ • cdag a := by
  constructor
  · rw [real_smul_eq']
    apply exp_mulVec_of_mulVec_eq_zero
    rw [smul_mulVec, oneBodyOp_vacuum, smul_zero]
  set X : FockOp K := Complex.I • oneBodyOp M with hX
  set Y : Matrix (Fin K) (Fin K) ℂ := Complex.I • M with hY
  have hXY : ∀ E, colCdag γ (Y * E) = X * colCdag γ E - colCdag γ E * X := by
    intro E
    rw [hX, hY, smul_mul_assoc, colCdag_smul, ← comm_oneBody_colCdag, smul_sub,
      smul_mul_assoc, mul_smul_comm]
  let G : ℝ → FockOp K := fun s => NormedSpace.exp (s • (-X)) *
    colCdag γ (NormedSpace.exp (s • Y)) * NormedSpace.exp (s • X)
  have hG : ∀ s, HasDerivAt G 0 s := by
    intro s
    have hV := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) s
    have hU := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
    have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y s
    let L := LinearMap.toContinuousLinearMap (colCdagLin (K := K) γ)
    have hΦ := L.hasFDerivAt.comp_hasDerivAt s hE
    have h := HasDerivAt.fun_mul (HasDerivAt.fun_mul hV hΦ) hU
    refine h.congr_deriv ?_
    show (NormedSpace.exp (s • -X) * -X * colCdag γ (NormedSpace.exp (s • Y)) +
      NormedSpace.exp (s • -X) * colCdag γ (Y * NormedSpace.exp (s • Y))) *
        NormedSpace.exp (s • X) +
      NormedSpace.exp (s • -X) * colCdag γ (NormedSpace.exp (s • Y)) *
        (X * NormedSpace.exp (s • X)) = 0
    rw [hXY]
    noncomm_ring
  have hGt := const_of_hasDerivAt_zero G hG t 0
  simp only [G, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, colCdag_one] at hGt
  have e1 : (Complex.I * t) • oneBodyOp M = t • X := real_smul_eq' _ _
  have e2 : (-(Complex.I * t)) • oneBodyOp M = -(t • X) := by rw [neg_smul, e1]
  have e3 : (Complex.I * t) • M = t • Y := real_smul_eq' _ _
  rw [smul_neg] at hGt
  change _ = colCdag γ _
  rw [e1, e2, e3, ← hGt]
  simp only [← mul_assoc]
  rw [exp_mul_exp_neg, one_mul, mul_assoc, exp_mul_exp_neg, mul_one]

end KochHFAux

open Matrix KochHF

theorem solution {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian)
    (t : ℝ) (γ : Fin K) :
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) *ᵥ vacuum K = vacuum K ∧
    NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * cdag γ *
        NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M) =
      ∑ a, NormedSpace.exp ((Complex.I * t) • M) a γ • cdag a := by
  exact KochHFAux.main_one_body_unitary_transform M hM t γ
