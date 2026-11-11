-- Prove2me | solution 1 for IncentiveFinNet.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:51:22.432096+00:00
-- url     : https://prove2.me/submissions/2eaf908a-d5df-40b4-8d99-8ce1db0e0ba0

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_Stable
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import Definitions.Def_IncentiveFinNet_ZF
import Mathlib.Data.Matrix.Basis

set_option autoImplicit false

open Matrix

namespace IncentiveFinNet.S01

variable {n : ℕ} (S : NetworkSetting n)

/-- The published selection-matrix expression is exactly a principal submatrix.
This identity also applies when the permitted-counterparty type is empty. -/
theorem selected_covariance_eq (i : Fin n) :
    S.Psi i * S.Sig i * (S.Psi i)ᵀ =
      (S.Sig i).submatrix (fun a : {k // k ∈ S.J i} => a.1) (fun a => a.1) := by
  ext a b
  simp [NetworkSetting.Psi, Matrix.mul_apply]

theorem selected_covariance_posDef (i : Fin n) :
    (S.Psi i * S.Sig i * (S.Psi i)ᵀ).PosDef := by
  rw [selected_covariance_eq]
  exact (S.Sig_posDef i).submatrix Subtype.val_injective

theorem restricted_hessian_posDef (i : Fin n) :
    ((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ)).PosDef :=
  (selected_covariance_posDef S i).smul (mul_pos (by norm_num) (S.γ_pos i))

theorem restricted_hessian_isUnit (i : Fin n) :
    IsUnit ((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ)) :=
  (restricted_hessian_posDef S i).isUnit

theorem psi_mulVec_apply (i : Fin n) (v : Fin n → ℝ) (a : {k // k ∈ S.J i}) :
    (S.Psi i *ᵥ v) a = v a.1 := by
  simp [NetworkSetting.Psi, Matrix.mulVec, dotProduct]

theorem psi_transpose_mulVec_apply (i : Fin n) (v : {k // k ∈ S.J i} → ℝ)
    (a : {k // k ∈ S.J i}) : ((S.Psi i)ᵀ *ᵥ v) a.1 = v a := by
  simp [NetworkSetting.Psi, Matrix.mulVec, dotProduct]

theorem psi_transpose_mulVec_zero (i k : Fin n) (v : {k // k ∈ S.J i} → ℝ)
    (hk : k ∉ S.J i) : ((S.Psi i)ᵀ *ᵥ v) k = 0 := by
  change (∑ a : {k // k ∈ S.J i}, (if k = a.1 then 1 else 0) * v a) = 0
  apply Finset.sum_eq_zero
  intro a _
  have hne : k ≠ a.1 := by
    intro h
    exact hk (h.symm ▸ a.2)
  simp [hne]

theorem psi_project_supported (i : Fin n) (v : Fin n → ℝ)
    (hv : ∀ k, k ∉ S.J i → v k = 0) :
    (S.Psi i)ᵀ *ᵥ (S.Psi i *ᵥ v) = v := by
  funext k
  by_cases hk : k ∈ S.J i
  · exact (psi_transpose_mulVec_apply S i _ ⟨k, hk⟩).trans
      (psi_mulVec_apply S i v ⟨k, hk⟩)
  · rw [psi_transpose_mulVec_zero S i k _ hk, hv k hk]

/-- A vector supported on the agent's permitted coordinates can be realized as
that column of a symmetric contract matrix. -/
def columnExtension (i : Fin n) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => if k = i then v j else if j = i then v k else 0

theorem columnExtension_column (i : Fin n) (v : Fin n → ℝ) :
    (fun j => columnExtension i v j i) = v := by
  funext j
  simp [columnExtension]

theorem columnExtension_feasible (i : Fin n) (v : Fin n → ℝ)
    (hv : ∀ k, k ∉ S.J i → v k = 0) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hP0 : ∀ j k, k ∉ S.J j → P j k = 0) :
    Feasible S (columnExtension i v) P := by
  refine ⟨?_, hP, ?_⟩
  · ext j k
    by_cases hj : j = i <;> by_cases hk : k = i <;>
      simp_all [columnExtension]
  · intro j k hkj
    refine ⟨?_, hP0 j k hkj⟩
    by_cases hk : k = i
    · subst k
      simp only [columnExtension]
      exact hv j (fun hj => hkj ((S.J_symm i j).mp hj))
    · by_cases hj : j = i
      · subst j
        simp [columnExtension, hk, hv k hkj]
      · simp [columnExtension, hj, hk]

section Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completing the square with the exact matrix inverse used by the platform.
The formula is dimension-free and does not assume a nonempty index type. -/
theorem quadratic_complete_square (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (b y : ι → ℝ) :
    y ⬝ᵥ b - (1 / 2 : ℝ) * (y ⬝ᵥ (K *ᵥ y)) =
      (K⁻¹ *ᵥ b) ⬝ᵥ b - (1 / 2 : ℝ) * ((K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ b))) -
        (1 / 2 : ℝ) * ((y - K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ (y - K⁻¹ *ᵥ b))) := by
  have hinv : K *ᵥ (K⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, K.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit),
      one_mulVec]
  have hsymm : Kᵀ = K := by
    exact Matrix.isHermitian_iff_isSymm.mp hK.isHermitian
  have hcross : (K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ y) = y ⬝ᵥ b := by
    calc
      _ = (K⁻¹ *ᵥ b) ⬝ᵥ (Kᵀ *ᵥ y) := by rw [hsymm]
      _ = y ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ b)) := dotProduct_transpose_mulVec _ _ _
      _ = y ⬝ᵥ b := by rw [hinv]
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hcross, hinv]
  ring

theorem quadratic_unique_maximum (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (b : ι → ℝ) :
    (∀ y : ι → ℝ,
      y ⬝ᵥ b - (1 / 2 : ℝ) * (y ⬝ᵥ (K *ᵥ y)) ≤
        (K⁻¹ *ᵥ b) ⬝ᵥ b - (1 / 2 : ℝ) * ((K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ b)))) ∧
    (∀ y : ι → ℝ,
      (K⁻¹ *ᵥ b) ⬝ᵥ b - (1 / 2 : ℝ) * ((K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ b))) ≤
        y ⬝ᵥ b - (1 / 2 : ℝ) * (y ⬝ᵥ (K *ᵥ y)) → y = K⁻¹ *ᵥ b) := by
  constructor
  · intro y
    rw [quadratic_complete_square K hK b y]
    have hnonneg := hK.posSemidef.dotProduct_mulVec_nonneg (y - K⁻¹ *ᵥ b)
    simp only [star_trivial] at hnonneg
    linarith
  · intro y hy
    by_contra hne
    have hpos := hK.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial] at hpos
    rw [quadratic_complete_square K hK b y] at hy
    linarith

end Quadratic

/-- The original utility depends only on the displayed agent column. -/
def columnValue (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  v ⬝ᵥ (fun k => S.M k i - P k i) - S.γ i * (v ⬝ᵥ (S.Sig i *ᵥ v))

theorem utility_eq_columnValue (i : Fin n) (W P : Matrix (Fin n) (Fin n) ℝ) :
    S.utility i W P = columnValue S i P (fun k => W k i) := rfl

theorem columnValue_embed (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ)
    (u : {k // k ∈ S.J i} → ℝ) :
    columnValue S i P ((S.Psi i)ᵀ *ᵥ u) =
      u ⬝ᵥ (S.Psi i *ᵥ (fun k => S.M k i - P k i)) - (1 / 2 : ℝ) *
        (u ⬝ᵥ (((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ)) *ᵥ u)) := by
  have hlin : ((S.Psi i)ᵀ *ᵥ u) ⬝ᵥ (fun k => S.M k i - P k i) =
      u ⬝ᵥ (S.Psi i *ᵥ (fun k => S.M k i - P k i)) := by
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
  have hquad : ((S.Psi i)ᵀ *ᵥ u) ⬝ᵥ (S.Sig i *ᵥ ((S.Psi i)ᵀ *ᵥ u)) =
      u ⬝ᵥ ((S.Psi i * S.Sig i * (S.Psi i)ᵀ) *ᵥ u) := by
    rw [dotProduct_comm, dotProduct_transpose_mulVec, mulVec_mulVec, mulVec_mulVec]
  unfold columnValue
  rw [hlin, hquad, smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem bestResponse_column (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ) :
    (fun k => bestResponse S P k i) =
      (S.Psi i)ᵀ *ᵥ
        (((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ))⁻¹ *ᵥ
          (S.Psi i *ᵥ (fun k => S.M k i - P k i))) := by
  change (Q S i *ᵥ (fun k => S.M k i - P k i)) = _
  unfold Q
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem bestResponse_column_supported (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) (hk : k ∉ S.J i) : bestResponse S P k i = 0 := by
  have h := congrFun (bestResponse_column S i P) k
  rw [h]
  exact psi_transpose_mulVec_zero S i k _ hk

theorem bestResponse_maximizes_column (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∀ k, k ∉ S.J i → v k = 0) :
    columnValue S i P v ≤ columnValue S i P (fun k => bestResponse S P k i) := by
  conv_lhs => rw [← psi_project_supported S i v hv]
  rw [bestResponse_column, columnValue_embed, columnValue_embed]
  exact (quadratic_unique_maximum _ (restricted_hessian_posDef S i) _).1 _

theorem bestResponse_unique_column (i : Fin n) (P : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∀ k, k ∉ S.J i → v k = 0)
    (hmax : columnValue S i P (fun k => bestResponse S P k i) ≤ columnValue S i P v) :
    v = fun k => bestResponse S P k i := by
  have hemb := psi_project_supported S i v hv
  have hlocal : S.Psi i *ᵥ v =
      ((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ))⁻¹ *ᵥ
        (S.Psi i *ᵥ (fun k => S.M k i - P k i)) := by
    apply (quadratic_unique_maximum _ (restricted_hessian_posDef S i) _).2
    conv_rhs at hmax => rw [← hemb]
    rwa [bestResponse_column, columnValue_embed, columnValue_embed] at hmax
  rw [← hemb, hlocal, bestResponse_column]

theorem feasible_column_supported (i : Fin n) (W P : Matrix (Fin n) (Fin n) ℝ)
    (hF : Feasible S W P) : ∀ k, k ∉ S.J i → W k i = 0 := by
  intro k hk
  exact (hF.2.2 k i (fun h => hk ((S.J_symm k i).mp h))).1

theorem stable_iff_feasible_and_bestResponse (W P : Matrix (Fin n) (Fin n) ℝ) :
    Stable S W P ↔ Feasible S W P ∧ W = bestResponse S P := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    ext k i
    let W' := columnExtension i (fun k => bestResponse S P k i)
    have hF' : Feasible S W' P := columnExtension_feasible S i _
      (bestResponse_column_supported S i P) P h.1.2.1
      (fun j k hjk => (h.1.2.2 j k hjk).2)
    have hopt := h.2 i W' hF'
    have hcol := bestResponse_unique_column S i P (fun k => W k i)
      (feasible_column_supported S i W P h.1)
      (by simpa only [utility_eq_columnValue, W', columnExtension_column] using hopt)
    exact congrFun hcol k
  · rintro ⟨hF, rfl⟩
    refine ⟨hF, ?_⟩
    intro i W' hF'
    simpa only [utility_eq_columnValue] using
      bestResponse_maximizes_column S i P (fun k => W' k i)
        (feasible_column_supported S i W' P hF')

end IncentiveFinNet.S01

open Matrix

namespace IncentiveFinNet.S01

/-- Full rank gives a bijective square real linear system, including the empty type. -/
theorem mulVec_bijective_of_full_rank {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.rank = Fintype.card ι) :
    Function.Bijective (fun p : ι → ℝ => A *ᵥ p) := by
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using hA
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp hrange
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

end IncentiveFinNet.S01

open Matrix
open scoped BigOperators

namespace IncentiveFinNet.S01

variable {n : ℕ}

/-- A single permitted upper-triangle price and its negative transpose. -/
def edgeMatrix (S : NetworkSetting n) (e : PermittedPairs S) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single e.1.1 e.1.2 1 - Matrix.single e.1.2 e.1.1 1

noncomputable def priceMatrix (S : NetworkSetting n) (p : PermittedPairs S → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ e, p e • edgeMatrix S e

theorem edgeMatrix_skew (S : NetworkSetting n) (e : PermittedPairs S) :
    (edgeMatrix S e)ᵀ = -edgeMatrix S e := by
  simp [edgeMatrix, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]

theorem edgeMatrix_forbidden (S : NetworkSetting n) (e : PermittedPairs S)
    (i j : Fin n) (hj : j ∉ S.J i) : edgeMatrix S e i j = 0 := by
  have hforward : ¬ (e.1.1 = i ∧ e.1.2 = j) := by
    rintro ⟨ha, hb⟩
    exact hj (ha ▸ hb ▸ e.2.2)
  have hreverse : ¬ (e.1.2 = i ∧ e.1.1 = j) := by
    rintro ⟨ha, hb⟩
    have hmem := (S.J_symm e.1.1 e.1.2).mp e.2.2
    exact hj (ha ▸ hb ▸ hmem)
  simp [edgeMatrix, Matrix.single_apply, hforward, hreverse]

theorem edgeMatrix_upper (S : NetworkSetting n) (e f : PermittedPairs S) :
    edgeMatrix S e f.1.1 f.1.2 = if e = f then 1 else 0 := by
  have hreverse : ¬ (e.1.2 = f.1.1 ∧ e.1.1 = f.1.2) := by
    rintro ⟨ha, hb⟩
    have he := e.2.1
    have hf := f.2.1
    omega
  have hforward : (e.1.1 = f.1.1 ∧ e.1.2 = f.1.2) ↔ e = f := by
    constructor
    · rintro ⟨ha, hb⟩
      exact Subtype.ext (Prod.ext ha hb)
    · intro h
      subst f
      exact ⟨rfl, rfl⟩
  simp [edgeMatrix, Matrix.single_apply, hreverse, hforward]

theorem priceMatrix_skew (S : NetworkSetting n) (p : PermittedPairs S → ℝ) :
    (priceMatrix S p)ᵀ = -priceMatrix S p := by
  simp [priceMatrix, Matrix.transpose_sum, Matrix.transpose_smul, edgeMatrix_skew,
    Finset.sum_neg_distrib]

theorem priceMatrix_forbidden (S : NetworkSetting n) (p : PermittedPairs S → ℝ)
    (i j : Fin n) (hj : j ∉ S.J i) : priceMatrix S p i j = 0 := by
  simp [priceMatrix, Matrix.sum_apply, edgeMatrix_forbidden S _ i j hj]

theorem uvecF_priceMatrix (S : NetworkSetting n) (p : PermittedPairs S → ℝ) :
    uvecF S (priceMatrix S p) = p := by
  funext f
  simp [uvecF, priceMatrix, Matrix.sum_apply, edgeMatrix_upper, smul_eq_mul]

theorem skew_eq_of_upper (P R : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hR : Rᵀ = -R)
    (hupper : ∀ i j, i < j → P i j = R i j) : P = R := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hupper i j hij
  · subst j
    have hp := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X i i) hP
    have hr := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X i i) hR
    change P i i = -P i i at hp
    change R i i = -R i i at hr
    linarith
  · have hp := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X j i) hP
    have hr := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X j i) hR
    change P i j = -P j i at hp
    change R i j = -R j i at hr
    rw [hp, hr, hupper j i hij]

theorem price_eq_of_uvecF (S : NetworkSetting n) (P R : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hR : Rᵀ = -R)
    (hP0 : ∀ i j, j ∉ S.J i → P i j = 0)
    (hR0 : ∀ i j, j ∉ S.J i → R i j = 0)
    (hvec : uvecF S P = uvecF S R) : P = R := by
  apply skew_eq_of_upper P R hP hR
  intro i j hij
  by_cases hj : j ∈ S.J i
  · exact congrFun hvec ⟨(i, j), hij, hj⟩
  · rw [hP0 i j hj, hR0 i j hj]

theorem priceMatrix_uvecF (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hP0 : ∀ i j, j ∉ S.J i → P i j = 0) :
    priceMatrix S (uvecF S P) = P := by
  exact price_eq_of_uvecF S _ P (priceMatrix_skew S _) hP
    (priceMatrix_forbidden S _) hP0 (uvecF_priceMatrix S _)

theorem matB_entry (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j a b : Fin n) :
    matB Q i j a b = if a = i then Q i j b else 0 := by
  simp [matB, Matrix.mul_apply, Matrix.vecMulVec, Pi.single_apply]

theorem mul_single_entry (Q : Matrix (Fin n) (Fin n) ℝ) (i j a b : Fin n) :
    (Q * (Matrix.single i j (1 : ℝ) : Matrix (Fin n) (Fin n) ℝ)) a b = if b = j then Q a i else 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, eq_comm]

theorem ZF_edge_coefficient (S : NetworkSetting n) (e f : PermittedPairs S) :
    ZF S e f =
      (Q S e.1.2 * edgeMatrix S f) e.1.1 e.1.2 -
        (Q S e.1.1 * edgeMatrix S f) e.1.2 e.1.1 := by
  simp only [ZF, Matrix.of_apply, uvecF, matC, Matrix.sub_apply, Matrix.transpose_apply,
    matB_entry, edgeMatrix, Matrix.mul_sub, mul_single_entry]
  simp only [eq_comm]
  split_ifs <;> ring

theorem ZF_priceMatrix (S : NetworkSetting n) (p : PermittedPairs S → ℝ) :
    ZF S *ᵥ p = fun e =>
      (Q S e.1.2 * priceMatrix S p) e.1.1 e.1.2 -
        (Q S e.1.1 * priceMatrix S p) e.1.2 e.1.1 := by
  funext e
  simp only [priceMatrix, Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  rw [ZF_edge_coefficient]
  ring

theorem matA_entry (S : NetworkSetting n) (i j : Fin n) :
    matA S i j = (Q S j * S.M) i j := by
  simp [matA, Matrix.mulVec_single, single_dotProduct]

theorem ZF_uvecF (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hP0 : ∀ i j, j ∉ S.J i → P i j = 0) :
    ZF S *ᵥ uvecF S P = fun e =>
      (Q S e.1.2 * P) e.1.1 e.1.2 - (Q S e.1.1 * P) e.1.2 e.1.1 := by
  rw [ZF_priceMatrix, priceMatrix_uvecF S P hP hP0]

theorem bestResponse_forbidden (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hj : j ∉ S.J i) : bestResponse S P i j = 0 := by
  apply bestResponse_column_supported S j P i
  intro hi
  exact hj ((S.J_symm i j).mpr hi)

theorem transpose_eq_iff_upper (B : Matrix (Fin n) (Fin n) ℝ) :
    Bᵀ = B ↔ ∀ i j, i < j → B i j = B j i := by
  constructor
  · intro h i j _
    exact (congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X i j) h).symm
  · intro h
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (h i j hij).symm
    · subst j
      rfl
    · exact h j i hij

theorem bestResponse_symmetric_iff (S : NetworkSetting n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = -P)
    (hP0 : ∀ i j, j ∉ S.J i → P i j = 0) :
    (bestResponse S P)ᵀ = bestResponse S P ↔
      ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ) := by
  rw [transpose_eq_iff_upper, ZF_uvecF S P hP hP0]
  constructor
  · intro h
    funext e
    have he := h e.1.1 e.1.2 e.2.1
    simp only [bestResponse, Matrix.of_apply, Matrix.mul_sub, Matrix.sub_apply] at he
    simp only [uvecF, Matrix.sub_apply, Matrix.transpose_apply, matA_entry]
    linarith
  · intro h i j hij
    by_cases hj : j ∈ S.J i
    · have he := congrFun h (⟨(i, j), hij, hj⟩ : PermittedPairs S)
      simp only [uvecF, Matrix.sub_apply, Matrix.transpose_apply, matA_entry] at he
      simp only [bestResponse, Matrix.of_apply, Matrix.mul_sub, Matrix.sub_apply]
      linarith
    · have hi : i ∉ S.J j := fun hi => hj ((S.J_symm i j).mpr hi)
      rw [bestResponse_forbidden S P i j hj, bestResponse_forbidden S P j i hi]

end IncentiveFinNet.S01

open Matrix

namespace IncentiveFinNet.S01

variable {n : ℕ} (S : NetworkSetting n)

theorem stable_prices_solution (W P : Matrix (Fin n) (Fin n) ℝ)
    (h : Stable S W P) :
    ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ) := by
  have hchar := (stable_iff_feasible_and_bestResponse S W P).mp h
  apply (bestResponse_symmetric_iff S P hchar.1.2.1
    (fun i j hij => (hchar.1.2.2 i j hij).2)).mp
  simpa only [← hchar.2] using hchar.1.1

theorem stable_of_price_solution (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (hP0 : ∀ i j, j ∉ S.J i → P i j = 0)
    (hsys : ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ)) :
    Stable S (bestResponse S P) P := by
  apply (stable_iff_feasible_and_bestResponse S _ P).mpr
  refine ⟨⟨(bestResponse_symmetric_iff S P hP hP0).mpr hsys, hP, ?_⟩, rfl⟩
  intro i j hij
  refine ⟨?_, hP0 i j hij⟩
  exact bestResponse_column_supported S j P i
    (fun hi => hij ((S.J_symm j i).mp hi))

theorem stable_exists_iff_linear_solvable :
    (∃ W P : Matrix (Fin n) (Fin n) ℝ, Stable S W P) ↔
      uvecF S (matA S - (matA S)ᵀ) ∈ LinearMap.range (ZF S).mulVecLin := by
  constructor
  · rintro ⟨W, P, h⟩
    exact ⟨uvecF S P, stable_prices_solution S W P h⟩
  · rintro ⟨p, hp⟩
    refine ⟨bestResponse S (priceMatrix S p), priceMatrix S p, ?_⟩
    apply stable_of_price_solution S _ (priceMatrix_skew S p) (priceMatrix_forbidden S p)
    simpa only [uvecF_priceMatrix, Matrix.mulVecLin_apply] using hp

theorem stable_unique_of_full_rank
    (hrank : (ZF S).rank = Fintype.card (PermittedPairs S)) :
    ∃! WP : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      Stable S WP.1 WP.2 := by
  have hbij := mulVec_bijective_of_full_rank (ZF S) hrank
  obtain ⟨p, hp⟩ := hbij.2 (uvecF S (matA S - (matA S)ᵀ))
  have hstable : Stable S (bestResponse S (priceMatrix S p)) (priceMatrix S p) := by
    apply stable_of_price_solution S _ (priceMatrix_skew S p) (priceMatrix_forbidden S p)
    simpa only [uvecF_priceMatrix] using hp
  refine ⟨(bestResponse S (priceMatrix S p), priceMatrix S p), hstable, ?_⟩
  intro WP hWP
  have hvec : uvecF S WP.2 = p :=
    hbij.1 ((stable_prices_solution S WP.1 WP.2 hWP).trans hp.symm)
  have hP : WP.2 = priceMatrix S p :=
    price_eq_of_uvecF S WP.2 (priceMatrix S p) hWP.1.2.1 (priceMatrix_skew S p)
      (fun i j hij => (hWP.1.2.2 i j hij).2) (priceMatrix_forbidden S p)
      (hvec.trans (uvecF_priceMatrix S p).symm)
  have hW : WP.1 = bestResponse S (priceMatrix S p) :=
    ((stable_iff_feasible_and_bestResponse S WP.1 WP.2).mp hWP).2.trans
      (congrArg (bestResponse S) hP)
  exact Prod.ext hW hP

end IncentiveFinNet.S01

open IncentiveFinNet

/-- The unchanged complete mission root: existence, the price equations for every
stable pair, and existence and uniqueness of the entire pair under full rank. -/
theorem solution {n : ℕ} (S : NetworkSetting n) : ((∃ W P : Matrix (Fin n) (Fin n) ℝ, Stable S W P) ↔ uvecF S (matA S - (matA S)ᵀ) ∈ LinearMap.range (ZF S).mulVecLin) ∧ (∀ W P : Matrix (Fin n) (Fin n) ℝ, Stable S W P → ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ)) ∧ ((ZF S).rank = Fintype.card (PermittedPairs S) → ∃! WP : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, Stable S WP.1 WP.2) := by
  exact ⟨S01.stable_exists_iff_linear_solvable S, S01.stable_prices_solution S,
    S01.stable_unique_of_full_rank S⟩

#print axioms solution
