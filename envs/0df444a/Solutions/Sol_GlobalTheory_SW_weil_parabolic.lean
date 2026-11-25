-- Prove2me | solution 1 for GlobalTheory.SW.weil_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:47.456914+00:00
-- url     : https://prove2.me/submissions/7741eb0f-f9ba-4bc2-89e6-cd621c9da81e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Theorems.Thm_GlobalTheory_SW_Parab_exists_den
import Theorems.Thm_GlobalTheory_SW_Parab_isSB_chiH
import Theorems.Thm_GlobalTheory_SW_Parab_blocks
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den
import Theorems.Thm_GlobalTheory_SW_Dict_isSB_comp
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_left_inv
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HAct_mul_mem
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den
import Theorems.Thm_GlobalTheory_SW_TransComp_blocks
import Theorems.Thm_GlobalTheory_SW_transH_comp
import Theorems.Thm_GlobalTheory_SW_weil_action

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Parab
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
end
end GlobalTheory.SW.Parab
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma isUnit_det_diag_blocks_of_lower_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    IsUnit γ.toBlocks₁₁.det ∧ IsUnit γ.toBlocks₂₂.det := by
  have h := (_root_.GlobalTheory.SW.HAct.group_part hγ).1
  have hγ' : γ = fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ 0 γ.toBlocks₂₂ := by
    rw [← h0]
    exact (fromBlocks_toBlocks γ).symm
  rw [hγ', det_fromBlocks_zero₂₁] at h
  exact IsUnit.mul_iff.1 h
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma exists_pos_nat_smul_mul_intM_of_intM {E : Type} [Field E] [NumberField E] {n N : ℕ}
    (M : Matrix (Fin N) (Fin N) E) : ∃ d : ℕ, 0 < d ∧ ∀ x : Matrix (Fin n) (Fin N) E,
      _root_.GlobalTheory.SW.IntM x → _root_.GlobalTheory.SW.IntM (d • (x * M)) := by
  obtain ⟨d, hd, hM⟩ := _root_.GlobalTheory.SW.Dict.exists_den (fun p : Fin N × Fin N => M p.1 p.2)
  refine ⟨d, hd, fun x hx => ?_⟩
  unfold _root_.GlobalTheory.SW.IntM at hx ⊢
  intro k j
  rw [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [← mul_smul_comm]
  exact (hx k i).mul (hM (i, j))
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma isSB_comp_mul_right_of_isUnit_det {E : Type} [Field E] [NumberField E] {n N : ℕ}
    {A : Matrix (Fin N) (Fin N) E} (hA : IsUnit A.det) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (hφ : _root_.GlobalTheory.SW.IsSB φ) : _root_.GlobalTheory.SW.IsSB fun x => φ (x * A) := by
  obtain ⟨d, hd, h1⟩ := exists_pos_nat_smul_mul_intM_of_intM (n := n) A
  obtain ⟨d', hd', h2⟩ := exists_pos_nat_smul_mul_intM_of_intM (n := n) A⁻¹
  let e : Matrix (Fin n) (Fin N) E →+ Matrix (Fin n) (Fin N) E :=
    { toFun := fun x => x * A
      map_zero' := Matrix.zero_mul A
      map_add' := fun x y => Matrix.add_mul x y A }
  refine _root_.GlobalTheory.SW.Dict.isSB_comp e d d' hd hd' h1 (fun x hx => ?_) hφ
  have := h2 _ hx
  change _root_.GlobalTheory.SW.IntM (d' • (x * A * A⁻¹)) at this
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.mul_one] at this
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma ccT_neg_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) E) :
    _root_.GlobalTheory.SW.ccT (-(B * _root_.GlobalTheory.SW.ccT A)) = -(A * _root_.GlobalTheory.SW.ccT B) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply Matrix.map_injective τ.injective
  show (_root_.GlobalTheory.SW.ccT _).map τ = τ.mapMatrix (-(A * _root_.GlobalTheory.SW.ccT B))
  rw [_root_.GlobalTheory.SW.HAct.map_ccT]
  change (τ.mapMatrix (-(B * _root_.GlobalTheory.SW.ccT A)))ᴴ = _
  simp only [map_neg, map_mul, RingHom.mapMatrix_apply, _root_.GlobalTheory.SW.HAct.map_ccT,
    conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma toBlocks₁₁_mul_ccT_toBlocks₁₂_comm_of_mem_UU {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    γ.toBlocks₁₁ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₂ = γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply Matrix.map_injective τ.injective
  change τ.mapMatrix _ = τ.mapMatrix _
  simp only [map_mul, RingHom.mapMatrix_apply, _root_.GlobalTheory.SW.HAct.map_ccT]
  have h := _root_.GlobalTheory.SW.HAct.map_mem τ hγ
  rw [_root_.GlobalTheory.SW.HAct.map_blocks, h0] at h
  obtain ⟨_, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks h
  simp only [Matrix.map_zero _ (map_zero τ), conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    zero_add] at h2 h3
  set A := γ.toBlocks₁₁.map τ
  set B := γ.toBlocks₁₂.map τ
  set D := γ.toBlocks₂₂.map τ
  have hDA' : D * Aᴴ = 1 := mul_eq_one_comm.1 h2
  have hAD' : A * Dᴴ = 1 := mul_eq_one_comm.1 h3
  calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA', Matrix.mul_one]
    _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = A * (Dᴴ * B) * Aᴴ := by rw [h4]
    _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = B * Aᴴ := by rw [hAD', Matrix.one_mul]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N)
    (h0 : γ.toBlocks₂₁ = 0) (τ : E →+* ℂ) :
    (γ.toBlocks₁₁.map τ)ᴴ * γ.toBlocks₂₂.map τ = 1 ∧ (γ.toBlocks₂₂.map τ)ᴴ * γ.toBlocks₁₁.map τ = 1 := by
  have h := _root_.GlobalTheory.SW.HAct.map_mem τ hγ
  rw [_root_.GlobalTheory.SW.HAct.map_blocks, h0] at h
  obtain ⟨_, h2, h3, _⟩ := _root_.GlobalTheory.SW.HAct.blocks h
  simp only [Matrix.map_zero _ (map_zero τ), conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add] at h2 h3
  exact ⟨h2, h3⟩
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma map_trace_mul_mul_ccT_self_eq_sum_dotProduct {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (τ : E →+* ℂ) (x : Matrix (Fin n) (Fin N) E) (β : Matrix (Fin N) (Fin N) E) :
    τ (x * β * _root_.GlobalTheory.SW.ccT x).trace =
      ∑ k, (x.map τ) k ⬝ᵥ (β.map τ) *ᵥ star ((x.map τ) k) := by
  have hc : ∀ a k, τ (_root_.GlobalTheory.SW.ccT x a k) = star (τ (x k a)) := fun a k =>
    congrFun (congrFun (_root_.GlobalTheory.SW.HAct.map_ccT τ x) a) k
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, hc, dotProduct, mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma hermitian_parabolic_exponent_rows_eq {n N : ℕ} (Y z z' : Matrix (Fin n) (Fin N) ℂ) (A B D Z : Matrix (Fin N) (Fin N) ℂ)
    (hAD : Aᴴ * D = 1) (hDA : Dᴴ * A = 1) (k : Fin n) :
    ((Y * Dᴴ) k ⬝ᵥ (-(B * Aᴴ)) *ᵥ star ((Y * Dᴴ) k)) +
      (((Y * Dᴴ) k ⬝ᵥ ((A * Z + B) * D⁻¹) *ᵥ star ((Y * Dᴴ) k)) + (Y * Dᴴ) k ⬝ᵥ (Dᴴ)⁻¹ *ᵥ z k +
        (z' k ᵥ* D⁻¹) ⬝ᵥ star ((Y * Dᴴ) k)) =
      Y k ⬝ᵥ Z *ᵥ star (Y k) + Y k ⬝ᵥ z k + z' k ⬝ᵥ star (Y k) := by
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_left_inv hAD
  have hDHinv : (Dᴴ)⁻¹ = A := Matrix.inv_eq_right_inv hDA
  have hrow : (Y * Dᴴ) k = Y k ᵥ* Dᴴ := rfl
  have hstar : star ((Y * Dᴴ) k) = D *ᵥ star (Y k) := by
    rw [hrow, Matrix.star_vecMul, conjTranspose_conjTranspose]
  rw [hstar, hrow, hDinv, hDHinv]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have e1 : Dᴴ * -(B * Aᴴ) * D = -(Dᴴ * B) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAD, Matrix.mul_one]
  have e2 : Dᴴ * ((A * Z + B) * Aᴴ) * D = Z + Dᴴ * B := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hAD, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, hDA,
      Matrix.one_mul]
  rw [e1, e2, hDA, hAD]
  simp only [Matrix.vecMul_one, Matrix.vecMul_add, Matrix.vecMul_neg, add_dotProduct,
    neg_dotProduct]
  ring
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma transH_chiH_mul_comp_of_toBlocks₂₁_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} {n N : ℕ} {γ : _root_.GlobalTheory.SW.M2 E N}
    (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    _root_.GlobalTheory.SW.TransH Ψ γ φ (fun x => (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
      _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
        φ (x * γ.toBlocks₁₁)) := by
  have hdetA : IsUnit γ.toBlocks₁₁.det := by
    have h := (_root_.GlobalTheory.SW.HAct.group_part hγ).1
    have hγ' : γ = fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ 0 γ.toBlocks₂₂ := by
      rw [← h0]
      exact (fromBlocks_toBlocks γ).symm
    rw [hγ', det_fromBlocks_zero₂₁] at h
    exact (IsUnit.mul_iff.1 h).1
  set A := γ.toBlocks₁₁ with hA
  set B := γ.toBlocks₁₂ with hB
  set D := γ.toBlocks₂₂ with hD
  let e : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    { toFun := fun y => y * A⁻¹
      invFun := fun x => x * A
      left_inv := fun y => by simp only [Matrix.mul_assoc, nonsing_inv_mul _ hdetA, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, mul_nonsing_inv _ hdetA, Matrix.mul_one] }
  have hden : ∀ (Z : _root_.GlobalTheory.SW.CM Ψ N N) (τ : Ψ),
      _root_.GlobalTheory.SW.hDen Ψ γ Z τ = D.map τ := by
    intro Z τ
    unfold _root_.GlobalTheory.SW.hDen
    rw [h0, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_add]
  have hadj : ∀ (Z : _root_.GlobalTheory.SW.CM Ψ N N) (τ : Ψ),
      _root_.GlobalTheory.SW.hDen' Ψ γ Z τ = (D.map τ)ᴴ := by
    intro Z τ
    unfold _root_.GlobalTheory.SW.hDen'
    rw [h0, Matrix.map_zero _ (map_zero _), conjTranspose_zero, Matrix.mul_zero, zero_add]
  have hAinv : ∀ τ : E →+* ℂ, (A⁻¹).map τ = (D.map τ)ᴴ := by
    intro τ
    have h1 : A.map τ * (A⁻¹).map τ = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hdetA, Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [← Matrix.inv_eq_right_inv h1, Matrix.inv_eq_left_inv (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ).2]
  intro Z _ z z'
  unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.hFac
  rw [← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have hyA : e y * A = y := e.left_inv y
  have hkey : _root_.GlobalTheory.SW.chiH Ψ (-(B * _root_.GlobalTheory.SW.ccT A)) (e y) *
      Complex.exp (2 * Real.pi * Complex.I * _root_.GlobalTheory.SW.expo Ψ (e y)
        (_root_.GlobalTheory.SW.hAct Ψ γ Z)
        (fun τ ↦ of fun k ↦ (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
        (fun τ ↦ of fun k ↦ z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹)) =
      Complex.exp (2 * Real.pi * Complex.I * _root_.GlobalTheory.SW.expo Ψ y Z z z') := by
    unfold _root_.GlobalTheory.SW.chiH _root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.hAct
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_trace_mul_mul_ccT_self_eq_sum_dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hey : (e y).map τ.1 = y.map τ.1 * (D.map τ.1)ᴴ := by
      change (y * A⁻¹).map τ.1 = _
      rw [Matrix.map_mul, hAinv]
    have hβ : (-(B * _root_.GlobalTheory.SW.ccT A)).map τ.1 = -(B.map τ.1 * (A.map τ.1)ᴴ) := by
      change τ.1.mapMatrix (-(B * _root_.GlobalTheory.SW.ccT A)) = _
      rw [map_neg, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        _root_.GlobalTheory.SW.HAct.map_ccT]
    simp only [of_apply, hadj, hden]
    have := hermitian_parabolic_exponent_rows_eq (y.map τ.1) (z τ) (z' τ) (A.map τ.1) (B.map τ.1) (D.map τ.1) (Z τ)
      (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ.1).1 (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ.1).2 k
    rw [← hey, ← hβ] at this
    exact this
  rw [← hkey]
  simp only [hden, h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero,
    Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [hyA]
  have hdet : ∀ τ : Ψ, (D.map τ).det = τ.1 D.det := fun τ => by
    rw [RingHom.map_det]
    rfl
  simp only [hdet]
  ring
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma toBlocks₂₁_mul_inv_eq_zero_of_botSpan_eq {E : Type} [Field E] {N : ℕ} {γ γ' : _root_.GlobalTheory.SW.M2 E N}
    (hdet : IsUnit (Matrix.det γ)) (hspan : _root_.GlobalTheory.SW.botSpan γ = _root_.GlobalTheory.SW.botSpan γ') :
    (γ' * γ⁻¹ : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E).toBlocks₂₁ = 0 := by
  ext a j
  have hmem : γ' (Sum.inr a) ∈ _root_.GlobalTheory.SW.botSpan γ := by
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  unfold _root_.GlobalTheory.SW.botSpan at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hid : ∀ b, ∑ m, γ (Sum.inr b) m * γ⁻¹ m (Sum.inl j) = 0 := by
    intro b
    have := congrFun (congrFun (mul_nonsing_inv (γ : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E) hdet) (Sum.inr b)) (Sum.inl j)
    rw [Matrix.mul_apply] at this
    rw [this]
    simp
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, Matrix.mul_apply, ← hc, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hid, mul_zero, Finset.sum_const_zero]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma hFac_eq_prod_det_pow_of_toBlocks₂₁_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} {n N : ℕ} {γ : _root_.GlobalTheory.SW.M2 E N} (h0 : γ.toBlocks₂₁ = 0)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (z z' : _root_.GlobalTheory.SW.CM Ψ n N) :
    _root_.GlobalTheory.SW.hFac Ψ γ Z z z' = ∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n := by
  unfold _root_.GlobalTheory.SW.hFac _root_.GlobalTheory.SW.hDen
  simp only [h0, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_add, Matrix.mul_zero, Matrix.zero_mulVec,
    dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  rfl
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ → (∀ γ ∈ _root_.GlobalTheory.SW.UU E N, γ.toBlocks₂₁ = 0 → ∀ x, _root_.GlobalTheory.SW.weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ _root_.GlobalTheory.SW.UU E N, ∀ γ' ∈ _root_.GlobalTheory.SW.UU E N, _root_.GlobalTheory.SW.botSpan γ = _root_.GlobalTheory.SW.botSpan γ' → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z', _root_.GlobalTheory.SW.eisTerm Ψ γ φ Z z z' = _root_.GlobalTheory.SW.eisTerm Ψ γ' φ Z z z' := by
  intro E _ _ _ Ψ hΨ n N hn φ hφ
  have hpar : ∀ γ ∈ _root_.GlobalTheory.SW.UU E N, γ.toBlocks₂₁ = 0 →
      ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ → ∀ x,
        _root_.GlobalTheory.SW.weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
          _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
            φ (x * γ.toBlocks₁₁) := by
    intro γ hγ h0 φ hφ x
    have hA := (isUnit_det_diag_blocks_of_lower_zero hγ h0).1
    have hSB : _root_.GlobalTheory.SW.IsSB fun x => (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
        _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
          φ (x * γ.toBlocks₁₁) := by
      refine _root_.GlobalTheory.SW.Parab.isSB_chiH hΨ ?_ _
        (isSB_comp_mul_right_of_isUnit_det hA hφ)
      rw [ccT_neg_mul_ccT, toBlocks₁₁_mul_ccT_toBlocks₁₂_comm_of_mem_UU hγ h0]
    have := (_root_.GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hφ).2.2.1 _ hSB
      (transH_chiH_mul_comp_of_toBlocks₂₁_eq_zero hγ h0 φ)
    exact (congrFun this x).symm
  refine ⟨fun γ hγ h0 x => hpar γ hγ h0 φ hφ x, ?_⟩
  intro γ hγ γ' hγ' hspan Z hZ z z'
  have hprops := _root_.GlobalTheory.SW.HAct.group_part hγ
  set p := γ' * γ⁻¹ with hp
  have hpU : p ∈ _root_.GlobalTheory.SW.UU E N := _root_.GlobalTheory.SW.HAct.mul_mem hprops.2.1 hγ'
  have hp0 : p.toBlocks₂₁ = 0 := toBlocks₂₁_mul_inv_eq_zero_of_botSpan_eq hprops.1 hspan
  have hγ'eq : γ' = p * γ := by
    rw [hp, Matrix.mul_assoc, nonsing_inv_mul _ hprops.1, Matrix.mul_one]
  have htest := _root_.GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hφ
  have hcomp := htest.2.2.2.2.2.1 p hpU
  have hcoc := (_root_.GlobalTheory.SW.transH_comp E Ψ n N γ p hγ hpU).1 Z hZ z z'
  have hD := (isUnit_det_diag_blocks_of_lower_zero hpU hp0).2
  have hc : (∏ τ : Ψ, τ.1 p.toBlocks₂₂.det ^ n) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro τ _
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hD.ne_zero)
  have hchi : _root_.GlobalTheory.SW.chiH Ψ (-(p.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT p.toBlocks₁₁))
      (0 : Matrix (Fin n) (Fin N) E) = 1 := by
    unfold _root_.GlobalTheory.SW.chiH
    simp
  unfold _root_.GlobalTheory.SW.eisTerm
  rw [hγ'eq, hcomp, hpar p hpU hp0 _ htest.1, hcoc, hFac_eq_prod_det_pow_of_toBlocks₂₁_eq_zero hp0, hchi,
    Matrix.zero_mul, mul_inv, mul_one]
  field_simp
end _root_.GlobalTheory.SW
