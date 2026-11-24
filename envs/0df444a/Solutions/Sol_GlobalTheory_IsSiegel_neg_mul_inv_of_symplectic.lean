-- Prove2me | solution 1 for GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:18.256703+00:00
-- url     : https://prove2.me/submissions/e59f6089-2b54-4661-9f23-06793ac3c833

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSiegelUpperHalfSpaceNegMulInvSymplectic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (hdet : P.det ≠ 0) (hsym : (-(Q * P⁻¹)).IsSymm) :
    GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  refine ⟨hsym, ?_⟩
  set A : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) with hA
  set B : Matrix l l ℂ := fun a b => (s (.inl a) (.inr b) : ℂ) with hB
  set C : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) with hC
  set D : Matrix l l ℂ := fun a b => (s (.inr a) (.inr b) : ℂ) with hD
  have hPe : P = A - I • B := by ext a b; simp only [hP]; rfl
  have hQe : Q = C - I • D := by ext a b; simp only [hQ]; rfl
  have hsc : s.map (Complex.ofRealHom : ℝ →+* ℂ) = fromBlocks A B C D := by
    ext (a|a) (b|b) <;> rfl
  have hJ : (J l ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) = J l ℂ := by
    ext (a|a) (b|b) <;> simp [J, one_apply] <;> split_ifs <;> simp
  have hc : (fromBlocks A B C D)ᵀ * J l ℂ * fromBlocks A B C D = J l ℂ := by
    have h1 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (SymplecticGroup.mem_iff'.mp hs)
    simp only [Matrix.map_mul, transpose_map, hJ, hsc] at h1
    exact h1
  rw [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  obtain ⟨h11, h12, h21, h22⟩ := hc
  simp at h11 h12 h21 h22
  have star_real : ∀ X : Matrix l l ℂ, (∀ a b, star (X a b) = X a b) → Xᴴ = Xᵀ := by
    intro X hX; ext a b; simp [conjTranspose_apply, hX]
  have hAs : Aᴴ = Aᵀ := star_real A (fun a b => by simp [A])
  have hBs : Bᴴ = Bᵀ := star_real B (fun a b => by simp [B])
  have hCs : Cᴴ = Cᵀ := star_real C (fun a b => by simp [C])
  have hDs : Dᴴ = Dᵀ := star_real D (fun a b => by simp [D])
  have key : Pᴴ * Q - Qᴴ * P = -(2 * I) • (1 : Matrix l l ℂ) := by
    rw [hPe, hQe]
    simp only [conjTranspose_sub, conjTranspose_smul, hAs, hBs, hCs, hDs, Complex.star_def, conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -h11 - h22 + I • h12 - I • h21
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := -(Q * P⁻¹) with hτ
  have hτP : τ * P = -Q := by rw [hτ, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsymm : ∀ a b, τ b a = τ a b := fun a b => by
    have := congrFun (congrFun hsym a) b
    simpa [transpose_apply] using this
  set M : Matrix l l ℝ := τ.map im with hM
  set Mc : Matrix l l ℂ := M.map (Complex.ofRealHom : ℝ →+* ℂ) with hMc
  have hdiff : τ - τᴴ = (2 * I) • Mc := by
    ext a b
    simp only [Matrix.sub_apply, conjTranspose_apply, hsymm a b, Matrix.smul_apply, smul_eq_mul, Mc, M, map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hQP : Pᴴ * τᴴ = -Qᴴ := by rw [← conjTranspose_mul, hτP, conjTranspose_neg]
  have h2 : Pᴴ * Mc * P = 1 := by
    have e : Pᴴ * (τ - τᴴ) * P = (2 * I) • (1 : Matrix l l ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hτP, hQP]
      rw [Matrix.mul_neg, Matrix.neg_mul]
      linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -key
    rw [hdiff, Matrix.mul_smul, Matrix.smul_mul] at e
    exact smul_right_injective _ (by simp [I_ne_zero] : (2 * I) ≠ 0) e
  have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hu, conjTranspose_one]
  have e2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hu
  have hMcf : Mc = (P⁻¹)ᴴ * P⁻¹ := by
    calc Mc = ((P⁻¹)ᴴ * Pᴴ) * Mc * (P * P⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * Mc * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h2, Matrix.mul_one]
  have hinj : Function.Injective (P⁻¹).mulVec := by
    intro u v h
    have := congrArg P.mulVec h
    simpa [mulVec_mulVec, e2] using this
  have hpd : Mc.PosDef := hMcf ▸ PosDef.conjTranspose_mul_self _ hinj
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp [conjTranspose_apply, M, hsymm a b]
  · intro x hx
    set xc : l → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h; apply hx; ext i
      have := congrFun h i
      simpa [xc] using this
    have e : star xc ⬝ᵥ Mc *ᵥ xc = ((star x ⬝ᵥ M *ᵥ x : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Mc, xc, Complex.ofReal_sum, Complex.ofReal_mul]
    have := hpd.dotProduct_mulVec_pos hxc0
    rw [e] at this
    exact zero_lt_real.mp this
end IsSiegel
end GlobalTheory
