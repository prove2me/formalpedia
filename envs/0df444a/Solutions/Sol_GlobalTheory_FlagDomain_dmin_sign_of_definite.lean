-- Prove2me | solution 1 for GlobalTheory.FlagDomain.dmin_sign_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:35.086053+00:00
-- url     : https://prove2.me/submissions/0edd5f72-1dcb-405b-a8cc-41d1848e1d20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
import Theorems.Thm_GlobalTheory_FlagDomain_gram_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder ComplexConjugate Matrix
open GlobalTheory GlobalTheory.FlagDomain
namespace GlobalTheory.FlagDomain
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (i : Fin (r + 1)) :
    0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  obtain ⟨ε, hε, hsgn⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∀ a : ℕ, a < r → sgn X.p0 a = ε := by
    rcases h with h | h
    · exact ⟨-1, by norm_num, fun a _ => by simp [sgn, h]⟩
    · exact ⟨1, by norm_num, fun a ha => by simp [sgn, h, ha]⟩
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hps : psgn X.p0 i = ε ^ (i : ℕ) := by
    unfold psgn
    rw [Finset.prod_congr rfl (g := fun _ => ε), Finset.prod_const, Finset.card_range]
    intro a ha
    exact hsgn a (lt_of_lt_of_le (Finset.mem_range.1 ha) hi)
  obtain ⟨P, hPdet, hP⟩ := X.signature τ
  set M := mat x τ with hM
  set Q := P⁻¹ * M with hQ
  have hPQ : P * Q = M := Matrix.mul_nonsing_inv_cancel_left P M (isUnit_iff_ne_zero.2 hPdet)
  have hQdet : Q.det ≠ 0 := by
    intro h0
    apply hx
    rw [← hPQ, Matrix.det_mul, h0, mul_zero]
  set N := Q.map (starRingEnd ℂ) with hN
  have hNdet : N.det ≠ 0 := by
    rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hQdet
  have hNinj : Function.Injective N.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hNdet))
  have hH : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hNinj
  have hNt : Nᴴ = Qᵀ := by
    ext a b
    simp [hN, Matrix.conjTranspose_apply]
  have hdiag : Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = (ε : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    rw [hsgn a a.isLt]
  have hgram : gram τ.1 X.Gm M = (ε : ℂ) • (Nᴴ * N) := by
    rw [← hPQ, GlobalTheory.FlagDomain.gram_mul, hP, hdiag, hNt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  set e := Fin.castLE hi with he
  have hsub : ((Nᴴ * N).submatrix e e).PosDef := hH.submatrix (Fin.castLE_injective hi)
  have hdpos := Complex.pos_iff.1 hsub.det_pos
  have hd : dmin X.Gm x τ i = ((ε ^ (i : ℕ) : ℝ) : ℂ) * ((Nᴴ * N).submatrix e e).det := by
    simp only [dmin, lminor]
    have hs : ((ε : ℂ) • (Nᴴ * N)).submatrix e e = (ε : ℂ) • ((Nᴴ * N).submatrix e e) := by
      ext a b
      simp
    rw [← hM, hgram, ← he, hs, Matrix.det_smul, Fintype.card_fin]
    push_cast
    rfl
  rw [hd, Complex.re_ofReal_mul, hps, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, hε, one_pow,
    one_mul]
  exact hdpos.1
end GlobalTheory.FlagDomain
