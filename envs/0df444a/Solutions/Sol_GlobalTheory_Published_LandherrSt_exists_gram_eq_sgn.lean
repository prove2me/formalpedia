-- Prove2me | solution 1 for GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:20.055155+00:00
-- url     : https://prove2.me/submissions/1549fd31-d567-42a3-bcb0-5a420614cdd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Theorems.Thm_GlobalTheory_Published_embedding_cc
import Theorems.Thm_GlobalTheory_Published_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end LandherrSt
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma eq_zero_iff_lt_card_filter_eq_zero_of_monotone {r : ℕ} (g : Fin r → ℕ) (hg : Monotone g) (a : Fin r) :
    g a = 0 ↔ (a : ℕ) < (Finset.univ.filter fun b => g b = 0).card := by
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ Finset.univ.filter fun b => g b = 0 := by
      intro b hb
      simp only [Finset.mem_Iic] at hb
      simpa using Nat.le_zero.1 (ha ▸ hg hb)
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at this
    omega
  · intro ha
    by_contra hne
    have hsub : (Finset.univ.filter fun b => g b = 0) ⊆ Finset.Iio a := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_Iio]
      by_contra hab
      exact hne (Nat.le_zero.1 (hb ▸ hg (not_lt.1 hab)))
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at this
    omega
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma inv_sqrt_abs_mul_self_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    (Real.sqrt |x|)⁻¹ * x * (Real.sqrt |x|)⁻¹ = if 0 < x then 1 else -1 := by
  have hpos : 0 < |x| := abs_pos.2 hx
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |x| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [mul_comm, ← mul_assoc, ← mul_inv, hs]
  split_ifs with h
  · rw [abs_of_pos h]; field_simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hx)]; field_simp
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma exists_conjTranspose_mul_mul_eq_sgn_diagonal {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ (p : ℕ) (M : Matrix (Fin r) (Fin r) ℂ),
      Mᴴ * A * M = diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  set U : Matrix (Fin r) (Fin r) ℂ := (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hU
  set ev := hA.eigenvalues with hev
  have hspec : Uᴴ * A * U = diagonal (Complex.ofReal ∘ ev) := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, ← star_eq_conjTranspose] using this
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hev, h])
  set g : Fin r → ℕ := fun i => if 0 < ev i then 0 else 1 with hg
  set σ := Tuple.sort g
  have hmono : Monotone (g ∘ σ) := Tuple.monotone_sort g
  refine ⟨(Finset.univ.filter fun b => (g ∘ σ) b = 0).card,
    (U * diagonal fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)).submatrix id σ, ?_⟩
  rw [conjTranspose_submatrix, ← submatrix_id_id A, ← Equiv.coe_refl,
    submatrix_mul_equiv, submatrix_mul_equiv, conjTranspose_mul, diagonal_conjTranspose]
  rw [show ∀ X Y Z : Matrix (Fin r) (Fin r) ℂ, X * Uᴴ * Y * (U * Z) = X * (Uᴴ * Y * U) * Z by
    intro X Y Z; simp only [Matrix.mul_assoc], hspec, diagonal_mul_diagonal, diagonal_mul_diagonal,
    submatrix_diagonal_equiv]
  congr 1
  ext a
  have key := eq_zero_iff_lt_card_filter_eq_zero_of_monotone _ hmono a
  have hsq := inv_sqrt_abs_mul_self_mul_inv_sqrt_abs_eq_sign (ev (σ a)) (hne _)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  simp only [Function.comp_apply, hg] at key ⊢
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsq]
  by_cases h : 0 < ev (σ a)
  · simp only [h, if_true, true_iff] at key ⊢
    rw [if_pos key]
  · simp only [h, if_false, one_ne_zero, false_iff] at key ⊢
    rw [if_neg key]
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma sgn_ne_zero_published_landherr (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num
end LandherrSt
end GlobalTheory.Published
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Published.LandherrSt
namespace _root_.GlobalTheory.Published.LandherrSt
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) (hd : G.det ≠ 0) (τ : E →+* ℂ) :
    ∃ (p : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ), Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  have hA : (G.map τ).IsHermitian := by
    ext i j
    simp [conjTranspose_apply, ← _root_.GlobalTheory.Published.embedding_cc, hG]
  have hAd : (G.map τ).det ≠ 0 := by
    have h := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero τ).2 hd
  obtain ⟨p, M, hM⟩ := exists_conjTranspose_mul_mul_eq_sgn_diagonal _ hA hAd
  have hg : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M.map (starRingEnd ℂ)) =
      diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    rw [_root_.GlobalTheory.Published.gram_eq, show (M.map (starRingEnd ℂ))ᵀ = Mᴴ from rfl]
    convert hM using 2
    ext i j
    simp
  refine ⟨p, M.map (starRingEnd ℂ), ?_, hg⟩
  intro h0
  have h := congrArg det hg
  rw [_root_.GlobalTheory.Published.gram_eq, det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul,
    det_diagonal] at h
  refine absurd h.symm (Finset.prod_ne_zero_iff.2 ?_)
  intro a _
  exact Complex.ofReal_ne_zero.2 (sgn_ne_zero_published_landherr p (a : ℕ))
end _root_.GlobalTheory.Published.LandherrSt
end GlobalTheory.Published.LandherrSt
