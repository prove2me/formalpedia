-- Prove2me | solution 1 for GlobalTheory.isOrth_rmul_iff_unitary_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:56.203086+00:00
-- url     : https://prove2.me/submissions/c836508b-1e47-4ad2-a175-58252820b3c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UpperTriangularPreservesDiagonalIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped Matrix in
private theorem gram_mul_eq_transpose_mul_gram_mul_conj {F : Type} [Field F] {r : ℕ} (τ : F →+* ℂ)
    (G : Matrix (Fin r) (Fin r) F) (A g : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (A * g) = gᵀ * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G A * g.map (starRingEnd ℂ) := by
  simp only [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
    Matrix.mul_assoc]
open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℂ} (d : Fin r → ℂ) (hdiag : ∀ a c, c ≠ a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) =
      Matrix.diagonal fun a => ((Complex.normSq (B a a) : ℝ) : ℂ) * d a := by
  have hBd : B = Matrix.diagonal fun a => B a a := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j (Ne.symm hij)]
  rw [hBd]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  congr 1
  funext a
  rw [← Complex.mul_conj]
  ring
open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_eq_diagonal_iff {r : ℕ} {B : Matrix (Fin r) (Fin r) ℂ}
    {d : Fin r → ℂ} (hd : ∀ a, d a ≠ 0) (hdet : B.det ≠ 0) (hup : ∀ a c, c < a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) = Matrix.diagonal d ↔
      ∀ a, ‖B a a‖ = 1 ∧ ∀ c, c ≠ a → B a c = 0 := by
  constructor
  · intro h
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
    have htri : B.BlockTriangular id := fun i j hij => hup i j hij
    letI := B.invertibleOfIsUnitDet hunit
    have hinv : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular htri
    have h2 : Matrix.diagonal d * B.map (starRingEnd ℂ) = (B⁻¹)ᵀ * Matrix.diagonal d := by
      have h3 : (B⁻¹)ᵀ * (Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ)) =
          (B⁻¹)ᵀ * Matrix.diagonal d := by rw [h]
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
        Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one, Matrix.one_mul] at h3
    have hoff : ∀ a c, a < c → B a c = 0 := by
      intro a c hac
      have h4 := congrFun (congrFun h2 a) c
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hinv hac, zero_mul,
        Matrix.map_apply] at h4
      have h5 := (mul_eq_zero.1 h4).resolve_left (hd a)
      simpa using h5
    have hdiag : ∀ a c, c ≠ a → B a c = 0 := by
      intro a c hca
      rcases lt_or_gt_of_ne hca with hlt | hlt
      · exact hup a c hlt
      · exact hoff a c hlt
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d hdiag] at h
    intro a
    refine ⟨?_, hdiag a⟩
    have h6 := congrFun (congrFun h a) a
    simp only [Matrix.diagonal_apply_eq] at h6
    have h7 : ((Complex.normSq (B a a) : ℝ) : ℂ) = 1 :=
      mul_right_cancel₀ (hd a) (h6.trans (one_mul _).symm)
    have h8 : ‖B a a‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast h7
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h8
  · intro h
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d fun a c hca => (h a).2 c hca]
    congr 1
    funext a
    rw [Complex.normSq_eq_norm_sq, (h a).1]
    simp
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r →
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ↔ ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0)) := by
  intro r X x b hx hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  simp only [Set.mem_setOf_eq] at hb
  have hd : ∀ a : Fin r, ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hprod : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := fun τ => rfl
  constructor
  · intro h τ
    have key := h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ] at key
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).1 key
  · intro h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).2 (h τ)
end _root_.GlobalTheory
end GlobalTheory
