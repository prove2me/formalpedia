-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:39.140512+00:00
-- url     : https://prove2.me/submissions/5cfb1c0d-4df8-44f6-8539-49d692c8fa6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_fin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution [FiniteDimensional K V] (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hp : PD h) : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      star (Matrix.of fun i l => h (b i) (b l)).det = (Matrix.of fun i l => h (b i) (b l)).det ∧
      ∀ τ : K →+* ℂ, 0 < (τ (Matrix.of fun i l => h (b i) (b l)).det).re := by
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (c := starRingEnd K) two_ne_zero _
    h.flip (fun x y => hs.eq y x) rfl
  have e : (Matrix.of fun i l => h (b i) (b l)) = Matrix.diagonal fun i => h (b i) (b i) := by
    ext i l
    by_cases hil : i = l
    · subst hil; simp
    · rw [Matrix.diagonal_apply_ne _ hil]; exact hb l i (Ne.symm hil)
  refine ⟨b, ?_⟩
  rw [e, Matrix.det_diagonal]
  refine Finset.prod_induction _ (fun d : K => star d = d ∧ ∀ τ : K →+* ℂ, 0 < (τ d).re) ?_ ?_ ?_
  · rintro x y ⟨x1, x2⟩ ⟨y1, y2⟩
    refine ⟨by rw [star_mul', x1, y1], fun τ => ?_⟩
    have : (τ x).im = 0 := Complex.conj_eq_iff_im.1 (by rw [← hK.2.1, x1])
    rw [map_mul, Complex.mul_re, this, zero_mul, sub_zero]
    exact mul_pos (x2 τ) (y2 τ)
  · simp
  · intro i _
    exact ⟨hs.eq _ _, fun τ => hp τ _ (b.ne_zero i)⟩
end GlobalTheory.Mass.SameBad
