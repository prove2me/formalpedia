-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.det_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:36.544081+00:00
-- url     : https://prove2.me/submissions/7e3169e8-c61c-4d04-a515-c754d45b6481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_form_bound_field
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U)
    (hσ : ∀ x : K, σ (star x) = star (σ x)) (herm : ∀ x y : U, star (h x y) = h y x)
    (hpos : ∀ w : U, w ≠ 0 → 0 < (σ (h w w)).re) (hη : ∀ x y : U, h (η x) (η y) = h x y) :
    ‖σ (LinearMap.det (LinearMap.id - η))‖ ≤ 2 ^ Module.finrank K U := by
  let u := Module.finBasis K U
  have hb := Formalism.HermitianLatticeCounting.P.det_form_bound_field K U σ h η hσ herm hpos hη _ u u
  set G : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K :=
    Matrix.of fun a b => h (u a) (u b) with hG
  set A := LinearMap.toMatrix u u (LinearMap.id - η) with hA
  have e : (Matrix.of fun a b => bEta h η (u a) (u b)) = G * (A.conjTranspose).transpose := by
    ext a b
    have h1 : u b - η (u b) = ∑ c, A c b • u c := by
      simp only [hA, LinearMap.toMatrix_apply]
      exact (u.sum_repr _).symm
    simp only [bEta, Matrix.of_apply, h1, map_sum, map_smulₛₗ, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, hG, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]; rfl
  have hG0 : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have h1 : ∀ b, h (∑ a, v a • u a) (u b) = 0 := by
      intro b
      have := congrFun hvG b
      simpa [Matrix.vecMul, dotProduct, hG, map_sum] using this
    have h2 : h (∑ a, v a • u a) = 0 := u.ext fun b => h1 b
    have h3 : (∑ a, v a • u a) = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [h2] at this
      simp at this
    exact hv (funext (Fintype.linearIndependent_iff.1 u.linearIndependent v h3))
  have hp : 0 < ‖σ G.det‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hG0)
  rw [e, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose, map_mul, norm_mul, hσ, norm_star,
    mul_assoc, Real.mul_self_sqrt hp.le, hA, LinearMap.det_toMatrix, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hp
end GlobalTheory.DegCnt.FixDisc
