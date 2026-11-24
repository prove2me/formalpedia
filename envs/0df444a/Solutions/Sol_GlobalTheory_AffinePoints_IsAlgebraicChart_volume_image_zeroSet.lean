-- Prove2me | solution 1 for GlobalTheory.AffinePoints.IsAlgebraicChart.volume_image_zeroSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:34.822054+00:00
-- url     : https://prove2.me/submissions/f9d0cd35-bc72-4896-98a4-85c763d9e799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_volume_coords_image_zeroSet
import Theorems.Thm_GlobalTheory_AffinePoints_aeval_coords
import Theorems.Thm_GlobalTheory_AffinePoints_apply_eq_div_of_mul_eq
import Theorems.Thm_GlobalTheory_AffinePoints_range_comap_away
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_of_ne_zero_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
namespace GlobalTheory.AffinePoints
namespace IsAlgebraicChart
theorem _root_.solution [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) {e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ)}
    (he : IsAlgebraicChart e) {f : A} (hf : f ≠ 0) :
    volume (e '' (e.source ∩ {p | p f = 0})) = 0 := by
  obtain ⟨x, s, hx⟩ := he.exists_eq_div
  by_cases hs : s = 0
  · have : e.source = ∅ := eq_empty_of_forall_notMem fun p hp => (hx p hp).1 (by simp [hs])
    simp [this]
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  let B := Localization.Away s
  haveI : IsDomain B := IsLocalization.isDomain_localization hs0
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective _ hs0
  let g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B :=
    aeval fun i => algebraMap A B (x i) * IsLocalization.Away.invSelf s
  have hsub : e '' (e.source ∩ {p | p f = 0}) ⊆
      coords g '' {q : B →ₐ[ℂ] ℂ | q (algebraMap A B f) = 0} := by
    rintro _ ⟨p, ⟨hp, hpf⟩, rfl⟩
    obtain ⟨q, rfl⟩ : p ∈ range (comap (IsScalarTower.toAlgHom ℂ A B)) := by
      rw [range_comap_away s]; exact (hx p hp).1
    refine ⟨q, hpf, funext fun i => ?_⟩
    rw [(hx _ hp).2 i]
    refine apply_eq_div_of_mul_eq q (IsLocalization.Away.algebraMap_isUnit s) ?_
    simp only [g, aeval_X]
    rw [mul_assoc, mul_comm _ (algebraMap A B s), IsLocalization.Away.mul_invSelf, mul_one]
  refine measure_mono_null hsub ?_
  by_cases hinj : Function.Injective g
  · refine volume_coords_image_zeroSet g ?_ ((map_ne_zero_iff _ hAB).2 hf)
    letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
    haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B :=
      IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
    haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) B :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hAB
    haveI : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic _ (Submonoid.powers s)
    obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq ℂ A
    rw [hd] at h1
    obtain rfl : d = n := by exact_mod_cast h1
    have h3 := trdeg_add_eq ℂ (MvPolynomial (Fin d) ℂ) (A := B)
    rw [trdeg_eq_of_isAlgebraic_top ℂ A B, h2, MvPolynomial.trdeg_of_isDomain] at h3
    simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast] at h3
    have h4 : Algebra.trdeg (MvPolynomial (Fin d) ℂ) B = 0 :=
      Cardinal.eq_of_add_eq_add_left (h3.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
    exact trdeg_eq_zero_iff.1 h4
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨r, hr0, hr⟩ := hinj
    refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
    rintro _ ⟨p, -, rfl⟩
    have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    rw [h1, hr0, map_zero]
end IsAlgebraicChart
end GlobalTheory.AffinePoints
