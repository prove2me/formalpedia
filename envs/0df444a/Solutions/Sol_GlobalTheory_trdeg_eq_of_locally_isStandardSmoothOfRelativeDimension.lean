-- Prove2me | solution 1 for GlobalTheory.trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:53.200836+00:00
-- url     : https://prove2.me/submissions/96bce7ac-6000-4c34-a7c2-c1665506b449

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Theorems.Thm_GlobalTheory_AffinePoints_ringKrullDim_eq_of_isStandardSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra! hz
    have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hz
    exact top_ne_bot (hs.symm.trans hbot)
  have hPt := hP t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hPt
  have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  have : Algebra.IsStandardSmooth K (Localization.Away t) := hPt.isStandardSmooth
  have hdim : ringKrullDim (Localization.Away t) = g :=
    AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := K)
  obtain ⟨d, hd1, hd2⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (Localization.Away t)
  have hdg : d = g := by
    rw [hdim] at hd1
    exact_mod_cast hd1.symm
  have : FaithfulSMul B (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic B (Localization.Away t) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers t)
  have : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K B).injective
  rw [← trdeg_eq_of_isAlgebraic_top K B (Localization.Away t), hd2, hdg]
end GlobalTheory
