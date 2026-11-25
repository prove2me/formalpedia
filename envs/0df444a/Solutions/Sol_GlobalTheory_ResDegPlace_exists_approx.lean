-- Prove2me | solution 1 for GlobalTheory.ResDegPlace.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:57.987798+00:00
-- url     : https://prove2.me/submissions/d462f042-3157-463a-a9b6-170e4be5a5a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField
import Theorems.Thm_GlobalTheory_ResDegPlace_ord_pos_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_nonneg_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_addVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing
variable {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}
namespace GlobalTheory.ResDegPlace
theorem _root_.solution (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : A) (hx : 0 ≤ ord ϖ ζ x) :
    ∃ a : As O A, 0 < ord ϖ ζ ((a : A) - x) := by
  obtain ⟨n, hn⟩ := h.denom x
  have h1 := hx
  rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
    IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
  obtain ⟨c, hc⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
  have h2 : algebraMap (As O A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As O A)) =
      algebraMap (As O A) (Loc ζ) (algebraMap O (As O A) ϖ ^ n * b) := by
    rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 : (algebraMap O A ϖ) ^ n * ((((t : As O A) : A) * ((s : As O A) : A)) * x) =
      (algebraMap O A ϖ) ^ n * (((t : As O A) : A) * (b : A)) := by
    have := congrArg Subtype.val ht
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
    have e : ((algebraMap O (As O A) ϖ : As O A) : A) = algebraMap O A ϖ := rfl
    rw [e] at this
    linear_combination this
  have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
  obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
  refine ⟨d * (t * b), ?_⟩
  have h5 : ((d * (t * b) : As O A) : A) - x = ((-i : As O A) : A) * x := by
    have := congrArg Subtype.val hdi
    simp only [Submonoid.coe_mul, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
      NegMemClass.coe_neg] at this ⊢
    linear_combination x * this - (d : A) * h4
  rw [h5, ord_mul ζ h]
  exact add_pos_of_pos_of_nonneg ((ord_pos_iff h ζ _).2 (ζ.asIdeal.neg_mem hi)) hx
end GlobalTheory.ResDegPlace
