-- Prove2me | solution 1 for GlobalTheory.WeierstrassLie.exists_eq_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:32.1659+00:00
-- url     : https://prove2.me/submissions/72a8c583-83e3-44ec-9580-6d4ed6a3cd65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveFst
import Theorems.Thm_GlobalTheory_WeierstrassLie_surjective_fst
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_zero_preimage_coordOpen_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
noncomputable section
open GlobalTheory GlobalTheory.WeierstrassLie
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.WeierstrassLie
theorem _root_.solution (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add, map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm
end GlobalTheory.WeierstrassLie
