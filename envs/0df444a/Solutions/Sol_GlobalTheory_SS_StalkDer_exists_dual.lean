-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:02.145745+00:00
-- url     : https://prove2.me/submissions/a11a5c93-e18f-49eb-9400-7bf4acf05f6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_germ_appLE
import Theorems.Thm_GlobalTheory_SS_StalkDer_extend
import Theorems.Thm_GlobalTheory_SS_StalkDer_gmDual_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
namespace GlobalTheory.SS.StalkDer
theorem _root_.solution {Y : Over (Sp K)} (p : P ⟶ X.left) (q : P ⟶ Y.left)
    (H : IsPullback p q X.hom Y.hom) (D : VF X) (E : VF Y) (z : P) :
    ∃ Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z), (∀ a, (Φ a).fst = a) ∧
      (∀ V hz u, Φ (gm p z V hz u) = gmDual D p z V hz u) ∧
      ∀ V hz u, Φ (gm q z V hz u) = gmDual E q z V hz u := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p z)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hW : IsAffineOpen W := hW
  have hzU : z ∈ p ⁻¹ᵁ U := hzU
  have hzW : z ∈ q ⁻¹ᵁ W := hzW
  have hO : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
    have : IsAffine _ := isAffineOpen_top (Sp K)
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top
    le_top rfl).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have hz : z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W := ⟨hzU, hzW⟩
  have w : X.hom.appLE ⊤ U le_top ≫ CommRingCat.ofHom (gmDual D p z U hzU) =
      Y.hom.appLE ⊤ W le_top ≫ CommRingCat.ofHom (gmDual E q z W hzW) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    refine (gmDual_const D p z U hzU c).trans (Eq.trans ?_ (gmDual_const E q z W hzW c).symm)
    simp only [H.w]
  let φ := po.desc _ _ w
  have h1 : ∀ u, φ.hom ((p.appLE U _ inf_le_left).hom u) = gmDual D p z U hzU u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inl_desc _ _ w)
  have h2 : ∀ u, φ.hom ((q.appLE W _ inf_le_right).hom u) = gmDual E q z W hzW u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inr_desc _ _ w)
  have hf : φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
      (P.presheaf.stalk z)).toRingHom = P.presheaf.germ _ z hz := by
    refine po.hom_ext (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
      (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
    · exact (congrArg TrivSqZeroExt.fst (h1 u)).trans (germ_appLE p z U _ inf_le_left hz u).symm
    · exact (congrArg TrivSqZeroExt.fst (h2 u)).trans (germ_appLE q z W _ inf_le_right hz u).symm
  have hf' : ∀ b, (φ.hom b).fst = (P.presheaf.germ _ z hz).hom b := fun b =>
    congrArg (fun φ => φ.hom b) hf
  letI := P.presheaf.algebra_section_stalk (⟨z, hz⟩ : (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W : P.Opens))
  have loc := hO.isLocalization_stalk ⟨z, hz⟩
  have hu : ∀ s : (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl, IsUnit (φ.hom s) := fun s => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf']
    exact IsLocalization.map_units (P.presheaf.stalk z) s
  let Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z) := IsLocalization.lift hu
  have hΦ : ∀ b, Φ ((P.presheaf.germ _ z hz).hom b) = φ.hom b := fun b =>
    IsLocalization.lift_eq hu b
  refine ⟨Φ, fun a => ?_, extend D p z Φ U hU hzU fun u => ?_, extend E q z Φ W hW hzW fun u => ?_⟩
  · have : (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
        (P.presheaf.stalk z)).toRingHom.comp Φ = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      refine RingHom.ext fun b => ?_
      exact (congrArg TrivSqZeroExt.fst (hΦ b)).trans (hf' b)
    exact congrArg (fun f => f a) this
  · rw [← germ_appLE p z U _ inf_le_left hz, hΦ, h1]
  · rw [← germ_appLE q z W _ inf_le_right hz, hΦ, h2]
end GlobalTheory.SS.StalkDer
