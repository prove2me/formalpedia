-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_etale_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:46.365802+00:00
-- url     : https://prove2.me/submissions/9988e82f-f4a6-4046-804e-b685d323efd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_SS_Ord_model_smoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
namespace GlobalTheory.SS.Ord
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (I : Type) [Fintype I], SmoothOfRelativeDimension (Fintype.card I) A.hom → ∀ (M : Model R A) (x : M.Y.left) (O : M.Y.left.Opens), x ∈ O → ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ O ∧ (MvPolynomial.eval₂Hom (cst M U) t).Etale := by
  intro R K _ _ _ _ _ _ A I _ hA M x O hx
  have hM := model_smoothOfRelativeDimension hA M
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)
  have h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I) := by
    have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
    have e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W) :=
      RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm
    rw [e]
    exact h3
  obtain ⟨φ, hC, hφ⟩ := h2.exists_etale_mvPolynomial
  let e := Fintype.equivFin I
  refine ⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg,
    (M.Y.left.basicOpen_le g).trans hWO, ?_⟩
  have h4 := RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ
  convert h4 using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [← hC]
  · simp
end GlobalTheory.SS.Ord
