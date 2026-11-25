-- Prove2me | solution 1 for GlobalTheory.SecSpread.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:19.949329+00:00
-- url     : https://prove2.me/submissions/1b8ef29e-69f7-484e-87b9-fdc066804405

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_isUnit_cst
import Theorems.Thm_GlobalTheory_SecSpread_exists_spread
import Theorems.Thm_GlobalTheory_SecSpread_res_mem_secOn
import Theorems.Thm_GlobalTheory_isReduced_scheme_of_smooth_of_isIntegrallyClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left), L.IsLB → ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G' : Scheme.{0}) (φ : G' ⟶ G.left) (π : G' ⟶ Sp K), IsPullback φ π G.hom (spMap (algebraMap R K)) → (∃ (s : (L.pull φ).Sec) (j : (L.pull φ).ι), s.f j ≠ 0) → ∃ h : R, h ≠ 0 ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h), ∀ y : Sp R, y ∈ PrimeSpectrum.basicOpen h → ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  intro R _ _ G _ hG L hL K _ _ _ G' φ π H ⟨s, j, hj⟩
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨d, hd, θ, hθ⟩ := exists_spread H hL s
  have : Smooth π := MorphismProperty.of_isPullback H hG.smooth
  have : IsReduced G' := isReduced_scheme_of_smooth_of_isIntegrallyClosed K π
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j PUnit.unit, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∈ G'.basicOpen (s.f (fun _ => i)) := by
    by_contra hn
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim))
  have hz₁ : z ∈ (L.pull φ).U (fun _ => i) := G'.basicOpen_le _ hz
  have hz₂ : φ z ∈ L.U i := mem_pull.1 hz₁
  have hu : IsUnit (gs φ z (L.U i) (θ.f i)) := by
    rw [hθ i z hz₂]
    refine (isUnit_cst H.w z hd).mul ?_
    rw [gs_eq (𝟙 G') z _ hz₁]
    exact (G'.mem_basicOpen _ z hz₁).1 hz
  have hb : φ z ∈ G.left.basicOpen (θ.f i) := by
    rw [gs_eq φ z _ hz₂] at hu
    have := (G'.mem_basicOpen _ z (show z ∈ φ ⁻¹ᵁ L.U i from hz₂)).2 hu
    rw [← Scheme.preimage_basicOpen] at this
    exact this
  have hopen : IsOpen (G.hom '' (G.left.basicOpen (θ.f i) : Set G.left)) :=
    G.hom.isOpenMap _ (G.left.basicOpen (θ.f i)).isOpen
  obtain ⟨_, ⟨h, rfl⟩, hyh, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem G.hom hb) hopen
  refine ⟨h, ?_, _, res_mem_secOn θ _, fun y hy => ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hyh (Ideal.zero_mem _)
  · obtain ⟨g, hg, rfl⟩ := hsub hy
    refine ⟨g, i, rfl, ?_⟩
    have e := G.left.basicOpen_res (θ.f i)
      (homOfLE (inf_le_right : G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h ⊓ L.U i ≤ L.U i)).op
    exact e.ge ⟨⟨hy, G.left.basicOpen_le _ hg⟩, hg⟩
end GlobalTheory.SecSpread
