-- Prove2me | solution 1 for GlobalTheory.PointsCompact.compactSpace_points_polAV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:53.854682+00:00
-- url     : https://prove2.me/submissions/1a7cc152-20b9-4e95-b07e-997168447f21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV
import Theorems.Thm_GlobalTheory_PointsCompact_continuous_comp
import Theorems.Thm_GlobalTheory_PointsCompact_compact_of_sections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PointsCompact
namespace GlobalTheory.PointsCompact
theorem _root_.solution : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ P : Out.PolAV (Sp ℂ), @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ P.A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ P.A) | ∃ (U : P.A.left.Opens) (f : Γ(P.A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})) := by
  intro h1 h2 P
  obtain ⟨A, grp, hab, g, hsm, L, hL, hrig, h9⟩ := P
  unfold Out.RelAmple at h9
  obtain ⟨N, hN, M, s, hcov, hh⟩ := h9 ⊤ (AlgebraicGeometry.isAffineOpen_top _)
  let X' : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  haveI : IsIso (⊤ : (Sp ℂ).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hψ : Function.Surjective (((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    have s1 := (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2
    have s2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
    exact s1.comp s2
  have hC : @CompactSpace _ (pointTopology X') := by
    refine compact_of_sections h1 h2 X' (Out.powOver A hsm ⊤ N) s hcov fun i => ?_
    obtain ⟨ha, r, hr1, hr2⟩ := hh i
    refine ⟨ha, r, hr1, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) ?_).hom.comp
      ((((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)), ?_, ?_⟩
    · exact le_top
    · intro a
      rfl
    · intro y
      obtain ⟨p, rfl⟩ := hr2 y
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ hψ p
      refine ⟨q, ?_⟩
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
      exact (MvPolynomial.eval₂_map _ _ _ _).symm
  let φ : X' ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι _ _).symm
  letI := pointTopology X'
  letI := pointTopology A
  have hsurj : Function.Surjective (fun y : 𝟙_ (Over (Sp ℂ)) ⟶ X' => y ≫ φ) := by
    intro x
    have hr : Set.range x.left.base ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι.base := by
      rw [Scheme.Opens.range_ι]
      intro y _
      trivial
    let y0 := IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hr
    have hy0 : y0 ≫ (A.hom ⁻¹ᵁ ⊤).ι = x.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk y0 ?_, ?_⟩
    · show y0 ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι = _
      rw [morphismRestrict_ι, ← Category.assoc, hy0]
      exact Over.w x
    · ext1
      exact hy0
  exact hsurj.compactSpace (continuous_comp h1 φ)
end GlobalTheory.PointsCompact
