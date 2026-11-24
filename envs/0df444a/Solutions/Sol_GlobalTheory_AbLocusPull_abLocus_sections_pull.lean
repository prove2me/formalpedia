-- Prove2me | solution 1 for GlobalTheory.AbLocusPull.abLocus_sections_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:23.648838+00:00
-- url     : https://prove2.me/submissions/4d04f6ce-bf23-4f80-9ea1-1f6a48f051dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Theorems.Thm_GlobalTheory_AbLocusPull_exists_secOn_pull
import Theorems.Thm_GlobalTheory_AbLocusPull_isProper_restrict_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_abLocusOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_abLocus_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLocusPull
theorem _root_.solution : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G f φ → ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) ∧ ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro X X' f G _ G' _ φ hG hp
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hU, hUp⟩
    refine ⟨f ⁻¹ᵁ U, ?_, ?_⟩
    · ext x
      change f x ∈ (U : Set X) ↔ x ∈ abLocus G'
      rw [hU]
      exact abLocus_pullback abLocusOne hG hp.1 x
    · have := hUp
      exact isProper_restrict_pull hp.1 U
  · intro L L' hL hL' hw hsec x
    obtain ⟨V, hxV, θ, hθ, hV⟩ := hsec (f x)
    have hW : G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ φ ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
      intro g hg
      show G.hom (φ g) ∈ V
      rw [← Scheme.Hom.comp_apply, hp.1.w, Scheme.Hom.comp_apply]
      exact hg
    obtain ⟨θ', hθ', hnz⟩ := exists_secOn_pull hL hL' hw hW hθ
    refine ⟨f ⁻¹ᵁ V, hxV, θ', hθ', fun y hy => ?_⟩
    obtain ⟨g, i, hg, hgi⟩ := hV (f y) hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := f) g y hg
    have e1 : φ (hp.1.isoPullback.inv z) = g := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_fst, hz1]
    have e2 : G'.hom (hp.1.isoPullback.inv z) = y := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_snd, hz2]
    obtain ⟨hcov', -, -⟩ := hL'
    obtain ⟨k, hk⟩ : ∃ k, hp.1.isoPullback.inv z ∈ L'.U k := by
      have hm : hp.1.isoPullback.inv z ∈ (⨆ i, L'.U i) := by rw [hcov']; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hm
    refine ⟨hp.1.isoPullback.inv z, k, e2, hnz _ ?_ i k hk ?_⟩
    · show G'.hom (hp.1.isoPullback.inv z) ∈ f ⁻¹ᵁ V
      rw [e2]; exact hy
    · rw [e1]; exact hgi
end GlobalTheory.AbLocusPull
