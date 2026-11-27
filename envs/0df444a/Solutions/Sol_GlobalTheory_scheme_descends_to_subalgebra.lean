-- Prove2me | solution 1 for GlobalTheory.scheme_descends_to_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:02.597743+00:00
-- url     : https://prove2.me/submissions/24ad024f-7cee-482a-8705-b01097ea8b94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_hasModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V R : Type) [CommRing V] [CommRing R] [Algebra V R] (X : Over (Sp R)), LocallyOfFinitePresentation X.hom → QuasiCompact X.hom → IsSeparated X.hom → ∃ s : Finset R, ∀ W : Subalgebra V R, (↑s : Set R) ⊆ W → ∃ X₀ : Over (Sp W), LocallyOfFinitePresentation X₀.hom ∧ QuasiCompact X₀.hom ∧ QuasiSeparated X₀.hom ∧ Nonempty ((Over.pullback (spMap W.val.toRingHom)).obj X₀ ≅ X) := by
  classical
  intro V R _ _ _ X h₁ h₂ h₃
  obtain ⟨k, _, f, X₀, p₀, φ, hk, g₁, g₂, g₃, hφ⟩ := SpreadScheme.hasModel X.hom
  obtain ⟨s, hs⟩ := hk.out
  refine ⟨s.image f, fun W hW ↦ ?_⟩
  have hf (x : k) : f x ∈ W := by
    have hx : x ∈ Algebra.adjoin ℤ (s : Set k) := hs ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hW (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact W.mul_mem hx hy
  have e : spMap W.val.toRingHom ≫ spMap (f.codRestrict W hf) = spMap f := by
    rw [← Spec.map_comp]
    rfl
  have h := SpreadScheme.isPullback_lift hφ _ _ e
  refine ⟨Over.mk (pullback.snd p₀ (spMap (f.codRestrict W hf))), inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _)),
    inferInstanceAs (QuasiCompact (pullback.snd _ _)), inferInstanceAs (QuasiSeparated (pullback.snd _ _)),
    ⟨Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd⟩⟩
end GlobalTheory
