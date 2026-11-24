-- Prove2me | solution 1 for GlobalTheory.VVRank.span_eq_top_of_functionals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:50.425253+00:00
-- url     : https://prove2.me/submissions/48004534-2e4c-450e-8282-a90d5b9c6d25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals

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
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution {R M I κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Finite κ]
    (b : Module.Basis κ R M) (t : I → M)
    (H : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ∀ l : M →ₗ[R] R, (∀ c, l (t c) ∈ 𝔪) → ∀ x, l x ∈ 𝔪) :
    Submodule.span R (Set.range t) = ⊤ := by
  have : Module.Finite R M := Module.Finite.of_basis b
  have : Module.Free R M := Module.Free.of_basis b
  rcases eq_top_or_exists_le_coatom (Submodule.span R (Set.range t)) with h | ⟨Q, hQ, hle⟩
  · exact h
  exfalso
  obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := M ⧸ Q)).1
    ((isSimpleModule_iff_isCoatom).2 hQ)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property 𝔪.mkQ (e.toLinearMap ∘ₗ Q.mkQ)
    (Submodule.mkQ_surjective _)
  have key : ∀ x, l x ∈ 𝔪 ↔ x ∈ Q := fun x => by
    have := LinearMap.congr_fun hl x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at this
    rw [← Submodule.Quotient.mk_eq_zero, this, e.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  exact hQ.1 (eq_top_iff.2 fun x _ => (key x).1 (H 𝔪 h𝔪 l
    (fun c => (key _).2 (hle (Submodule.subset_span ⟨c, rfl⟩))) x))
end GlobalTheory.VVRank
