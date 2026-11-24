-- Prove2me | solution 1 for GlobalTheory.VVRank.functional_mem_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:47.568947+00:00
-- url     : https://prove2.me/submissions/133edda9-4dd4-4352-a167-1ddd0416b1a9

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
theorem _root_.solution {R R' M M' I κ : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] [Finite κ] (σ : R →+* R') (φ : M →ₛₗ[σ] M')
    (b : Module.Basis κ R M) (b' : Module.Basis κ R' M') (hb : ∀ i, b' i = φ (b i)) (t : I → M)
    (ht : Submodule.span R' (Set.range fun c => φ (t c)) = ⊤) (l : M →ₗ[R] R)
    (hl : ∀ c, σ (l (t c)) = 0) (x : M) : σ (l x) = 0 := by
  let l' : M' →ₗ[R'] R' := b'.constr R' fun i => σ (l (b i))
  have key : ∀ x, l' (φ x) = σ (l x) := fun x => by
    have := Fintype.ofFinite κ
    rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, ← hb, l', Module.Basis.constr_basis, smul_eq_mul,
      RingHom.id_apply, map_mul]
  have h0 : l' = 0 := LinearMap.ext_on_range ht fun c => (key _).trans (hl c)
  rw [← key, h0, LinearMap.zero_apply]
end GlobalTheory.VVRank
