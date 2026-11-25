-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.exists_units_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:40:04.428832+00:00
-- url     : https://prove2.me/submissions/6cfae57b-20cb-4e54-af47-ca9bee428997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
namespace GlobalTheory.TorusQuotientLift
theorem _root_.solution [Module.Free ℤ X] (h : ∀ χ, χ ∈ unitWts i V) :
    ∃ u : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, IsWt i V (u (Multiplicative.ofAdd χ)).val χ := by
  choose v hv using h
  let b := Module.Free.chooseBasis ℤ X
  let l : X →ₗ[ℤ] Additive Γ(G.left, V)ˣ := b.constr ℤ fun k => Additive.ofMul (v (b k))
  refine ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  change IsWt i V (l χ).toMul.val χ
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt i V (l χ).toMul.val χ}
      add_mem' := fun {a b} ha hb => by
        change IsWt i V (l (a + b)).toMul.val _
        rw [map_add]; exact IsWt.mul ha hb
      zero_mem' := by
        change IsWt i V (l 0).toMul.val _
        rw [map_zero]; exact isWt_one
      neg_mem' := fun {a} ha => by
        change IsWt i V (l (-a)).toMul.val _
        rw [map_neg]; exact IsWt.inv ha }
  have : Submodule.span ℤ (Set.range b) ≤ H.toIntSubmodule := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    change IsWt i V (l (b k)).toMul.val _
    rw [Module.Basis.constr_basis]; exact hv _)
  exact this (b.span_eq ▸ Submodule.mem_top)
end GlobalTheory.TorusQuotientLift
