-- Prove2me | solution 1 for GlobalTheory.FieldDescentGen.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:32.9903+00:00
-- url     : https://prove2.me/submissions/0d91345b-b3fd-4278-ad4e-2784b681bba7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.FieldDescentGen
variable {X₀ X : Scheme.{0}}
namespace GlobalTheory.FieldDescentGen
theorem _root_.solution {L : LB X} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) (s : L.Sec) :
    ∃ u : Γ(X, ⊤), ∀ j, s.f j =
      (X.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom u * (t.s j).val := by
  obtain ⟨u, hu⟩ := Out.TLinPf.glue L.U hL.cover (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e : res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)⁻¹ =
        L.g i j * res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i)⁻¹ := by
      rw [map_inv, map_inv, ht i j, mul_inv, mul_inv_cancel_left]
    have e' : (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom ((t.s j)⁻¹).val =
        (L.g i j).val * (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom ((t.s i)⁻¹).val :=
      congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e']
    ring)
  exact ⟨u, fun j => by rw [hu j, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]⟩
end GlobalTheory.FieldDescentGen
