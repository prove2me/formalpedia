-- Prove2me | solution 1 for GlobalTheory.ConvFE.pullB_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:46.625857+00:00
-- url     : https://prove2.me/submissions/14a42086-21bd-4532-94f9-eee1b39a2cee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdicSumRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecScale
import Theorems.Thm_GlobalTheory_values_natural
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ConvFE
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α}
    {s : Raw D F k} (h : PullB D F φ k f s) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J := by
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) r z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left r z J hJ).2.1 (f α)
  have hJ' : Good D.P.L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ _
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)
end GlobalTheory.ConvFE
