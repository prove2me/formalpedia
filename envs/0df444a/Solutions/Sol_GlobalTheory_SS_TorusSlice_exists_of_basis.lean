-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.exists_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:07:30.025785+00:00
-- url     : https://prove2.me/submissions/b39abd77-37a3-427c-8496-465785198a39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_eq

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {I : Type} (b : Module.Basis I ℤ X) {Z : Over S} (v : I → Γ(Z.left, ⊤)ˣ) :
    ∃ t : Z ⟶ splitTorus S X, ∀ n, ch t (b n) = (v n).val := by
  refine ⟨(splitTorusPointsEquiv S X Z).symm (MonoidHom.toAdditiveRight.symm
    (b.constr ℤ fun n => Additive.ofMul (v n)).toAddMonoidHom), fun n => ?_⟩
  rw [ch_eq, MulEquiv.apply_symm_apply]
  exact congrArg (fun x : Additive Γ(Z.left, ⊤)ˣ => x.toMul.val) (b.constr_basis ℤ (fun n => Additive.ofMul (v n)) n)
end GlobalTheory.SS.TorusSlice
