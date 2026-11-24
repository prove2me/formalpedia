-- Prove2me | solution 1 for GlobalTheory.MulFinite.locallyQuasiFinite_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:36.181912+00:00
-- url     : https://prove2.me/submissions/5cd9f641-e01b-412f-a138-957dfbc67f3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_isClosed_basicOpen

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
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [IsProper f] {I : Type} (a : I → Γ(Z, ⊤)) (hc : ⨆ i, Z.basicOpen (a i) = ⊤)
    (ha : ∀ i, IsAffineOpen (Z.basicOpen (a i))) : LocallyQuasiFinite f := by
  have : IsZariskiLocalAtSource @LocallyQuasiFinite.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite.{0}) _ hc fun i => ?_
  have : IsClosedImmersion (Z.basicOpen (a i)).ι :=
    .of_isPreimmersion _ (by simpa using isClosed_basicOpen f (a i))
  have : IsAffine (Z.basicOpen (a i)).toScheme := ha i
  have : IsFinite ((Z.basicOpen (a i)).ι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  infer_instance
end GlobalTheory.MulFinite
