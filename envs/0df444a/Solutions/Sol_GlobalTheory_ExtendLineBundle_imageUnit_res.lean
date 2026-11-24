-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.imageUnit_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:42.944162+00:00
-- url     : https://prove2.me/submissions/017da765-6877-44be-a0d0-a6b8b862dafa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
omit [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ) :
    imageUnit j V (res hle a) = res (j.image_mono hle) (imageUnit j U a) :=
  Units.ext (congrArg (fun q => q.hom a.val) (j.appIso_inv_naturality (homOfLE hle).op))
end GlobalTheory.ExtendLineBundle
