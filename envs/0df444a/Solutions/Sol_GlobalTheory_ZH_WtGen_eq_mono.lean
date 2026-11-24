-- Prove2me | solution 1 for GlobalTheory.ZH.WtGen.eq_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:55.529538+00:00
-- url     : https://prove2.me/submissions/457dba32-ebd2-4378-9bbb-49541dce6663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
import Theorems.Thm_GlobalTheory_ZH_WtPart_cf_ext
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb
namespace GlobalTheory.ZH.WtGen
theorem _root_.solution {s : R} {α : X} (h : ∀ χ, χ ≠ α → cf hb χ s = 0) :
    s = f (cf hb α s) * m (Multiplicative.ofAdd α) := by
  refine cf_ext hb fun χ => ?_
  rw [cf_mono]
  split_ifs with e
  · rw [e]
  · exact h χ fun e' => e e'.symm
end GlobalTheory.ZH.WtGen
