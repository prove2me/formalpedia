-- Prove2me | solution 1 for GlobalTheory.GrpTangent.finiteEtale_mulN_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:29.281986+00:00
-- url     : https://prove2.me/submissions/2b2eeef0-fba4-44bf-80a6-858758d8ba82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_etale_mulN
import Theorems.Thm_GlobalTheory_GrpTangent_etale_torsion
import Theorems.Thm_GlobalTheory_GrpTangent_isFinite_mulN
import Theorems.Thm_GlobalTheory_GrpTangent_isFinite_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.GrpTangent
theorem _root_.solution [hG : IsAbelianScheme G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
      IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom :=
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  ⟨⟨isFinite_mulN G hn, etale_mulN G hn⟩, isFinite_torsion G hn, etale_torsion G hn⟩
end GlobalTheory.GrpTangent
