-- Prove2me | solution 1 for GroundTheory.Global.SUnit.finrank_quotient_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:11.672932+00:00
-- url     : https://prove2.me/submissions/b6c9d08c-afa4-4a25-9213-7c406c84332d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
import Theorems.Thm_GroundTheory_Global_SUnit_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.Global.SUnit
namespace GroundTheory.Global.SUnit
theorem _root_.solution [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) = Units.rank K + Nat.card S := by
  rw [← finrank_eq S]
  exact finrank_quotient_torsion_eq (M := Additive (S.unit K))
end GroundTheory.Global.SUnit
