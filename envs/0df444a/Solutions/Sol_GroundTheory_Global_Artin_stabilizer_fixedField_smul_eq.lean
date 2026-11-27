-- Prove2me | solution 1 for GroundTheory.Global.Artin.stabilizer_fixedField_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:49.843443+00:00
-- url     : https://prove2.me/submissions/0305365f-d5e7-45b5-bf5b-1967c787bf50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Theorems.Thm_GroundTheory_Global_Artin_stabilizer_fixedField_eq
import Theorems.Thm_GroundTheory_Global_Artin_stabilizer_smul_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
omit [IsGalois K L]
namespace GroundTheory.Global.Artin
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) (x : Gal(L/K)) :
    MulAction.stabilizer Gal(L/fixedField H) (x • w.asIdeal) =
      ((MulAut.conj x • MulAction.stabilizer Gal(L/K) w.asIdeal : Subgroup Gal(L/K)).subgroupOf
        H).map (fixedFieldMulEquiv H).toMonoidHom := by
  rw [stabilizer_fixedField_eq]
  congr 1
  exact stabilizer_smul_eq H x w.asIdeal
end GroundTheory.Global.Artin
