-- Prove2me | solution 1 for GroundTheory.Global.Modulus.quotientEquivIdealRayClassGroup_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:30.46332+00:00
-- url     : https://prove2.me/submissions/e9e2fba3-a2d8-44d2-a297-f6e93d042f11

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass
import Theorems.Thm_GroundTheory_Global_Modulus_rayClassGroupEquiv_mk
import Theorems.Thm_GroundTheory_Global_Modulus_quotientMapCongruenceEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.quotientEquivIdealRayClassGroup (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  rw [quotientEquivIdealRayClassGroup, MulEquiv.trans_apply, quotientMapCongruenceEquiv_mk,
    rayClassGroupEquiv_mk _ hx]
end GroundTheory.Global.Modulus
