-- Prove2me | solution 1 for GroundTheory.Global.Modulus.rayClassGroupEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:33.569181+00:00
-- url     : https://prove2.me/submissions/a0886ed4-40d5-41ce-879d-16118f8327f5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
    𝔪.rayClassGroupEquiv (QuotientGroup.mk x : 𝔪.RayClassGroup) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm
      (QuotientGroup.mk x : 𝔪.RayClassGroup) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [rayClassGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl
end GroundTheory.Global.Modulus
