-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.smulQuotient_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:32.255987+00:00
-- url     : https://prove2.me/submissions/3805a5b4-8e45-4616-81db-499b5927b0d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
import Theorems.Thm_GroundTheory_Global_IdeleGroup_smulQuotient_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective


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
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    smulQuotient 1 I q = Submodule.quotEquivOfEq _ _ (by rw [one_smul]) q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.quotEquivOfEq_mk, smulQuotient_mk_eq_mk_iff]
  intro v
  rw [map_one, Units.val_one, one_mul, sub_self]
  exact zero_mem _
end GroundTheory.Global.IdeleGroup
