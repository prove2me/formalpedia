-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.smulQuotient_diagonal_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:30.300125+00:00
-- url     : https://prove2.me/submissions/c4911e6c-e67b-462a-9d19-33a93905b26a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
import Theorems.Thm_GroundTheory_Global_IdeleGroup_smulQuotient_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal



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
theorem _root_.solution (a : Kˣ) (I : 𝓘) (x : K) :
    smulQuotient (diagonal K a) I (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((a : K) * x) := by
  rw [smulQuotient_mk_eq_mk_iff]
  intro v
  rw [coe_finiteProj_diagonal, ← adicCompletion.coe_mul, sub_self]
  exact zero_mem _
end GroundTheory.Global.IdeleGroup
