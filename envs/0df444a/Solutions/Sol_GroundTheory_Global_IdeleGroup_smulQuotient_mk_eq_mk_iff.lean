-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:50.889546+00:00
-- url     : https://prove2.me/submissions/9d1b80de-5826-43da-b090-b42dcf86be54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
import Theorems.Thm_GroundTheory_Global_quotientEquivLocalQuotients_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_localMul_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_quotientEquivLocalQuotients_smulQuotient
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding


attribute [local simp] GroundTheory.Global.quotientEquivLocalQuotients_mk

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
theorem _root_.solution (s : IdeleGroup K) (I : 𝓘) (x y : K) :
    smulQuotient s I (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (finiteProj v s : v.adicCompletion K) * (x : v.adicCompletion K) -
        (y : v.adicCompletion K) ∈ localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [← (quotientEquivLocalQuotients (s • I).ne_zero).injective.eq_iff,
    quotientEquivLocalQuotients_smulQuotient, quotientEquivLocalQuotients_mk,
    quotientEquivLocalQuotients_mk, DFinsupp.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply, toLocalQuotients_apply,
    toLocalQuotients_apply, localMul_mk, Submodule.Quotient.eq]
end GroundTheory.Global.IdeleGroup
