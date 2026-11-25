-- Prove2me | solution 1 for GlobalTheory.BorelUMod.isInducing_GU_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:11.314554+00:00
-- url     : https://prove2.me/submissions/73a9a202-9199-4fbe-a535-7b08376b3581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Theorems.Thm_GlobalTheory_BorelUMod_continuous_adjJ
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
theorem _root_.solution {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Topology.IsInducing fun g : GU σ n => (g.1.val : Matrix (Fin n) (Fin n) L) := by
  have h1 : Topology.IsInducing fun g : GU σ n => Units.embedProduct _ g.1 :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  refine Topology.IsInducing.of_comp (g := fun A : Matrix (Fin n) (Fin n) L => (A, MulOpposite.op (adjJ σ A)))
    (Units.continuous_val.comp continuous_subtype_val)
    (continuous_id.prodMk (MulOpposite.continuous_op.comp (continuous_adjJ hσ n))) ?_
  convert h1 using 1
  funext g
  simp only [Function.comp_apply, Units.embedProduct_apply, (mem_GU_iff_adjJ σ _).1 g.2]
end GlobalTheory.BorelUMod
