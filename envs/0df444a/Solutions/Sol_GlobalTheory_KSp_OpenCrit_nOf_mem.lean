-- Prove2me | solution 1 for GlobalTheory.KSp.OpenCrit.nOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:30.923705+00:00
-- url     : https://prove2.me/submissions/1d413013-ae09-411a-8ade-d30cb8dab13a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
import Theorems.Thm_GlobalTheory_KSp_mem_sieg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.KSp.OpenCrit
theorem _root_.solution (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem
end GlobalTheory.KSp.OpenCrit
