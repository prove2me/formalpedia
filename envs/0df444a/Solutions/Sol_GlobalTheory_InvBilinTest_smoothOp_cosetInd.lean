-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.smoothOp_cosetInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:56.253787+00:00
-- url     : https://prove2.me/submissions/8ba2bd59-80ae-4373-a864-e4c3ed956095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_cosetInd_apply
import Theorems.Thm_GlobalTheory_InvBilinTest_integral_ite
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
namespace GlobalTheory.InvBilinTest
theorem _root_.solution (hπ : IsSmooth π) (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) {w : V} (hw : ∀ k ∈ K, π k w = w) :
    smoothOp π μ (cosetInd K ho hK 1).1 w = (μ.real K : ℂ) • w := by
  refine eq_of_forall_dual fun l => ?_
  rw [hπ.map_smoothOp (cosetInd K ho hK 1).2.1 (cosetInd K ho hK 1).2.2, map_smul, smul_eq_mul,
    ← integral_ite K ho]
  congr 1
  ext g
  rw [cosetInd_apply]
  by_cases hg : g ∈ K
  · simp [hg, hw g hg]
  · simp [hg]
end GlobalTheory.InvBilinTest
