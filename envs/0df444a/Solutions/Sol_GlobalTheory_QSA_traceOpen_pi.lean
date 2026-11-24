-- Prove2me | solution 1 for GlobalTheory.QSA.traceOpen_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:06.602312+00:00
-- url     : https://prove2.me/submissions/70cf7a69-c672-4521-9ec0-fed70df3736d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi
import Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_glue_comp
import Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_nrm_comp
import Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_nrm_glue
import Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_continuous_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA
open TraceOpenPi
namespace GlobalTheory.QSA
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  intro ι _ R _ _ a b h g hg W hW
  have hgi : ∀ i, nrm (comp i g) = 1 := fun i => by
    rw [nrm_comp, hg]; rfl
  have hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g) := by
    refine continuous_glue.continuousAt.preimage_mem_nhds ?_
    rw [glue_comp]; exact hW
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨I, -, V, hV, hVW⟩ := hW'
  have hO := fun i => h i (comp i g) (hgi i) (V i) (hV i)
  choose O hOo hOn hOt using hO
  refine ⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i,
    Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩
  have ht' := fun i => hOt i (t i) (ht i (Set.mem_univ i))
  choose u huV hun hur using ht'
  refine ⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩
  · rw [nrm_glue]; funext i; exact hun i
  · funext i; exact hur i
end GlobalTheory.QSA
