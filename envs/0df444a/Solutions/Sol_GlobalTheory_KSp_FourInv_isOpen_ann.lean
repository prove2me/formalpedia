-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.isOpen_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:52.837927+00:00
-- url     : https://prove2.me/submissions/72aafa30-e8a1-4dbe-9a66-7acb2b1a341a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
namespace GlobalTheory.KSp.FourInv
theorem _root_.solution [IsTopologicalAddGroup X] (he : IsPair e) {L : Set X} (hL : IsCompact L) :
    IsOpen (ann he L : Set X) := by
  have hS : IsOpen {p : X × X | e p.1 p.2 = 1} := he.lc.isOpen_fiber 1
  have hsub : L ×ˢ ({0} : Set X) ⊆ {p : X × X | e p.1 p.2 = 1} := by
    rintro ⟨y, z⟩ ⟨_, hz⟩
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact zero_right he y
  obtain ⟨u, v, -, hv, hLu, h0v, huv⟩ := generalized_tube_lemma hL isCompact_singleton hS hsub
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  refine Filter.mem_of_superset (hv.mem_nhds (h0v (Set.mem_singleton 0))) ?_
  intro z hz
  show ∀ y ∈ L, e y z = 1
  intro y hy
  exact huv (show (y, z) ∈ u ×ˢ v from ⟨hLu hy, hz⟩)
end GlobalTheory.KSp.FourInv
