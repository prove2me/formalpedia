-- Prove2me | solution 1 for GlobalTheory.SplitDict.exists_box_invariant_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:10.047075+00:00
-- url     : https://prove2.me/submissions/cc55c19f-cdf2-4ae1-b30c-514a91e8b80b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
omit [DecidableEq n] [T2Space T]
namespace GlobalTheory.SplitDict
theorem _root_.solution {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by
  obtain ⟨hlc, hcs⟩ := hf
  have hlc2 : IsLocallyConstant fun p : (T × (n → k)) × (n → k) => f (p.1.1, p.1.2 + p.2) - f p.1 :=
    (hlc.comp_continuous (by fun_prop)).sub (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
    hlc2.isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact (isCompact_singleton (x := (0 : n → k))) hW (by
    rintro ⟨z, u⟩ ⟨-, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu])
  obtain ⟨s, hs⟩ := exists_box_subset (hV.mem_nhds (h0V rfl))
  have key : ∀ z ∈ tsupport f, ∀ u ∈ box n s, f (z.1, z.2 + u) = f z := by
    intro z hz u hu
    have hm : (z, u) ∈ {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
      hUV ⟨hKU hz, hs hu⟩
    exact sub_eq_zero.mp hm
  refine ⟨s, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact key z hz u hu
  · by_cases hz' : (z.1, z.2 + u) ∈ tsupport f
    · have hneg : -u ∈ box n s := fun i _ => neg_mem_cball (hu i (Set.mem_univ i))
      have := key _ hz' (-u) hneg
      simp only [add_neg_cancel_right, Prod.mk.eta] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
end GlobalTheory.SplitDict
