-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.exists_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:28.614807+00:00
-- url     : https://prove2.me/submissions/7811e51a-8e2d-4145-993e-176a5c450113

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
theorem _root_.solution [IsTopologicalAddGroup X] {f : X → ℂ} (hf : f ∈ SB X) :
    ∃ U ∈ 𝓝 (0 : X), ∀ M : AddSubgroup X, (M : Set X) ⊆ U → ∀ t ∈ M, ∀ x, f (x + t) = f x := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hS : IsOpen {p : X × X | f (p.1 + p.2) - f p.1 = 0} :=
    ((hf'.1.comp_continuous continuous_add).comp₂ (hf'.1.comp_continuous continuous_fst)
      (fun a b : ℂ => a - b)).isOpen_fiber 0
  have hsub : tsupport f ×ˢ ({0} : Set X) ⊆ {p : X × X | f (p.1 + p.2) - f p.1 = 0} := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    simp
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hf'.2.isCompact isCompact_singleton hS hsub
  refine ⟨v, hv.mem_nhds (h0v (Set.mem_singleton 0)), fun M hM t ht x => ?_⟩
  have key : ∀ y ∈ tsupport f, ∀ s ∈ M, f (y + s) = f y := fun y hy s hs => by
    have h := huv (show (y, s) ∈ u ×ˢ v from ⟨hKu hy, hM hs⟩)
    exact sub_eq_zero.mp h
  by_cases hx : x ∈ tsupport f
  · exact key x hx t ht
  · by_cases hxt : x + t ∈ tsupport f
    · have h := key (x + t) hxt (-t) (M.neg_mem ht)
      rw [add_neg_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxt]
end GlobalTheory.KSp.FourInv
