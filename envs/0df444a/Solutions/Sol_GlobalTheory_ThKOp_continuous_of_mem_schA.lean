-- Prove2me | solution 1 for GlobalTheory.ThKOp.continuous_of_mem_schA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:36.760474+00:00
-- url     : https://prove2.me/submissions/6d80d063-c7cd-48d0-a198-96d91e510ebc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfMemSchA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThKOp
open scoped Classical
namespace GlobalTheory.ThKOp
theorem _root_.solution {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have hr : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [this]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply _)
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
      continuous_pi fun i => hr.comp (continuous_fst.comp (continuous_apply i))
    have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)
  | zero => exact continuous_const
  | add _ _ _ _ h h' => exact h.add h'
  | smul c _ _ h => exact continuous_const.mul h
end GlobalTheory.ThKOp
