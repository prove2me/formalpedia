-- Prove2me | solution 1 for GroundTheory.Arith.Toric.fg_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:52.994153+00:00
-- url     : https://prove2.me/submissions/f7a97eda-0ff0-48f5-b9e8-fdcd68b0f313

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
namespace GroundTheory.Arith.Toric
theorem _root_.solution [FiniteDimensional 𝕜 V] : (⊤ : PointedCone 𝕜 V).FG := by
  classical
  let b := Module.finBasis 𝕜 V
  let S : Finset V := Finset.univ.image b ∪ Finset.univ.image (fun i => -b i)
  refine ⟨S, top_le_iff.1 fun x _ => ?_⟩
  have key : ∀ y ∈ Submodule.span 𝕜 (Set.range b),
      y ∈ hull 𝕜 (S : Set V) ∧ -y ∈ hull 𝕜 (S : Set V) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨subset_hull (by simp [S]), subset_hull (by simp [S])⟩
    | zero => simp
    | add y z _ _ hy hz =>
      exact ⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩
    | smul c y _ hy =>
      rcases le_total 0 c with hc | hc
      · exact ⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩
      · refine ⟨?_, ?_⟩
        · rw [← neg_neg c, neg_smul, ← smul_neg]; exact smul_mem _ (neg_nonneg.2 hc) hy.2
        · rw [← neg_smul]; exact smul_mem _ (neg_nonneg.2 hc) hy.1
  exact (key x (by rw [b.span_eq]; exact Submodule.mem_top)).1
end GroundTheory.Arith.Toric
