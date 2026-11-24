-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpLower.sum_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:22.735964+00:00
-- url     : https://prove2.me/submissions/6fad2975-88a9-4938-9066-5d3a7f677dd9

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset
namespace GlobalTheory.CompanionTheory.GapOpLower
theorem _root_.solution {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (D : (Fin (n + 1) → k) → ℝ) (hD : ∀ b, (∀ s : k, b ≠ s • a) → D b = 0) :
    ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), D b
      = ∑ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), D (s • a) := by
  have hinj : Function.Injective (fun s : k => s • a) := smul_left_injective k ha
  rw [← Finset.sum_image (f := D) (g := fun s : k => s • a) hinj.injOn]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact smul_ne_zero hs ha
  · intro b hb hb'
    refine hD b ?_
    intro s hs
    apply hb'
    refine Finset.mem_image.mpr ⟨s, ?_, hs.symm⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rintro rfl
    exact hb (by simpa using hs)
end GlobalTheory.CompanionTheory.GapOpLower
