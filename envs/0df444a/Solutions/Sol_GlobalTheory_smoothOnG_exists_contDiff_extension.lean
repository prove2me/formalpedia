-- Prove2me | solution 1 for GlobalTheory.smoothOnG_exists_contDiff_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:48.630736+00:00
-- url     : https://prove2.me/submissions/27fe0087-6514-4109-a29a-266530fa9092

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContDiffExtensionOfIsClosed
import Theorems.Thm_GlobalTheory_exists_contDiff_extension_of_isClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped ContDiff Manifold Topology
open GlobalTheory
open scoped ContDiff Manifold Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), _root_.Formalism.REAL.SmoothOnG ε f →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
        ∀ g : Matrix (Fin n) (Fin n) ℂ, _root_.Formalism.REAL.inUJ ε g → F (fun i j => g i j) = f g := by
  intro n ε f hf
  let S : Set (Fin n → Fin n → ℂ) := {x | _root_.Formalism.REAL.inUJ ε (Matrix.of x)}
  have hS : IsClosed S := by
    have h0 : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
    have hc : Continuous
        (fun x : Fin n → Fin n → ℂ => Matrix.conjTranspose (Matrix.of x) * _root_.Formalism.REAL.Jm ε * Matrix.of x) :=
      (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  obtain ⟨F, hF, hFS⟩ := _root_.GlobalTheory.exists_contDiff_extension_of_isClosed hS
    (fun x => f (Matrix.of x)) (by
      intro x hx
      unfold _root_.Formalism.REAL.SmoothOnG at hf
      obtain ⟨U, G, hU, hxU, hG, hfG⟩ := hf (Matrix.of x) hx
      let U' : Set (Fin n → Fin n → ℂ) := U
      let G' : (Fin n → Fin n → ℂ) → ℂ := G
      have hU' : IsOpen U' := hU
      have hG' : ContDiffOn ℝ ∞ G' U' := hG
      exact ⟨U', G', hU', hxU, hG', fun y hy hyS => hfG (Matrix.of y) hy hyS⟩)
  exact ⟨F, hF, fun g hg => hFS (fun i j => g i j) hg⟩
end _root_.GlobalTheory
end GlobalTheory
