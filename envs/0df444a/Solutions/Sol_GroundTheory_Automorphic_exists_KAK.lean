-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_KAK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:15.73105+00:00
-- url     : https://prove2.me/submissions/aa647a5d-2817-4034-8a52-122bd859212a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
namespace GroundTheory.Automorphic
theorem _root_.solution (g : GL n 𝕜) :
    ∃ k₁ k₂ : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧
      (g : Matrix n n 𝕜) = (k₁ : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * k₂ := by
  have hp : (polarPos g).PosDef := polarPos_posDef g
  have hH : (polarPos g).IsHermitian := hp.isHermitian
  refine ⟨⟨polarUnitary g, polarUnitary_mem g⟩ * hH.eigenvectorUnitary, star hH.eigenvectorUnitary,
    hH.eigenvalues, hp.eigenvalues_pos, ?_⟩
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  calc (g : Matrix n n 𝕜) = polarUnitary g * polarPos g := (polarUnitary_mul_polarPos g).symm
    _ = polarUnitary g * ((hH.eigenvectorUnitary : Matrix n n 𝕜) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix n n 𝕜)) := by
        rw [← hs]
    _ = _ := by simp [Matrix.mul_assoc, Function.comp_def]
end GroundTheory.Automorphic
