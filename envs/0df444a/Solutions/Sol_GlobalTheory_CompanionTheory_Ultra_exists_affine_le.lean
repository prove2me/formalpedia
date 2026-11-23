-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_affine_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:03.564028+00:00
-- url     : https://prove2.me/submissions/91c42d17-7735-491f-ab0e-de55344e1b94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {O : X.Opens} {x : X} (hx : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ O := by
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨W, hW⟩, hxW, hWO⟩
end GlobalTheory.CompanionTheory.Ultra
