-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_finite_affine_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:10.358579+00:00
-- url     : https://prove2.me/submissions/b3b05597-ce15-4b9b-8a2b-ff1a03b4be23

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_affine_le

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
theorem _root_.solution (O : X.Opens) (hO : IsCompact (O : Set X)) :
    ∃ S : Set X.affineOpens, S.Finite ∧ (∀ W ∈ S, W.1 ≤ O) ∧ ∀ x ∈ O, ∃ W ∈ S, x ∈ W.1 := by
  classical
  have h : ∀ x : X, ∃ W : X.affineOpens, x ∈ O → x ∈ W.1 ∧ W.1 ≤ O := by
    intro x
    by_cases hx : x ∈ O
    · obtain ⟨W, h1, h2⟩ := exists_affine_le hx
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · obtain ⟨W, h1, h2⟩ := exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨W, fun h => absurd h hx⟩
  choose w hw using h
  obtain ⟨t, ht, hcov⟩ := hO.elim_nhds_subcover (fun x => ((w x).1 : Set X))
    (fun x hx => ((w x).1.2.mem_nhds (hw x hx).1))
  refine ⟨w '' (t : Set X), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hw x (ht x hx)).2
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact ⟨w y, ⟨y, hy, rfl⟩, hxy⟩
end GlobalTheory.CompanionTheory.Ultra
