-- Prove2me | solution 1 for GlobalTheory.T.self_dual_hermitian_lattice_basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:07.595909+00:00
-- url     : https://prove2.me/submissions/ae7dc495-0d97-45e7-999d-c3de0d6f1f78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExists
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExistsStatement
import Theorems.Thm_GlobalTheory_SelfDualLattice_exists_orthonormal_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) → ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧ ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.SelfDualLattice.exists_orthonormal_basis | exact GlobalTheory.SelfDualLattice.exists_orthonormal_basis | (intros; apply GlobalTheory.SelfDualLattice.exists_orthonormal_basis <;> assumption)
end _root_.GlobalTheory.T
