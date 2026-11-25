-- Prove2me | solution 1 for GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:22:41.379359+00:00
-- url     : https://prove2.me/submissions/41a52a1a-e4f9-4a6a-a52a-62eb22043d46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsBaseChangeLatticeOfBasisAfterExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsBaseChangeLatticeOfBasisAfterExtensionStatement
import Theorems.Thm_GlobalTheory_isBaseChange_subtype_of_basis_after_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  first | exact @GlobalTheory.isBaseChange_subtype_of_basis_after_extension | exact GlobalTheory.isBaseChange_subtype_of_basis_after_extension | (intros; apply GlobalTheory.isBaseChange_subtype_of_basis_after_extension <;> assumption)
end _root_.GlobalTheory.T
