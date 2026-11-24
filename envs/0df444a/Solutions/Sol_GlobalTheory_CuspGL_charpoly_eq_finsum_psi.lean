-- Prove2me | solution 1 for GlobalTheory.CuspGL.charpoly_eq_finsum_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:09:36.272865+00:00
-- url     : https://prove2.me/submissions/f049222e-3a45-4e09-823c-c70be32f84c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsi
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V) :
    s (LinearMap.charpoly g) =
      ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  haveI := Fintype.ofFinite {W : Submodule F V // ∀ x ∈ W, g x ∈ W}
  haveI := Fintype.ofFinite {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}
  let T : {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := ⟨⊤, fun _ _ => Submodule.mem_top⟩
  have hT : psi s T.1 (g.restrict T.2) = psi s V g := by
    rw [← psi_conj F s T.1 V Submodule.topEquiv (g.restrict T.2)]
    congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ T), hT, psi_eq,
    finsum_eq_sum_of_fintype]
  rw [sub_add, eq_comm, sub_eq_self, sub_eq_zero]
  refine Finset.sum_bij (fun W _ => ⟨W.1, W.2.2⟩) ?_ ?_ ?_ ?_
  · intro W _
    refine Finset.mem_erase.2 ⟨fun h => W.2.1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro b hb
    exact ⟨⟨b.1, fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h), b.2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl
end GlobalTheory.CuspGL
