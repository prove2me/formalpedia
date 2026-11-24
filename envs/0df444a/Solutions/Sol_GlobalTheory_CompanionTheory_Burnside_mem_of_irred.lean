-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Burnside.mem_of_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:13.198187+00:00
-- url     : https://prove2.me/submissions/43a450e2-4be5-4580-af62-687ee0143a69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
import Theorems.Thm_GlobalTheory_IrreducibleMembership_mem_of_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Burnside
namespace GlobalTheory.CompanionTheory.Burnside
theorem _root_.solution {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  first
  | exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | (apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)
end GlobalTheory.CompanionTheory.Burnside
