-- Prove2me | solution 1 for OAI.Saxl.orbitAverage_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:13:30.144251+00:00
-- url     : https://prove2.me/submissions/8f602304-af4f-4d33-8383-701cdc706f52

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007

section
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma orbitAverage_base_oai {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

end

end OAI
end

theorem solution.{uV} : type_of% @OAI.Saxl.orbitAverage_base_oai.{uV} := @OAI.Saxl.orbitAverage_base_oai.{uV}
