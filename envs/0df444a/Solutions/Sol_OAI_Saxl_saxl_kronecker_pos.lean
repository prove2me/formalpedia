-- Prove2me | solution 1 for OAI.Saxl.saxl_kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T20:02:44.397786+00:00
-- url     : https://prove2.me/submissions/2a627f2c-0c28-42dd-a45f-229adc9de1c2

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_cyclic_saxl_conjecture

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  unfold intertwiningLiftSubrep at h
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

lemma staircaseToTensor_injective (m : ℕ) : Function.Injective (staircaseToTensor m) := by
  unfold staircaseToTensor
  exact @intertwiningLiftSubrep_injective (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

/- Every Specht type occurs in the specified staircase cyclic module. -/
theorem saxl_of_cyclic_support (h : CyclicSaxlConjecture) : SaxlConjecture := by
  intro m hm μ hμ
  apply (kronecker_pos_iff _ _ _).mpr
  obtain ⟨f, hf⟩ := h m hm μ hμ
  refine ⟨(staircaseToTensor m).comp f, ?_⟩
  intro he
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply staircaseToTensor_injective m
  exact (congrArg (fun F : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) => F x) he).trans
    (map_zero _).symm

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

theorem saxl_conjecture : SaxlConjecture := saxl_of_cyclic_support cyclic_saxl_conjecture



theorem saxl_kronecker_pos_oai (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = m * (m + 1) / 2) :
    0 < kronecker (canonicalTableau (staircase m) (staircase_card m))
      (canonicalTableau (staircase m) (staircase_card m)) (canonicalTableau μ hμ) := by
  have H : ∀ (n : ℕ) (hn : (staircase m).card = n) (hnu : μ.card = n),
      0 < kronecker (canonicalTableau (staircase m) hn)
        (canonicalTableau (staircase m) hn) (canonicalTableau μ hnu) := by
    intro n hn hnu
    subst n
    exact saxl_conjecture m hm μ hnu
  exact H _ (staircase_card m) hμ

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.saxl_kronecker_pos_oai := @OAI.Saxl.saxl_kronecker_pos_oai
