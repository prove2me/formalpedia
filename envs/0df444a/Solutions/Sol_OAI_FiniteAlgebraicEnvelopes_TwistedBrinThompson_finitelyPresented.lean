-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.finitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T19:34:20.859247+00:00
-- url     : https://prove2.me/submissions/74805062-49ae-4e67-afbf-db03b1f04ddf

import Mathlib
import Definitions.Def_OAIFAE004

section
-- module Solutions.OAIFAE.FinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentation seeds, localization, and structural relations.
-/

namespace FiniteAlgebraicEnvelopes
namespace FiniteLocalizationClosure
universe u v
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Group K]
variable (f : K →* K) (a : K) (s r : Finset K)

variable (hs : Subgroup.closure (s : Set K)=⊤)
include hs

omit hs in
lemma kernel_finitelyNormallyGenerated : (kernel f a s r).IsFinitelyNormallyGenerated :=
  ⟨(relations f a s r : Set K),(relations f a s r).finite_toSet,rfl⟩

omit hs in
instance quotient_finitelyPresented [Group.IsFinitelyPresented K] :
    Group.IsFinitelyPresented (Quotient f a s r) :=
  Group.IsFinitelyPresented.quotient _ (kernel_finitelyNormallyGenerated f a s r)

end FiniteLocalizationClosure
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

variable [MulAction.IsPretransitive Γ X]

instance localQuotient_finitelyPresented [Group.IsFinitelyPresented Γ]
    (s r : Finset (Seed (Γ:=Γ) x)) :
    Group.IsFinitelyPresented (LocalQuotient x s r) := inferInstance

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeRefinement
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tree prefixes, common refinements, and quotient refinement relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

instance structuralQuotient_finitelyPresented [Group.IsFinitelyPresented Γ]
    (s : Finset (Seed (Γ:=Γ) x)) : Group.IsFinitelyPresented (StructuralQuotient x s) := inferInstance

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.DecoratedPresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Stabilizer cocycles, decorations, and explicit finite endpoint relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))

instance decoratedQuotient_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (DecoratedQuotient x s t) := inferInstance

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y : X)

instance endpointQuotient_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (EndpointQuotient x s t y) := inferInstance

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Intermediate simple overgroups, finite-presentation transport, and Boone–Higman equivalence.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Finite presentation of the actual twisted finite-chart group for a faithful
2-transitive action with finitely generated point stabilizers. -/
theorem finitelyPresented_oai [Group.IsFinitelyPresented Γ] [Infinite X]
    [FaithfulSMul Γ X]
    (htwo : ∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂)
    (hstab : ∀ x : X, Group.FG (MulAction.stabilizer Γ x)) :
    Group.IsFinitelyPresented (group (Γ:=Γ) (X:=X)) := by
  classical
  let : MulAction.IsPretransitive Γ X := ⟨by
    intro a b
    obtain ⟨a',ha⟩ := exists_ne a
    obtain ⟨b',hb⟩ := exists_ne b
    obtain ⟨g,hg,_⟩ := htwo a a' b b' (Ne.symm ha) (Ne.symm hb)
    exact ⟨g,hg⟩⟩
  let x : X := Classical.arbitrary X
  obtain ⟨y,hy⟩ := exists_ne x
  let : Group.FG (Generators.Seed (Γ:=Γ) x) := by
    obtain ⟨n,φ,hφ,_⟩ := Group.IsFinitelyPresented.out (G:=Generators.Seed (Γ:=Γ) x)
    exact Group.fg_of_surjective hφ
  let := hstab x
  obtain ⟨s,hs⟩ := Group.fg_def.mp (inferInstance : Group.FG (Generators.Seed (Γ:=Γ) x))
  obtain ⟨t,ht⟩ := Group.fg_def.mp (inferInstance : Group.FG (MulAction.stabilizer Γ x))
  exact Group.IsFinitelyPresented.equiv
    (Generators.endpointEquivalence x s t y hs ht (Ne.symm hy) htwo)

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.finitelyPresented_oai.{u, v} := @OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.finitelyPresented_oai.{u, v}
