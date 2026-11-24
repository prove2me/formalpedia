-- Prove2me | solution 1 for GlobalTheory.CharIndep.exists_asAlgebraHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:34.346379+00:00
-- url     : https://prove2.me/submissions/2848bdda-8db0-40e5-87af-6a41bfea1c0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissible
import Theorems.Thm_GlobalTheory_CharIndep_exists_smul_eq_self_and_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.CharIndep
namespace GlobalTheory.CharIndep
theorem _root_.solution {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W)
    [π.IsIrreducible] [π'.IsIrreducible] [IsEmpty (π.Equiv π')] (S : Submodule ℂ V)
    (T : Submodule ℂ W) [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] :
    ∃ a : MonoidAlgebra ℂ G, (∀ v ∈ S, π.asAlgebraHom a v = v) ∧
      ∀ w ∈ T, π'.asAlgebraHom a w = 0 := by
  have : IsEmpty (π'.Equiv π) := ⟨fun e => IsEmpty.false (α := π.Equiv π') e.symm⟩
  have s1 := (Representation.IntertwiningMap.equivLinearMapAsModule π π').toEquiv.symm.subsingleton
  have s2 := (Representation.IntertwiningMap.equivLinearMapAsModule π' π).toEquiv.symm.subsingleton
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional T).2 inferInstance
  obtain ⟨a, h1, h2⟩ := exists_smul_eq_self_and_smul_eq_zero (R := MonoidAlgebra ℂ G)
    (M := π.asModule) (N := π'.asModule) (fun f => Subsingleton.elim _ _)
    (fun f => Subsingleton.elim _ _) s t
  refine ⟨a, fun v hv => ?_, fun w hw => ?_⟩
  · rw [← hs] at hv
    exact LinearMap.eqOn_span (f := π.asAlgebraHom a) (g := LinearMap.id) (fun x hx => h1 x hx) hv
  · rw [← ht] at hw
    exact LinearMap.eqOn_span (f := π'.asAlgebraHom a) (g := 0) (fun x hx => h2 x hx) hw
end GlobalTheory.CharIndep
