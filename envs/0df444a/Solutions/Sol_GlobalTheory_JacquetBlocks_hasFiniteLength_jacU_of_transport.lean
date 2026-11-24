-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.hasFiniteLength_jacU_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:43.493847+00:00
-- url     : https://prove2.me/submissions/3034d13d-a862-4058-b507-6c85c84bcb68

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_of_surjective
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_hasFiniteLength_comp_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h
end GlobalTheory.JacquetBlocks
