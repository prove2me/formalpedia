-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.hasFiniteLength_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:32.924723+00:00
-- url     : https://prove2.me/submissions/b583b51c-0e3a-4011-a264-3d9b2e6e38d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CoinvExact
namespace GlobalTheory.CompanionTheory.CoinvExact
theorem _root_.solution {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
    (f : α.IntertwiningMap β) (g : β.IntertwiningMap γ)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength β := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α β f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule β γ g
  have hg' : Function.Surjective g' := hg
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range f') :=
    IsFiniteLength.of_surjective hA f'.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.range f').subtype g' := by
    intro y
    have h1 : g' y = 0 ↔ g y = 0 := Iff.rfl
    have h2 : y ∈ Set.range (LinearMap.range f').subtype ↔ y ∈ Set.range f := by
      constructor
      · rintro ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨f' a, ⟨a, rfl⟩⟩, rfl⟩
    rw [h1, h2]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact (LinearMap.range f').subtype g'
    (LinearMap.range f').injective_subtype hg' hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hr, Module.length_ne_top_iff.2 hC⟩
end GlobalTheory.CompanionTheory.CoinvExact
