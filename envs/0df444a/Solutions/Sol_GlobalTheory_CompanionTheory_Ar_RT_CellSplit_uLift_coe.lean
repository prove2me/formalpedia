-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.uLift_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:27.170036+00:00
-- url     : https://prove2.me/submissions/ceb5190f-b1bd-4b6a-9326-dccff0b0b97c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)
variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution (x : UG c₁ (dbl (J.map (pr₁ s)))) :
    (((uLift c c₁ c₂ s hc1 hc2 J x : UG c (dbl J)) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) =
      lift s ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) := rfl
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
