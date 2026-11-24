-- Prove2me | solution 1 for GlobalTheory.KilledFin.commute_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:27.194808+00:00
-- url     : https://prove2.me/submissions/8cf1a986-3755-4e6b-98d3-9dfd5b7e3a36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (s : Set (Module.End ℂ V)) (t : Module.End ℂ V)
    (ht : ∀ u ∈ s, Commute u t) (z : Module.End ℂ V) (hz : z ∈ Algebra.adjoin ℂ s) (q : ℂ[X]) :
    Commute z (aeval t q) := by
  have h1 : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {t} := by
    rw [Algebra.adjoin_le_iff]
    intro u hu
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ((ht u hu).eq).symm
  have h2 : z ∈ Subalgebra.centralizer ℂ {t} := h1 hz
  have h3 : Algebra.adjoin ℂ {t} ≤ Subalgebra.centralizer ℂ {z} := by
    rw [Algebra.adjoin_le_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [Subalgebra.mem_centralizer_iff] at h2
    exact (h2 g rfl).symm
  have h4 := h3 (Polynomial.aeval_mem_adjoin_singleton ℂ (x := t) (p := q))
  rw [Subalgebra.mem_centralizer_iff] at h4
  exact h4 z rfl
end GlobalTheory.KilledFin
