-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_sumElim_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:33.342215+00:00
-- url     : https://prove2.me/submissions/d10e0236-475f-4b26-857d-5c656df0c3c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLinearIndependentSumElimOfFinrankEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have h1 := Submodule.finrank_add_eq_of_isCompl hQ
  rw [finrank_span_eq_card hv, Fintype.card_fin, hV] at h1
  have h2 : Module.finrank k Q = n' := by omega
  let b := Module.finBasisOfFinrankEq k Q h2
  refine ⟨fun j => (b j : V), hv.sum_type (b.linearIndependent.map' Q.subtype Q.ker_subtype) ?_⟩
  refine hQ.disjoint.mono_right ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact (b j).2
end GlobalTheory
