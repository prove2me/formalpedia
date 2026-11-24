-- Prove2me | solution 1 for GlobalTheory.ThetaOnto.mem_span_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:19.183022+00:00
-- url     : https://prove2.me/submissions/22c933b5-3ac9-415e-9d53-884d039f41cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanOfCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaOnto
namespace GlobalTheory.ThetaOnto
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V → Prop) {N : ℕ}
    (hN : ∀ (M : ℕ) (f : Fin M → V), (∀ k, Q (f k)) → LinearIndependent ℂ f → M ≤ N)
    (f : Fin N → V) (hf : ∀ k, Q (f k)) (hli : LinearIndependent ℂ f) {v : V} (hv : Q v) :
    ∃ a : Fin N → ℂ, ∑ i, a i • f i = v := by
  by_contra hne
  have hv' : v ∉ Submodule.span ℂ (Set.range f) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact hne
  have hli' : LinearIndependent ℂ (Fin.cons v f : Fin (N + 1) → V) :=
    linearIndependent_finCons.mpr ⟨hli, hv'⟩
  have hQ : ∀ k, Q ((Fin.cons v f : Fin (N + 1) → V) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hf i
  have := hN (N + 1) _ hQ hli'
  omega
end GlobalTheory.ThetaOnto
