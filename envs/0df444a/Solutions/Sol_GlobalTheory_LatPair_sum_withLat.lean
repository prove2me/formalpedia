-- Prove2me | solution 1 for GlobalTheory.LatPair.sum_withLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:46.147786+00:00
-- url     : https://prove2.me/submissions/7f1cf0d9-e2cc-4351-b680-488f03eb1715

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
namespace GlobalTheory.LatPair
theorem _root_.solution {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withLat L, F P = ∑ f, F (ofDual L f) := by
  haveI : Fintype {P : Pair k n // P.lat = L} := Fintype.ofEquiv _ (latEquiv L)
  rw [Finset.sum_subtype (withLat L) (p := fun P => P.lat = L) (fun _ => mem_withLat)]
  exact ((latEquiv L).sum_comp fun P => F P.1).symm
end GlobalTheory.LatPair
