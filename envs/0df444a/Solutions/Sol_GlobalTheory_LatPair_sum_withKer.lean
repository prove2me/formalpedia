-- Prove2me | solution 1 for GlobalTheory.LatPair.sum_withKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:49.75472+00:00
-- url     : https://prove2.me/submissions/b8464bff-f3fd-41e3-92d1-c3a21fb47e0a

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k)
    [Fintype {x : Red L // x ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withKer L, F P = ∑ x, F (up L q x) := by
  haveI : Fintype {P : Pair k n // P.ker = L} := Fintype.ofEquiv _ (kerEquiv L q)
  rw [Finset.sum_subtype (withKer L) (p := fun P => P.ker = L) (fun _ => mem_withKer)]
  exact ((kerEquiv L q).sum_comp fun P => F P.1).symm
end GlobalTheory.LatPair
