-- Prove2me | solution 1 for GlobalTheory.IsLatticeFrame.finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:40.649462+00:00
-- url     : https://prove2.me/submissions/fe2b7647-5bf4-42e1-9f50-1ae30334a376

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
open GlobalTheory.IsLatticeFrame
variable {A : Submodule (𝓞 K) V} {ι κ : Type*} {e : ι → V}
namespace GlobalTheory.IsLatticeFrame
theorem _root_.solution (he : IsLatticeFrame A e) (hA : A.FG) :
    Finite (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A) :=
  Nat.finite_of_card_ne_zero (he.relIndex_ne_zero hA)
end GlobalTheory.IsLatticeFrame
