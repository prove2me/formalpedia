-- Prove2me | solution 1 for GlobalTheory.LocDualInt.pairKO_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:56.033125+00:00
-- url     : https://prove2.me/submissions/c21bf2a9-480d-45fe-82cb-d3b1af8b969f

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.LocDualInt
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {G : Type} [Group G] [TopologicalSpace G]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')
namespace GlobalTheory.LocDualInt
theorem _root_.solution {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t : ↥D.T'}
    (ht : t ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = 0 := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 ht
  rw [map_smul, ← LinearMap.smul_apply, ← map_smul, hx, map_zero, LinearMap.zero_apply]
end GlobalTheory.LocDualInt
