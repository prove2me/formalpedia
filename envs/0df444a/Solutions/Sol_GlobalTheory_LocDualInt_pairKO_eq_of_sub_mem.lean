-- Prove2me | solution 1 for GlobalTheory.LocDualInt.pairKO_eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:57.926817+00:00
-- url     : https://prove2.me/submissions/1b45b965-0f6b-48f8-88c2-82c1e5899998

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
import Theorems.Thm_GlobalTheory_LocDualInt_pairKO_eq_zero_of_mem

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
theorem _root_.solution {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t t' : ↥D.T'}
    (ht : t - t' ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = pairKO D.bT D.T x t' := by
  rw [← sub_eq_zero, ← map_sub]
  exact pairKO_eq_zero_of_mem D hx ht
end GlobalTheory.LocDualInt
