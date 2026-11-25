-- Prove2me | solution 1 for GlobalTheory.LocDualInt.cupMod_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:13.824898+00:00
-- url     : https://prove2.me/submissions/e756d38d-27c1-4508-90b8-cf083ed851d6

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
import Theorems.Thm_GlobalTheory_LocDualInt_mk_qlift
import Theorems.Thm_GlobalTheory_LocDualInt_pairKO_eq_of_sub_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocDualInt.mk_qlift

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
theorem _root_.solution {c : G → VT ⧸ D.T} {a : O} {r m n : ℕ} (hc : ∀ g, a ^ r • c g = 0)
    (hrm : r ≤ m) (hmn : m ≤ n) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    cupMod D c a m (fun g => Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z g)) =
      cupMod D c a n z := by
  funext p
  refine pairKO_eq_of_sub_mem D (hc p.1) ?_
  rw [← map_sub]
  refine powSub_stable _ a r p.1 _ (powSub_anti a hrm ?_)
  apply (Submodule.Quotient.eq _).1
  have e : (Submodule.Quotient.mk (qlift (z p.2)) : ↥D.T' ⧸ powSub (M := ↥D.T') a m) =
      Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z p.2) := by
    conv_rhs => rw [← mk_qlift (z p.2)]
    rfl
  rw [e, mk_qlift]
end GlobalTheory.LocDualInt
