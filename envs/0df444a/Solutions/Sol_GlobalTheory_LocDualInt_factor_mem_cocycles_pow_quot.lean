-- Prove2me | solution 1 for GlobalTheory.LocDualInt.factor_mem_cocycles_pow_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:03:38.320849+00:00
-- url     : https://prove2.me/submissions/4d29b026-7561-40d3-887d-0a896d136250

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
import Theorems.Thm_GlobalTheory_LocDualInt_continuous_factor

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
open GlobalTheory GlobalTheory.LocDualInt
variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]
namespace GlobalTheory.LocDualInt
theorem _root_.solution (ρ : Representation O G M) (a : O) {m n : ℕ} (h : m ≤ n)
    {z : G → M ⧸ powSub (M := M) a n} (hz : z ∈ Z1 (quotRep ρ a n)) :
    (fun g => Submodule.factor (powSub_anti (M := M) a h) (z g)) ∈ Z1 (quotRep ρ a m) := by
  refine ⟨(continuous_factor a h).comp hz.1, fun g g' => ?_⟩
  show Submodule.factor _ (z (g * g')) = Submodule.factor _ (z g) +
    quotRep ρ a m g (Submodule.factor (powSub_anti (M := M) a h) (z g'))
  rw [hz.2 g g', map_add]
  congr 1
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (z g')
  rw [← hy]
  rfl
end GlobalTheory.LocDualInt
