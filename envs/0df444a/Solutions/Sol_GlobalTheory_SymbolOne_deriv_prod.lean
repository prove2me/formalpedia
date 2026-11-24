-- Prove2me | solution 1 for GlobalTheory.SymbolOne.deriv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:50.04634+00:00
-- url     : https://prove2.me/submissions/8fe44eb0-2696-443b-b177-7a4ee6925801

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolOne
variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace GlobalTheory.SymbolOne
theorem _root_.solution (D : Derivation k A A) (f : ι → A) (s : Finset ι) :
    D (∏ l ∈ s, f l) = ∑ j ∈ s, (∏ l ∈ s.erase j, f l) * D (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, ih, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij, Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)),
      mul_assoc]
end GlobalTheory.SymbolOne
