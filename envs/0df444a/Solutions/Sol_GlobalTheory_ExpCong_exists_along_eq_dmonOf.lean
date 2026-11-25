-- Prove2me | solution 1 for GlobalTheory.ExpCong.exists_along_eq_dmonOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:29.584686+00:00
-- url     : https://prove2.me/submissions/4605f7b1-8d59-4037-83d5-6c8a46bf827d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Theorems.Thm_GlobalTheory_ExpCong_exists_grouped_of_sublist
import Theorems.Thm_GlobalTheory_ExpCong_dmonOf_eq_along
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.ExpCong
variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
namespace GlobalTheory.ExpCong
theorem _root_.solution (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by
  obtain ⟨m', hm'⟩ := exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse
    (by simpa using hv.reverse)
  refine ⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩
  rw [dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]
end GlobalTheory.ExpCong
