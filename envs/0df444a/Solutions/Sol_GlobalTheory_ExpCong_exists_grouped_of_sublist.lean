-- Prove2me | solution 1 for GlobalTheory.ExpCong.exists_grouped_of_sublist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:58:27.793596+00:00
-- url     : https://prove2.me/submissions/3252cbed-d31b-4450-94bf-80da64df1e97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Theorems.Thm_GlobalTheory_ExpCong_grouped_cons
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
variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)
namespace GlobalTheory.ExpCong
theorem _root_.solution {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by
  classical
  induction L generalizing v with
  | nil => exact ⟨m, by simpa [grouped] using hv⟩
  | cons a L ih =>
    rw [grouped_cons, List.sublist_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv
    obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    rw [List.nodup_cons] at hL
    obtain ⟨m', rfl⟩ := ih hL.2 v₂ h₂
    refine ⟨Function.update m' a n, ?_⟩
    rw [grouped_cons, Function.update_self]
    congr 1
    unfold grouped
    refine List.flatMap_congr fun l hl => ?_
    rw [Function.update_of_ne]
    rintro rfl
    exact hL.1 hl
end GlobalTheory.ExpCong
