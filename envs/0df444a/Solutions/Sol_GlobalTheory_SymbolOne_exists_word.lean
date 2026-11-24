-- Prove2me | solution 1 for GlobalTheory.SymbolOne.exists_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:51.0828+00:00
-- url     : https://prove2.me/submissions/665ac9c5-78d6-4338-a09e-443c1da18591

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
namespace GlobalTheory.SymbolOne
theorem _root_.solution {ι A : Type} [DecidableEq ι] (D : ι → A → A) (m : ι → ℕ) (L : List ι) :
    ∃ w : List ι, (∀ l, w.count l = L.count l * m l) ∧
      ∀ f, L.foldr (fun l g => (D l)^[m l] g) f = w.foldl (fun g l => D l g) f := by
  induction L with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons j L ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨w ++ List.replicate (m j) j, fun l => ?_, fun f => ?_⟩
    · rw [List.count_append, h1, List.count_replicate, List.count_cons]
      by_cases h : j = l
      · subst h; simp [add_mul]
      · simp [h]
    · rw [List.foldr_cons, List.foldl_append, h2]
      generalize w.foldl (fun g l => D l g) f = x
      generalize m j = n
      induction n generalizing x with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply, ih]
end GlobalTheory.SymbolOne
