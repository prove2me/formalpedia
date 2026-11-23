-- Prove2me | solution 1 for GlobalTheory.HermModel.finrank_eq_of_injective_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:12.368316+00:00
-- url     : https://prove2.me/submissions/6ee19c27-1ad7-4192-9d1c-5f2ec078e0ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermModel
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.HermModel
namespace _root_.GlobalTheory.HermModel
theorem _root_.solution {R K M V : Type} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module R V] [Module K V] [IsScalarTower R K V] (f : M →ₗ[R] V) (hf : Function.Injective f)
    (hspan : Submodule.span K (Set.range f) = ⊤) :
    Module.finrank R M = Module.finrank K V := by
  have hle : Module.rank R M ≤ Module.rank K V := by
    rw [Module.rank_def]
    refine ciSup_le' fun s => ?_
    have hs : LinearIndependent R (f ∘ ((↑) : s.1 → M)) :=
      s.2.map' f (LinearMap.ker_eq_bot.mpr hf)
    exact ((LinearIndependent.iff_fractionRing R K).mp hs).cardinal_le_rank
  have hge : Module.rank K V ≤ Module.rank R M := by
    obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
    have hrank : Module.rank K V = Cardinal.mk s := by
      rw [← rank_top, ← hspan, ← hs_span, rank_span_set hs_li]
    have hpre : ∀ x : s, ∃ m, f m = x.1 := fun x => hs_sub x.2
    choose g hg using hpre
    have hli : LinearIndependent R (f ∘ g) := by
      have : f ∘ g = ((↑) : s → V) := funext hg
      rw [this]
      exact (LinearIndependent.iff_fractionRing R K).mpr hs_li
    rw [hrank]
    exact (LinearIndependent.of_comp f hli).cardinal_le_rank
  unfold Module.finrank
  rw [le_antisymm hle hge]
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
