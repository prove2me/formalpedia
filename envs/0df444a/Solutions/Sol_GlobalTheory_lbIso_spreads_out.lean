-- Prove2me | solution 1 for GlobalTheory.lbIso_spreads_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:25.396291+00:00
-- url     : https://prove2.me/submissions/a68d071a-5be8-4a99-8c0a-80b0c3b3d0d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_exists_fg_lbIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : IntermediateField ℚ ℂ) (B : Scheme.{0}) (pB : B ⟶ Sp k) [QuasiCompact pB]
    [QuasiSeparated pB] (R₀ : Subalgebra k ℂ) (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (j₀ : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R₀)))
    (h₁ : j₀ ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R₀.val.toRingHom)
    (H : LBIso (M.pull j₀) (N.pull j₀)) :
    ∃ (R : Subalgebra k ℂ) (hR : R₀ ≤ R)
      (i : pullback pB (spMap (algebraMap k R)) ⟶ pullback pB (spMap (algebraMap k R₀))), R.FG ∧
      i ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion hR).toRingHom ∧
      LBIso (M.pull i) (N.pull i) := by
  obtain rfl : j₀ = baseChangeMap pB R₀.val :=
    pullback.hom_ext (h₁.trans (baseChangeMap_fst pB _).symm) (h₂.trans (baseChangeMap_snd pB _).symm)
  obtain ⟨R, hR, hfg, hiso⟩ := exists_fg_lbIso pB h M N hM hN H
  exact ⟨R, hR, _, hfg, baseChangeMap_fst pB _, baseChangeMap_snd pB _, hiso⟩
end GlobalTheory
