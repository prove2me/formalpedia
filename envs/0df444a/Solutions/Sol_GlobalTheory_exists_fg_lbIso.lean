-- Prove2me | solution 1 for GlobalTheory.exists_fg_lbIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:54:53.335553+00:00
-- url     : https://prove2.me/submissions/724ea32d-d766-467c-b45a-00c8685a487e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_exists_lbIso_of_isLimit
import Theorems.Thm_GlobalTheory_FGAbove_isFiltered
import Theorems.Thm_GlobalTheory_isAffineHom_baseChangeMap
import Theorems.Thm_GlobalTheory_nonempty_isLimit_baseChange

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
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
namespace GlobalTheory
theorem _root_.solution [QuasiCompact pB] [QuasiSeparated pB] (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (baseChangeMap pB R₀.val)) (N.pull (baseChangeMap pB R₀.val))) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧
      LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR)))
        (N.pull (baseChangeMap pB (Subalgebra.inclusion hR))) := by
  have q₁ : QuasiCompact (pullback.snd pB (spMap (algebraMap k R₀))) :=
    quasiCompact_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have q₂ : QuasiSeparated (pullback.snd pB (spMap (algebraMap k R₀))) :=
    quasiSeparated_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have h₁ : CompactSpace ↥(pullback pB (spMap (algebraMap k R₀))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd pB (spMap (algebraMap k R₀)))
  have h₂ : QuasiSeparatedSpace ↥(pullback pB (spMap (algebraMap k R₀))) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd pB (spMap (algebraMap k R₀)))
  have := FGAbove.isFiltered h
  obtain ⟨hc⟩ := nonempty_isLimit_baseChange pB h
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom ((baseChangeDiagram R₀ pB).map f) :=
    fun _ => isAffineHom_baseChangeMap pB _
  have : CompactSpace ((baseChangeDiagram R₀ pB).obj (.op ⟨R₀, h, le_rfl⟩)) := h₁
  have : QuasiSeparatedSpace ((baseChangeDiagram R₀ pB).obj (.op ⟨R₀, h, le_rfl⟩)) := h₂
  obtain ⟨R, f, hR⟩ := exists_lbIso_of_isLimit _ _ _ hc (i := .op ⟨R₀, h, le_rfl⟩) M N hM hN H
  exact ⟨R.unop.1, R.unop.2.2, R.unop.2.1, hR⟩
end GlobalTheory
