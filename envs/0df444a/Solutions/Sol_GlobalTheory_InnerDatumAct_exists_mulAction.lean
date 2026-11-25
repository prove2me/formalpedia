-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.exists_mulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:15.065863+00:00
-- url     : https://prove2.me/submissions/e1d5e720-a91e-4eb6-8243-2f0b0e9e7178

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
import Theorems.Thm_GlobalTheory_InnerDatumAct_inU_of_mem
import Theorems.Thm_GlobalTheory_InnerDatumAct_moves_act
import Theorems.Thm_GlobalTheory_InnerDatumAct_moves_unique
import Theorems.Thm_GlobalTheory_InnerDatumAct_moves_one
import Theorems.Thm_GlobalTheory_InnerDatumAct_moves_comp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.InnerDatumAct
open Formalism.MainNotions.S.LocNG
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.InnerDatumAct
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _
  let sm : P.UW0 → Datum P → Datum P := fun g d => act (inU_of_mem g.2) d
  have key : ∀ (g : P.UW0) d d', Datum.Moves g.1 d d' ↔ sm g d = d' := fun g d d' =>
    ⟨fun h => moves_unique (inU_of_mem g.2) (moves_act _ d) h, fun h => h ▸ moves_act _ d⟩
  letI act' : MulAction P.UW0 (Datum P) :=
    { smul := sm
      one_smul := fun d => (key 1 d d).1 (moves_one d)
      mul_smul := fun g g' d => (key (g * g') d _).1
        (moves_comp (inU_of_mem g'.2) ((key g' d _).2 rfl) ((key g _ _).2 rfl)) }
  refine ⟨act', key, fun d g => ?_⟩
  have hS : Datum.Stab d = (MulAction.stabilizer P.UW0 d).map P.UW0.subtype := by
    unfold Datum.Stab
    have hset : {g | g ∈ P.UW0 ∧ Datum.Moves g d d} =
        ((MulAction.stabilizer P.UW0 d).map P.UW0.subtype : Set (V ≃ₗ[E] V)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map, MulAction.mem_stabilizer_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, hg⟩, (key ⟨g, hg⟩ d d).1 hm, rfl⟩
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, (key g' d d).2 hg'⟩
    rw [hset, Subgroup.closure_eq]
  rw [hS, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := Subtype.ext he
    subst this
    exact MulAction.mem_stabilizer_iff.1 hg'
  · intro h
    exact ⟨g, MulAction.mem_stabilizer_iff.2 h, rfl⟩
end GlobalTheory.InnerDatumAct
