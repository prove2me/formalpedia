-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.moves_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:09.726384+00:00
-- url     : https://prove2.me/submissions/e95b7bf1-0962-4835-8bbc-b055d087c285

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
import Theorems.Thm_GlobalTheory_InnerDatumAct_datum_ext
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
theorem _root_.solution {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) {d d₁ d₂ : Datum P}
    (h₁ : Datum.Moves g d d₁) (h₂ : Datum.Moves g d d₂) : d₁ = d₂ := by
  refine datum_ext ?_ ?_ ?_
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e)
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e)
  · ext ⟨w', w⟩
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ w'
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e' : (y' : V) = g (g.symm y') := by simp
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y' ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y
      e' e).symm.trans (h₂.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y'
        ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e' e)
end GlobalTheory.InnerDatumAct
