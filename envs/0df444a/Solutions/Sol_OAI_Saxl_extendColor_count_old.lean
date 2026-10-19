-- Prove2me | solution 1 for OAI.Saxl.extendColor_count_old
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:50:23.09899+00:00
-- url     : https://prove2.me/submissions/a73c5779-27cb-4bfd-abe0-68555f16bbd3

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripExtension.lean:L86-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.extendColor_count_old. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension

-- ---- from OAI.RepresentationTheory.Saxl.StripExtension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma extendColor_apply {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (x : Fin a) : extendColor i c q (i x) = c x := by
  classical
  unfold extendColor
  rw [dite_eq_left ⟨x,rfl⟩]
  congr 1
  exact (Equiv.ofInjective i i.injective).symm_apply_apply x

lemma extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => i x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hx
  · intro x hx y hy hxy
    exact i.injective hxy
  · intro y hy
    have hyj := (Finset.mem_filter.mp hy).2
    have hym : y ∈ Set.range i := by
      by_contra hn
      simp only [extendColor, dite_eq_right hn] at hyj
      exact hj hyj.symm
    obtain ⟨x,rfl⟩ := hym
    refine ⟨x, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hyj

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.extendColor_count_old := @_root_.OAI.Saxl.extendColor_count_old
