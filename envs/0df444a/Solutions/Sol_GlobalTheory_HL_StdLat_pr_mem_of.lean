-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.pr_mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:28.887887+00:00
-- url     : https://prove2.me/submissions/9b263fc1-d25d-4433-a2c6-7a59548b1989

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_e
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_es
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_pr_r
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_decomp
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_mem
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm} {r : ℕ} {e es : Fin r → Fin n → E} (hH : IsHerm L Hm)
  (hee : ∀ i j, hf L Hm (e i) (e j) = 0) (hss : ∀ i j, hf L Hm (es i) (es j) = 0)
  (hes : ∀ i j, hf L Hm (e i) (es j) = if i = j then 1 else 0)
include hH hes
variable {A : Submodule L.O (Fin n → E)}
variable (hXA : ∀ x ∈ Submodule.span E (Set.range e), x ∈ A)
  (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0)
  (hd : ∀ y, (∀ j, hf L Hm y (e j) = 0) → ((∀ x ∈ A, hf L Hm x y ∈ L.O) ↔ y ∈ A))
include hee hss hXA hAp hd
namespace GlobalTheory.HL.StdLat
theorem _root_.solution (y : Fin n → E)
    (h : ∀ x ∈ A, (∀ j, hf L Hm x (es j) = 0) → hf L Hm x y ∈ L.O) : pr L Hm e es y ∈ A := by
  refine (hd _ (pr_e hH hee hes y)).1 fun x hx => ?_
  rw [hf_decomp hH hee hss hes]
  simp only [pr_e hH hee hes, pr_es hss hes, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  rw [hf_pr_r (pr_e hH hee hes x) (pr_es hss hes x), hf_pr_r (pr_e hH hee hes x) (pr_es hss hes x)]
  exact h _ (pr_mem hXA hAp hx) (pr_es hss hes x)
end GlobalTheory.HL.StdLat
