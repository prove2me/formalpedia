-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_norm_one_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:28.745707+00:00
-- url     : https://prove2.me/submissions/c617c806-7726-4463-96d8-203e7b83166f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_gram_unit
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (S : Subring E) (σ : E →+* E) (φ : o →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hN : ∀ x ∈ S, ∃ c, x * σ x = φ c)
    (hτ : ∃ τ ∈ S, τ + σ τ = 1) (hU : ∀ u : oˣ, ∃ x ∈ S, x * σ x = φ u)
    {y0 y1 y2 c0 c1 c2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) (hc0 : c0 ∈ S) (hc1 : c1 ∈ S) (hc2 : c2 ∈ S)
    (h : y0 * σ c0 + y1 * σ c1 + y2 * σ c2 = 1) :
    ∃ u0 ∈ S, ∃ u1 ∈ S, ∃ u2 ∈ S, u0 * σ u0 + u1 * σ u1 + u2 * σ u2 = 1 ∧
      u0 * σ y0 + u1 * σ y1 + u2 * σ y2 = 0 := by
  obtain ⟨d0, hd0, d1, hd1, d2, hd2, w, hw, hd⟩ :=
    exists_gram_unit S σ φ hσ hσS hN hτ hy0 hy1 hy2 hc0 hc1 hc2 h
  obtain ⟨x, hx, hxx⟩ := hU hw.unit⁻¹
  have hw1 : φ w * φ (hw.unit⁻¹ : oˣ) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  refine ⟨x * σ (y1 * d2 - y2 * d1), ?_, x * σ (y2 * d0 - y0 * d2), ?_,
    x * σ (y0 * d1 - y1 * d0), ?_, ?_, ?_⟩
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy1 hd2) (S.mul_mem hy2 hd1)))
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy2 hd0) (S.mul_mem hy0 hd2)))
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy0 hd1) (S.mul_mem hy1 hd0)))
  · simp only [map_mul, map_sub, hσ]
    rw [← hd, ← hxx] at hw1
    linear_combination hw1
  · simp only [map_mul, map_sub]
    ring
end GlobalTheory.HL.OrthCompl
