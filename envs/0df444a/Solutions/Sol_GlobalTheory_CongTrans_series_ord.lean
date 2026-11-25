-- Prove2me | solution 1 for GlobalTheory.CongTrans.series_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:39:56.087906+00:00
-- url     : https://prove2.me/submissions/1f6d20f6-94d4-4464-9a43-a3d9db192039

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_series_int
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
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
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
variable [CharZero F] (L : LocE F E)
namespace GlobalTheory.CongTrans
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : ℕ → E) (ha : ∀ k, a k ∈ L.O) :
    ∃ l : E, ∀ n, ∃ w ∈ L.O,
      l = ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * a k + algebraMap F E ϖ ^ n * w := by
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have hco : ∀ x ∈ L.O, ∃ s r : 𝒪[F], x = (algebraMap F E s * ω - algebraMap F E r) * e := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_trace L hx
    obtain ⟨r, hr⟩ := exists_trace L (L.O.mul_mem hx (cj_mem L hω))
    simp only [map_mul, L.cj_cj] at hr
    refine ⟨s, r, ?_⟩
    rw [← hs, ← hr]
    linear_combination (-x) * hωe
  choose s r hsr using fun k => hco (a k) (ha k)
  obtain ⟨l₁, h₁⟩ := series_int hϖ s
  obtain ⟨l₂, h₂⟩ := series_int hϖ r
  refine ⟨(algebraMap F E l₁ * ω - algebraMap F E l₂) * e, fun n => ?_⟩
  obtain ⟨w₁, hw₁⟩ := h₁ n
  obtain ⟨w₂, hw₂⟩ := h₂ n
  refine ⟨(algebraMap F E w₁ * ω - algebraMap F E w₂) * e,
    L.O.mul_mem (L.O.sub_mem (L.O.mul_mem (hint _) hω) (hint _)) he, ?_⟩
  have e1 : ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * a k
      = ((∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * algebraMap F E (s k)) * ω
        - ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * algebraMap F E (r k)) * e := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsr k]; ring
  rw [e1, hw₁, hw₂]
  push_cast
  ring
end GlobalTheory.CongTrans
