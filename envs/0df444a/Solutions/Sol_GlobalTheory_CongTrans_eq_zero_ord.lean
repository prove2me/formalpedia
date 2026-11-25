-- Prove2me | solution 1 for GlobalTheory.CongTrans.eq_zero_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:51.480596+00:00
-- url     : https://prove2.me/submissions/6d5d75fb-4ddc-4991-8859-8c1e00882e92

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_eq_zero_int
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : E)
    (h : ∀ n, ∃ w ∈ L.O, x = algebraMap F E ϖ ^ n * w) : x = 0 := by
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hx : x ∈ L.O := by
    obtain ⟨w, hw, rfl⟩ := h 0
    simpa using hw
  have tr : ∀ b ∈ L.O, x * b + L.cj (x * b) = 0 := by
    intro b hb
    obtain ⟨t, ht⟩ := exists_trace L (L.O.mul_mem hx hb)
    have : t = 0 := eq_zero_int hϖ t fun n => by
      obtain ⟨w, hw, hxw⟩ := h n
      obtain ⟨u, hu⟩ := exists_trace L (L.O.mul_mem hw hb)
      refine ⟨u, Subtype.ext (algebraMap_inj L ?_)⟩
      rw [← ht, Subring.coe_mul, Subring.coe_pow, map_mul (algebraMap F E), map_pow, ← hu, hxw]
      simp only [map_mul, map_pow, AlgEquiv.commutes]
      ring
    rw [ht, this]; simp
  have h1 := tr 1 L.O.one_mem
  have h2 := tr _ (cj_mem L hω)
  simp only [map_mul, L.cj_cj, mul_one] at h1 h2
  linear_combination (-x) * hωe + e * ω * h1 - e * h2
end GlobalTheory.CongTrans
