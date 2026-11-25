-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:47.260231+00:00
-- url     : https://prove2.me/submissions/b73026c5-f131-4a7f-88f8-ca58e425ddec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
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
omit [IsLocalRing o]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution [IsArtinianRing E] [IsReduced E] (S : Subring E) [IsPrincipalIdealRing S]
    (hid : ∀ e : E, e * e = e → e ∈ S) {y0 y1 y2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) :
    ∃ d : E, ∃ b0 ∈ S, ∃ b1 ∈ S, ∃ b2 ∈ S, ∃ r0 ∈ S, ∃ r1 ∈ S, ∃ r2 ∈ S,
      y0 = d * b0 ∧ y1 = d * b1 ∧ y2 = d * b2 ∧ b0 * r0 + b1 * r1 + b2 * r2 = 1 := by
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span {(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩})).principal
  have hm : ∀ z ∈ ({(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩} : Set S), ∃ b : S, b * d = z :=
    fun z hz => by
      have := Ideal.subset_span hz
      rw [hd] at this
      exact Ideal.mem_span_singleton'.1 this
  obtain ⟨b0, hb0⟩ := hm ⟨y0, hy0⟩ (by simp)
  obtain ⟨b1, hb1⟩ := hm ⟨y1, hy1⟩ (by simp)
  obtain ⟨b2, hb2⟩ := hm ⟨y2, hy2⟩ (by simp)
  have hdm : d ∈ Ideal.span {(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩} := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨r0, z, hz, hz'⟩ := Ideal.mem_span_insert.1 hdm
  obtain ⟨r1, r2, rfl⟩ := Ideal.mem_span_pair.1 hz
  have e0 : (b0 : E) * d = y0 := congrArg Subtype.val hb0
  have e1 : (b1 : E) * d = y1 := congrArg Subtype.val hb1
  have e2 : (b2 : E) * d = y2 := congrArg Subtype.val hb2
  have e3 : (d : E) = r0 * y0 + (r1 * y1 + r2 * y2) := congrArg Subtype.val hz'
  have : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {(d : E)})
  have hee : e * e = e := he
  obtain ⟨p, hp⟩ : ∃ p, p * (d : E) = e :=
    Ideal.mem_span_singleton'.1 (hI ▸ Ideal.mem_span_singleton_self e)
  obtain ⟨q, hq⟩ : ∃ q, q * e = (d : E) :=
    Ideal.mem_span_singleton'.1 (hI ▸ Ideal.mem_span_singleton_self (d : E))
  have hde : (d : E) * e = d := by rw [← hq, mul_assoc, hee]
  have heS := hid e hee
  have h1e := S.sub_mem S.one_mem heS
  refine ⟨d, e * b0 + (1 - e), S.add_mem (S.mul_mem heS b0.2) h1e, e * b1, S.mul_mem heS b1.2,
    e * b2, S.mul_mem heS b2.2, e * r0 + (1 - e), S.add_mem (S.mul_mem heS r0.2) h1e,
    r1, r1.2, r2, r2.2, ?_, ?_, ?_, ?_⟩
  · linear_combination -e0 - (b0 - 1 : E) * hde
  · linear_combination -e1 - (b1 : E) * hde
  · linear_combination -e2 - (b2 : E) * hde
  · have k : e * (b0 * r0 + b1 * r1 + b2 * r2) = e := by
      rw [← hp]
      linear_combination p * r0 * e0 + p * r1 * e1 + p * r2 * e2 - p * e3
    linear_combination k + ((b0 : E) * r0 - b0 - r0 + 1) * hee
end GlobalTheory.HL.OrthCompl
