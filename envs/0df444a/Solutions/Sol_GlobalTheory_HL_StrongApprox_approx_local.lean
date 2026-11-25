-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.approx_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:50.406345+00:00
-- url     : https://prove2.me/submissions/5f553119-8e25-4df9-a5c9-5816fab104a0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_int_of
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_int_iff
import Theorems.Thm_GlobalTheory_HL_PlacesInt_val_le_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (T : LocAt F E sig p) (z : T.Fp) (hz : valuation T.Fp z ≤ 1) (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, valuation T.Fp (z - T.ιF (algebraMap (𝓞 F) F a)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := by
  haveI := T.lf
  have hhK : algebraMap (𝓞 F) F h ≠ 0 := by simpa using hh
  have hh0 : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) ≠ 0 := by simpa using hhK
  have hn : {x : T.Fp | valuation T.Fp (x - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))} ∈ nhds z :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hh0, fun x hx => hx⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := hk
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← PlacesInt.mem_int_iff T]
    have e : T.ιF k = (T.ιF k - z) + z := by ring
    show valuation T.Fp (T.ιF k) ≤ 1
    rw [e]
    exact (valuation T.Fp).map_add_le (hk'.le.trans (int_of T h)) hz
  have hpv : p.valuation F (algebraMap (𝓞 F) F h) ≠ 0 := by simpa using hhK
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hpv)
  refine ⟨a, ?_⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - k)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) :=
    (PlacesInt.val_le_iff T _ _).2 ha.le
  have e : z - T.ιF (algebraMap (𝓞 F) F a) = -(T.ιF k - z) - T.ιF (algebraMap (𝓞 F) F a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine ((valuation T.Fp).map_sub _ _).trans (max_le ?_ ha')
  rw [Valuation.map_neg]; exact hk'.le
end GlobalTheory.HL.StrongApprox
