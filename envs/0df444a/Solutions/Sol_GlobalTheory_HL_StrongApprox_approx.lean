-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:09.401953+00:00
-- url     : https://prove2.me/submissions/25725877-8d44-479b-ad4f-9247fc14b81f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_int_of
import Theorems.Thm_GlobalTheory_HL_StrongApprox_approx_local
import Theorems.Thm_GlobalTheory_HL_PlacesInt_val_le_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (z : ∀ p, (A.loc p).Fp) (hz : ∀ p, valuation (A.loc p).Fp (z p) ≤ 1)
    (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, ∀ p, valuation (A.loc p).Fp (z p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) ≤
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) := by
  have hT : {p : HeightOneSpectrum (𝓞 F) | p.asIdeal ∣ Ideal.span {h}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hh)
  choose a0 ha0 using fun p => approx_local (A.loc p) (z p) (hz p) h hh
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hT.toFinset) (fun p => p.asIdeal)
    (fun p => multiplicity p.asIdeal (Ideal.span {h})) (fun p _ => p.prime)
    (fun p _ q _ hpq e => hpq (HeightOneSpectrum.ext e)) (fun p => a0 p.1)
  refine ⟨a, fun p => ?_⟩
  by_cases hp : p ∈ hT.toFinset
  · have h1 := ha p hp
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity p hh,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)] at h1
    have h2 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h1
    have e : z p - (A.loc p).ιF (algebraMap (𝓞 F) F a) =
        (z p - (A.loc p).ιF (algebraMap (𝓞 F) F (a0 p))) - (A.loc p).ιF (algebraMap (𝓞 F) F (a - a0 p)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (ha0 p) h2)
  · have h1 : p.intValuation h = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hp ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    have h2 : p.valuation F (algebraMap (𝓞 F) F 1) ≤ p.valuation F (algebraMap (𝓞 F) F h) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, h1, map_one]
    have h3 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h2
    rw [map_one, map_one, map_one] at h3
    refine le_trans ?_ h3
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (hz p) (int_of _ a))
end GlobalTheory.HL.StrongApprox
