-- Prove2me | solution 1 for GlobalTheory.HL.PlacesInt.integers_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:22.936641+00:00
-- url     : https://prove2.me/submissions/955e0f83-9c9d-4259-834f-54abe8b84d73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_int_iff
import Theorems.Thm_GlobalTheory_HL_PlacesInt_resQ_eq_absNorm
import Theorems.Thm_GlobalTheory_HL_PlacesInt_exists_trace_norm
import Theorems.Thm_GlobalTheory_HL_PlacesInt_isIntegral_of_quad
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_O_iff

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.HL.PlacesInt
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), (∀ x : E, (∀ p, (A.loc p).ιE x ∈ (A.L p).O) ↔ ∃ o : 𝓞 E, (o : E) = x) ∧ (∀ x : E, {p | (A.loc p).ιE x ∉ (A.L p).O}.Finite) ∧ (∀ (x : F) p, (A.loc p).ιF x ∈ 𝒪[(A.loc p).Fp] ↔ p.valuation F x ≤ 1) ∧ ∀ p (ϖ : 𝒪[(A.loc p).Fp]), Irreducible ϖ → resQ ϖ = Ideal.absNorm p.asIdeal := by
  intro F E _ _ _ _ _ sig A
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun x => ?_, fun x p => mem_int_iff _ x,
    fun p ϖ h => resQ_eq_absNorm _ ϖ h⟩
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    have h := fun p => (mem_O_iff A p x t n ht hn).1 (hx p)
    obtain ⟨t', ht'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t
      (fun p => (h p).1)
    obtain ⟨n', hn'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F n
      (fun p => (h p).2)
    have hi : IsIntegral (𝓞 F) x := isIntegral_of_quad x (sig x) t' n'
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ht', ht])
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hn', hn])
    exact ⟨⟨x, isIntegral_trans (R := ℤ) x hi⟩, rfl⟩
  · rintro ⟨o, rfl⟩ p
    rw [(A.L p).O_def]
    have h : IsIntegral ℤ ((A.loc p).ιE (o : E)) :=
      map_isIntegral_int (A.loc p).ιE o.isIntegral_coe
    exact h.tower_top
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    refine ((HeightOneSpectrum.Support.finite (𝓞 F) t).union
      (HeightOneSpectrum.Support.finite (𝓞 F) n)).subset fun p hp => ?_
    have hp' : ¬ ((A.loc p).ιE x ∈ (A.L p).O) := hp
    rw [mem_O_iff A p x t n ht hn, not_and_or, not_le, not_le] at hp'
    exact hp'
end GlobalTheory.HL.PlacesInt
