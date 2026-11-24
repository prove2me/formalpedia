-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.henselian_locInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:46.065016+00:00
-- url     : https://prove2.me/submissions/70efe0fb-772a-44fe-bc0a-54237479b0de

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_henselian_of_closure
import Theorems.Thm_GlobalTheory_CNorm_isAdicComplete_and_card_quotient_adicCompletionIntegers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open GlobalTheory.RowLev.PrimeIdem
open Formalism.UG Formalism.UG.P
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    HenselianRing (LocInt E v) (Ideal.span {(g : LocInt E v)}) := by
  have hlt : Valued.v ((g : v.adicCompletionIntegers F) : v.adicCompletion F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) g,
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hg
  have := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ hlt
  let φ : v.adicCompletionIntegers F →+* LocInt E v :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)).toRingHom.comp
      (v.adicCompletionIntegers F).subtype).codRestrict _ fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  let ψ : 𝓞 E →+* LocInt E v :=
    ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y =>
      Subring.subset_closure (Or.inl ⟨⟨_, y, rfl⟩, rfl⟩)
  have h := henselian_of_closure (g : v.adicCompletionIntegers F) φ ψ fun T h1 h2 x => by
    have hle : LocInt E v ≤ T.map (LocInt E v).subtype := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
      · exact ⟨_, h2 a, rfl⟩
      · exact ⟨_, h1 y, rfl⟩
    obtain ⟨y, hy, e⟩ := hle x.2
    rwa [← Subtype.ext e]
  rwa [map_natCast] at h
end GlobalTheory.RowLev.PrimeIdem
