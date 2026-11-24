-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.epsV_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:00.118807+00:00
-- url     : https://prove2.me/submissions/6fcb8602-c97a-43f0-99cc-e3a692fffd47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_henselian_locInt
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_prInt_surj
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_mul_eq
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (r : IntAf F E) :
    ∃ s, epsV E v * (1 - g * r) * s = epsV E v := by
  have hH := henselian_locInt (E := E) v g hg
  have h1 := Ideal.mem_jacobson_bot.1 (hH.jac (Ideal.mem_span_singleton_self _)) (-prInt E v r)
  obtain ⟨d, hd⟩ := h1.exists_right_inv
  obtain ⟨s, rfl⟩ := prInt_surj v d
  have h2 := epsV_mul_eq v (x := (1 - (g : IntAf F E) * r) * s) (y := 1) (by
    rw [map_mul, map_sub, map_mul, map_natCast, map_one]; linear_combination hd)
  exact ⟨s, by rw [mul_assoc, h2, mul_one]⟩
end GlobalTheory.RowLev.PrimeIdem
