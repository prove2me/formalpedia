-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.epsV_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:59.294105+00:00
-- url     : https://prove2.me/submissions/7af5d3bc-7e40-4e35-8409-1816af663ca4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_exists_idem
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_henselian_locInt
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_prInt_surj
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_mul_eq
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_idem

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (a : IntAf F E)
    (ha : a * a - a ∈ Ideal.span {(g : IntAf F E)}) :
    ∃ x, epsV E v * (a + g * x) * (epsV E v * (a + g * x)) = epsV E v * (a + g * x) := by
  have := henselian_locInt (E := E) v g hg
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 ha
  obtain ⟨y, hy, hy'⟩ := exists_idem (Ideal.span {(g : LocInt E v)}) (prInt E v a) (by
    rw [← map_mul, ← map_sub, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 hy'
  obtain ⟨x, rfl⟩ := prInt_surj v d
  have h1 : prInt E v (a + g * x) = y := by
    rw [map_add, map_mul, map_natCast, ← hd]; ring
  have h2 := epsV_mul_eq v (x := (a + (g : IntAf F E) * x) * (a + (g : IntAf F E) * x))
    (y := a + (g : IntAf F E) * x) (by rw [map_mul, h1, hy])
  exact ⟨x, by linear_combination h2 + (a + g * x) * (a + g * x) * epsV_idem (E := E) v⟩
end GlobalTheory.RowLev.PrimeIdem
