-- Prove2me | solution 1 for GlobalTheory.RowLev.exists_prime_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:42.160628+00:00
-- url     : https://prove2.me/submissions/0467d7ae-d9b8-44c3-9b0b-7f774447882d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_exists_idem_prime
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_idem
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_lift
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_unit
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_one_sub_epsV_mem
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_mem
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_extId_eq_map
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_csDual_sig_incl
import Theorems.Thm_Formalism_UG_P_csDual_sig_mem
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_approx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open PrimeIdem Formalism.UG Formalism.UG.P
namespace GlobalTheory.RowLev
theorem _root_.solution : ∀ (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E)), ∃ ε : IntAf I.F I.E, ε * ε = ε ∧ 1 - ε ∈ extId I w.asIdeal ∧ (∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ extId I u.asIdeal) ∧ (∀ z : IntAf I.F I.E, z ∉ extId I w.asIdeal → ∃ t : IntAf I.F I.E, z * t * ε = ε) ∧ (¬ IsConj I w w → (ε : (I.E ⊗[I.F] Af I.F)) * Formalism.UG.sigR I.cm.sig (Af I.F) ε = 0) := by
  intro I w
  set g : ℕ := Ideal.absNorm w.asIdeal with hgdef
  have hg0 : g ≠ 0 := by rw [hgdef, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hgw : (g : 𝓞 I.E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hun : ∀ u : HeightOneSpectrum (𝓞 I.E), (g : 𝓞 I.F) ∈ (u.under (𝓞 I.F)).asIdeal ↔ (g : 𝓞 I.E) ∈ u.asIdeal :=
    fun u => by
      rw [← map_natCast (algebraMap (𝓞 I.F) (𝓞 I.E)) g]; rfl
  have hgv := (hun w).2 hgw
  obtain ⟨ε, h1, h2, h3, h4, h5, h6⟩ := exists_idem_prime (Inhab.psi I.F I.E) (g : 𝓞 I.E) (by exact_mod_cast hg0)
    (epsV I.E (w.under (𝓞 I.F))) (epsV_idem _)
    (by rw [map_natCast]; exact epsV_lift _ g hgv) (by rw [map_natCast]; exact epsV_unit _ g hgv)
    (by rw [map_natCast]; exact Inhab.exists_approx hg0) w hgw (one_sub_epsV_mem w)
  have h7 : ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ u.asIdeal.map (Inhab.psi I.F I.E) := fun u hu => by
    by_cases h : u.under (𝓞 I.F) = w.under (𝓞 I.F)
    · exact h4 u hu ((hun u).1 (h ▸ hgv))
    · rw [← h2]; exact Ideal.mul_mem_right _ _ (epsV_mem _ u h)
  simp only [extId_eq_map]
  refine ⟨ε, h1, h3, h7, h5, fun hw => ?_⟩
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  let w' : HeightOneSpectrum (𝓞 I.E) := w.comap st fun a => ⟨st a, hst2 a⟩
  have hw' : ∀ a, a ∈ w'.asIdeal ↔ st a ∈ w.asIdeal := fun a => Iff.rfl
  have hne : w' ≠ w := fun e => hw fun a b hab => by
    have : b = st a := RingOfIntegers.ext hab
    rw [this, ← hw', e]
  let σ : IntAf I.F I.E →+* IntAf I.F I.E :=
    ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun y => csDual_sig_mem _ y.2
  have hσ : w'.asIdeal.map (Inhab.psi I.F I.E) ≤ (w.asIdeal.map (Inhab.psi I.F I.E)).comap σ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have e : σ (Inhab.psi I.F I.E a) = Inhab.psi I.F I.E (st a) := Subtype.ext (csDual_sig_incl _ _)
    show σ (Inhab.psi I.F I.E a) ∈ w.asIdeal.map (Inhab.psi I.F I.E)
    rw [e]
    exact Ideal.mem_map_of_mem _ ((hw' a).1 ha)
  exact congrArg Subtype.val (h6 (σ ε) (hσ (h7 w' hne)) (by rw [← map_mul, h1]))
end GlobalTheory.RowLev
