-- Prove2me | solution 1 for GlobalTheory.RowLev.exists_map_psi_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:47:01.260605+00:00
-- url     : https://prove2.me/submissions/e097ef04-c53d-42ba-b757-8735f426c804

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Theorems.Thm_GlobalTheory_RowLev_map_eq_span_of_idem
import Theorems.Thm_GlobalTheory_RowLev_exists_idem_intAd
import Theorems.Thm_GlobalTheory_RowLev_intAdIncl_jacobson
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev
theorem _root_.solution (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) :
    ∃ t : IntAf F E, IsUnit (t : E ⊗[F] Af F) ∧ 𝔞.map (psi F E) = Ideal.span {t} := by
  have hN0 : Ideal.absNorm 𝔞 ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNmem : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
  have hNne : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  have hI : Ideal.span {((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E)} * 𝔞 ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hNne, h⟩
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (J := 𝔞)
    (Ideal.mul_le.2 fun _ _ _ hy => Ideal.mul_mem_left _ _ hy) hI
  obtain ⟨μ₀, hidem, hjac⟩ := exists_idem_intAd (F := F) ((Ideal.absNorm 𝔞 : ℕ) : intAd F)
  obtain ⟨t, ht⟩ := map_eq_span_of_idem (psi F E) 𝔞 (IsNoetherian.noetherian 𝔞) _ a hNmem ha
    (intAdIncl F E μ₀)
    (by simpa [map_mul] using congrArg (intAdIncl F E) hidem)
    (by simpa [map_mul, map_sub] using intAdIncl_jacobson (E := E) hjac)
  refine ⟨t, ?_, ht⟩
  have hmem : psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ Ideal.span {t} := by
    rw [← ht]
    exact Ideal.mem_map_of_mem _ hNmem
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
  have hu : IsUnit ((psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) : IntAf F E) : E ⊗[F] Af F) := by
    rw [map_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap F (E ⊗[F] Af F))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN0)).map _
  rw [← hs, Subring.coe_mul] at hu
  exact isUnit_of_mul_isUnit_right hu
end GlobalTheory.RowLev
