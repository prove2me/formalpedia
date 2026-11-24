-- Prove2me | solution 1 for GlobalTheory.RowLev.psi_mem_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:37.807295+00:00
-- url     : https://prove2.me/submissions/3108187e-083a-4967-a060-1f49cb2c2274

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_csGlob_int
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
theorem _root_.solution (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) (a : 𝓞 E) :
    psi F E a ∈ 𝔞.map (psi F E) ↔ a ∈ 𝔞 := by
  refine ⟨fun ha => ?_, fun ha => Ideal.mem_map_of_mem _ ha⟩
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h𝔟0 : 𝔟 ≠ 0 := by
    rintro rfl
    rw [mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at h𝔟
    exact hc0 h𝔟
  have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h0 => hc0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))
  have key : Ideal.span {a} * 𝔟 ≤ 𝔞 * 𝔟 := by
    rw [← h𝔟, Ideal.span_singleton_mul_le_iff]
    intro b hb
    have h1 : psi F E (a * b) ∈ Ideal.span {psi F E c} := by
      have h2 : psi F E (a * b) ∈ (𝔞 * 𝔟).map (psi F E) := by
        rw [map_mul, Ideal.map_mul]
        exact Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ hb)
      rwa [← h𝔟, Ideal.map_span, Set.image_singleton] at h2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
    have hpsi : ∀ z : 𝓞 E, ((psi F E z : IntAf F E) : E ⊗[F] Af F) =
        inclE (F := F) (Af F) (algebraMap (𝓞 E) E z) := fun _ => rfl
    have e1 := congrArg (fun z : IntAf F E => (z : E ⊗[F] Af F)) hs
    simp only [Subring.coe_mul, hpsi] at e1
    have hq : inclE (F := F) (Af F) (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) =
        (s : E ⊗[F] Af F) := by
      have hu : IsUnit (inclE (F := F) (Af F) (algebraMap (𝓞 E) E c)) := (IsUnit.mk0 _ hcE).map _
      apply hu.mul_right_cancel
      rw [e1, ← map_mul, div_mul_cancel₀ _ hcE]
    have hint : IsIntegral ℤ (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) :=
      Formalism.UG.P.csGlob_int (F := F) _ (by rw [hq]; exact s.2)
    have hint' : algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c ∈ integralClosure ℤ E := hint
    obtain ⟨k, hk⟩ : ∃ k : 𝓞 E,
        algebraMap (𝓞 E) E k = algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c :=
      ⟨⟨_, hint'⟩, rfl⟩
    refine Ideal.mem_span_singleton'.2 ⟨k, RingOfIntegers.coe_injective ?_⟩
    rw [map_mul, hk]
    exact div_mul_cancel₀ _ hcE
  rw [← Ideal.dvd_iff_le, mul_dvd_mul_iff_right h𝔟0, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem] at key
  exact key
end GlobalTheory.RowLev
