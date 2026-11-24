-- Prove2me | solution 1 for GlobalTheory.RowLev.extId_mul_sup_natCast_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:38.536842+00:00
-- url     : https://prove2.me/submissions/5696d5f5-27e0-45cf-86a9-4dde7c107fc5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtIdMulSupNatCastConj
import Theorems.Thm_GlobalTheory_RowLev_extId_eq_map_psi
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_RowLev_intAf_approx_inter_unit_conj
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
namespace GlobalTheory.RowLev
theorem _root_.solution : ∀ (I : AutInst), (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), extId I (𝔞 * 𝔟) = extId I 𝔞 * extId I 𝔟) ∧ (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), 𝔞 ⊔ 𝔟 = ⊤ → extId I 𝔞 ⊔ extId I 𝔟 = ⊤) ∧ (∀ m : ℕ, extId I (Ideal.span {(m : 𝓞 I.E)}) = Ideal.span {(m : IntAf I.F I.E)}) ∧ (∀ w : HeightOneSpectrum (𝓞 I.E), ∃ w', IsConj I w w') ∧ (∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w' w) ∧ (∀ w w' w'' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w w'' → w' = w'') ∧ ∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → ∀ z ∈ extId I w.asIdeal, ∃ z' ∈ extId I w'.asIdeal, (z' : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.sigR I.cm.sig (Af I.F) z := by
  intro I
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  have hsig : ∀ z ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) z ∈ IntAf I.F I.E :=
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2
  refine ⟨fun a b => ?_, fun a b h => ?_, fun m => ?_, fun w => ?_, fun w w' h => ?_,
    fun w w' w'' h h' => ?_, fun w w' h z hz => ?_⟩
  · simp only [extId_eq_map_psi, Ideal.map_mul]
  · simp only [extId_eq_map_psi, ← Ideal.map_sup, h, Ideal.map_top]
  · rw [extId_eq_map_psi, Ideal.map_span, Set.image_singleton, map_natCast]
  · refine ⟨w.comap st hsurj, fun a b hab => ?_⟩
    have : b = st a := RingOfIntegers.ext hab
    subst this
    show _ ↔ st (st a) ∈ w.asIdeal
    rw [hst2]
  · intro a b hab
    exact (h b a (by rw [hab, star_star])).symm
  · refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    have e : (b : I.E) = star (st b : I.E) := by rw [hst, star_star]
    exact (h (st b) b e).symm.trans (h' (st b) b e)
  · have key : (⟨_, hsig z z.2⟩ : IntAf I.F I.E) ∈ extId I w'.asIdeal := by
      unfold extId at hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, e⟩ := hx
        refine Ideal.subset_span ⟨st a, (h a (st a) (hst a)).1 ha, ?_⟩
        show Formalism.UG.sigR I.cm.sig (Af I.F) x = _
        rw [e]
        rfl
      | zero =>
        convert (extId I w'.asIdeal).zero_mem using 1
        exact Subtype.ext (map_zero _)
      | add x y _ _ hx hy =>
        convert add_mem hx hy using 1
        exact Subtype.ext (map_add _ _ _)
      | smul a x _ hx =>
        convert Ideal.mul_mem_left _ ⟨_, hsig a a.2⟩ hx using 1
        exact Subtype.ext (map_mul _ _ _)
    exact ⟨_, key, rfl⟩
end GlobalTheory.RowLev
