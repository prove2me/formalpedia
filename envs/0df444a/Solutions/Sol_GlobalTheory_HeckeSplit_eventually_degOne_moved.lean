-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.eventually_degOne_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:04.909953+00:00
-- url     : https://prove2.me/submissions/66b84767-c5b7-4cc8-9790-841113d8afbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGalois
import Theorems.Thm_GlobalTheory_HeckeSplit_exists_int_moved
import Theorems.Thm_GlobalTheory_HeckeSplit_finite_setOf_mem_asIdeal
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_localIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_localIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HeckeSplit.finPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.finPart_localIdele
attribute [local simp] GlobalTheory.HeckeSplit.infPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.infPart_localIdele



set_option autoImplicit false
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open GlobalTheory GlobalTheory.HeckeSplit
namespace GlobalTheory.HeckeSplit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w →
      ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  intro F E _ _ _ _ _ _ c hc
  obtain ⟨θ, hθ⟩ := exists_int_moved F E c hc
  have hint : IsIntegral ℤ (c (θ : E)) := θ.isIntegral_coe.map c.toRingHom.toIntAlgHom
  set θ' : 𝓞 E := ⟨c (θ : E), hint⟩ with hθ'
  have hδ : θ - θ' ≠ 0 := by
    intro h0
    apply hθ
    have := congrArg (fun t : 𝓞 E => (t : E)) h0
    push_cast at this
    exact (sub_eq_zero.mp this).symm
  refine (finite_setOf_mem_asIdeal E (θ - θ') hδ).subset ?_ |> Filter.eventually_cofinite.mpr
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hnot
  apply hw
  intro hdeg
  obtain ⟨u, hu⟩ := hdeg θ
  refine ⟨θ - algebraMap (𝓞 F) (𝓞 E) u, hu, fun y hy hyw => hnot ?_⟩
  have hcu : c ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) := by
    have : ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl
    rw [this, AlgEquiv.commutes]
  have hy' : y = θ' - algebraMap (𝓞 F) (𝓞 E) u := by
    apply RingOfIntegers.ext
    rw [hy]
    push_cast
    rw [map_sub, hcu]
    rfl
  have := w.asIdeal.sub_mem hu hyw
  rw [hy'] at this
  convert this using 1
  ring
end GlobalTheory.HeckeSplit
