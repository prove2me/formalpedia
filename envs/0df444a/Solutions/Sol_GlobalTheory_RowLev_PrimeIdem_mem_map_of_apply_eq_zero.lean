-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.mem_map_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:29.828806+00:00
-- url     : https://prove2.me/submissions/ab08a2f4-83f6-4b54-a9c6-f09d1f6453ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_integral_adele_approximation_holds


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
theorem _root_.solution (u : HeightOneSpectrum (𝓞 E)) (y : Af F) (hy : y ∈ intAd F)
    (h0 : y (u.under (𝓞 F)) = 0) (z : IntAf F E) (hz : z.1 = (1 : E) ⊗ₜ[F] y) :
    z ∈ u.asIdeal.map (Inhab.psi F E) := by
  set v := u.under (𝓞 F) with hv
  obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y', hy', e⟩ := integral_adele_approximation_holds F D hD0 y hy
  have hval : ∀ d : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (Af F) d) v) < 1 ↔ d ∈ v.asIdeal := fun d => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rfl
  have hr : r ∈ v.asIdeal := by
    rw [e, afsplit_add_apply, afsplit_mul_apply, add_eq_zero_iff_eq_neg] at h0
    rw [← hval, h0, Valuation.map_neg, map_mul]
    exact (mul_le_of_le_one_right' (hy' v)).trans_lt ((hval D).2 hD)
  have hC : ∀ d : 𝓞 F, (Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) d)).1 =
      (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (Af F) d := fun d => adelstab_incl_C d
  have hz' : z = Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) r) + Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) D) *
      ⟨(1 : E) ⊗ₜ[F] y', Subring.subset_closure (Or.inr ⟨⟨y', hy'⟩, rfl⟩)⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, hC, hC, hz, e, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      TensorProduct.tmul_add]
  rw [hz']
  exact add_mem (Ideal.mem_map_of_mem _ hr) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hD))
end GlobalTheory.RowLev.PrimeIdem
