-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:21.050186+00:00
-- url     : https://prove2.me/submissions/f3a05271-5aaa-442d-84b7-e755cb5a1e93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one
import Theorems.Thm_GlobalTheory_RowLev_Inhab_levelafC_nat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_int
import Theorems.Thm_Formalism_UG_P_integral_adele_approximation_holds
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
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : Ideal.absNorm w.asIdeal = p) :
    ∃ r : IntAf F E →+* ZMod p, ∀ a, r (psi F E a) = 0 ↔ a ∈ w.asIdeal := by
  classical
  have hfin : Finite (𝓞 E ⧸ w.asIdeal) := (Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card, ← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e := ZMod.ringEquivOfPrime (𝓞 E ⧸ w.asIdeal) hp hc
  let ρ : 𝓞 E →+* ZMod p := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hρ : ∀ a, ρ a = 0 ↔ a ∈ w.asIdeal := fun a => by
    show e.symm (Ideal.Quotient.mk _ a) = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  let P : Ideal (IntAf F E) := Ideal.span {(p : IntAf F E)}
  let θ : 𝓞 E →+* IntAf F E ⧸ P := (Ideal.Quotient.mk P).comp (psi F E)
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hθ : Function.Surjective θ := by
    intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx integral_adele_approximation_holds (p : 𝓞 F) hp0 s.1 s.2
    refine ⟨b, ?_⟩
    show Ideal.Quotient.mk P _ = _
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    rw [levelafC_nat] at hs
    show t * ((p : IntAf F E) : E ⊗[F] Af F) = s.1 - inclE (F := F) (Af F) (algebraMap (𝓞 E) E b)
    rw [hs]
    simp [mul_comm]
  have hker : RingHom.ker θ ≤ RingHom.ker ρ := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have ha' : psi F E a ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ha'
    have ht' : (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = inclE (F := F) (Af F) (algebraMap (𝓞 E) E a) := by
      have : (t : E ⊗[F] Af F) * (p : E ⊗[F] Af F) = (psi F E a : E ⊗[F] Af F) := by
        simpa using congrArg Subtype.val ht
      exact this
    have hpE : (p : E) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h2 : inclE (F := F) (Af F) (algebraMap (𝓞 E) E a / p) = t := by
      rw [div_eq_mul_inv, map_mul, ← ht', mul_assoc, ← map_natCast (inclE (F := F) (E := E) (Af F)) p, ← map_mul,
        mul_inv_cancel₀ hpE, map_one, mul_one]
    have h3 := csGlob_int (F := F) _ (h2 ▸ t.2)
    obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a / p := ⟨⟨_, h3⟩, rfl⟩
    have h4 : a = (p : 𝓞 E) * b := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_natCast, hb]
      field_simp
    rw [h4, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  refine ⟨(RingHom.liftOfSurjective θ hθ ⟨ρ, hker⟩).comp (Ideal.Quotient.mk P), fun a => ?_⟩
  rw [← hρ]
  have := RingHom.liftOfSurjective_comp_apply θ hθ ⟨ρ, hker⟩ a
  exact Eq.congr this rfl
end GlobalTheory.RowLev.Inhab
