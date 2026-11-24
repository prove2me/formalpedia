-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.henselian_of_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:41.229528+00:00
-- url     : https://prove2.me/submissions/bb9e72fc-ba8a-4405-bd94-050d37f1bff5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_isAdicComplete_map_of_finite
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
open GlobalTheory.RowLev.PrimeIdem
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution {O B S : Type} [CommRing O] [IsNoetherianRing O] [CommRing B] [Module.Finite ℤ B]
    [CommRing S] (t : O) [IsAdicComplete (Ideal.span {t}) O] (φ : O →+* S) (ψ : B →+* S)
    (h : ∀ T : Subring S, (∀ x, φ x ∈ T) → (∀ x, ψ x ∈ T) → ∀ x, x ∈ T) :
    HenselianRing S (Ideal.span {φ t}) := by
  let _ : Algebra O S := φ.toAlgebra
  let f : O ⊗[ℤ] B →ₐ[O] S :=
    Algebra.TensorProduct.lift (Algebra.ofId O S) ψ.toIntAlgHom fun _ _ => Commute.all _ _
  have hf : Function.Surjective f := fun x => by
    refine h (f : O ⊗[ℤ] B →+* S).range (fun y => ⟨y ⊗ₜ 1, ?_⟩) (fun y => ⟨1 ⊗ₜ y, ?_⟩) x
    · simp [f]; rfl
    · simp [f]
  have : Module.Finite O S := Module.Finite.of_surjective f.toLinearMap hf
  have := GlobalTheory.isAdicComplete_map_of_finite (Ideal.span {t}) S
  rw [Ideal.map_span, Set.image_singleton] at this
  exact IsAdicComplete.henselianRing S (Ideal.span {algebraMap O S t})
end GlobalTheory.RowLev.PrimeIdem
