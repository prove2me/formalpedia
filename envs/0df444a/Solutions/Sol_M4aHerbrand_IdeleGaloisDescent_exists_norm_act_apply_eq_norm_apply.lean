-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_norm_act_apply_eq_norm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/32dcb932-5d71-53c2-bb4a-bd1a21291c54

import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField.PlaceTransport

namespace SigmaIsometryBody

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem norm_transport_finite (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w')
    (y : w.adicCompletion L) : ‖NumberField.PlaceTransport.transport σ h y‖ = ‖y‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NumberField.PlaceTransport.valued_transport]
  have habs : Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal := by
    rw [← h, NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
      ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L)) rfl).toEquiv).symm
  simp_rw [habs]

theorem norm_transport_infinite (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (y : w.Completion) :
    ‖NumberField.InfinitePlaceTransport.transport σ h y‖ = ‖y‖ := by
  induction y using NumberField.InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_norm.comp (NumberField.InfinitePlaceTransport.continuous_transport σ h))
      continuous_norm
  | ih x =>
    rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe, WithAbs.congr_apply]
    exact NumberField.InfinitePlaceTransport.apply_apply_of_smul_eq h _

theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x := by
    apply Subtype.ext
    show σ⁻¹ (algebraMap K L (x : K)) = algebraMap K L (x : K)
    exact AlgEquiv.commutes _ _
  rw [this]

end SigmaIsometryBody

open SigmaIsometryBody in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    (∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)), ∃ w' : v.Extension (𝓞 L),
        ‖((D.act σ : RingAut (AdeleRing (𝓞 L) L)) a).2 w.1‖ = ‖a.2 w'.1‖) ∧
    (∀ w : InfinitePlace L, ∃ w' : InfinitePlace L,
        ‖((D.act σ : RingAut (AdeleRing (𝓞 L) L)) a).1 w‖ = ‖a.1 w'‖) := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  refine ⟨fun v w => ?_, fun w => ?_⟩
  ·
    have hw' : (σ⁻¹ • w.1).under (𝓞 K) = v := by rw [under_smul]; exact w.2
    refine ⟨⟨σ⁻¹ • w.1, hw'⟩, ?_⟩
    have h : σ • (σ⁻¹ • w.1) = w.1 := smul_inv_smul σ w.1
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ a h]
    exact norm_transport_finite σ h _
  ·
    refine ⟨σ⁻¹ • w, ?_⟩
    have h : σ • (σ⁻¹ • w) = w := smul_inv_smul σ w
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ a h]
    exact norm_transport_infinite σ h _

end S_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply (solution)
