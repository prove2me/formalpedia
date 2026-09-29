-- Prove2me | solution 1 for NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3082cd90-83c9-5594-85d1-c7986b80fc2c

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hsplit : Nontrivial (v.Extension (𝓞 L))) :
    Nonempty (L →ₐ[K] v.adicCompletion K) := by
  classical

  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  haveI : IsGalois K L := by
    apply IsGalois.of_card_aut_eq_finrank
    have hF := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    have htop : Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) = Nat.card (L ≃ₐ[K] L) :=
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (L ≃ₐ[K] L)) ≃* (L ≃ₐ[K] L)).toEquiv
    rw [htop] at hF

    have hdvd : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
      rw [← hF]
      exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L)
    haveI : Finite (L ≃ₐ[K] L) := inferInstance
    have h2 : 1 < Nat.card (L ≃ₐ[K] L) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨σ, 1, hσ⟩⟩
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · omega
    · exact h

  obtain ⟨w₁, w₂, hne⟩ := hsplit
  haveI hmax : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w₁.1.asIdeal.IsPrime := w₁.1.isPrime
  haveI hlo : w₁.1.asIdeal.LiesOver v.asIdeal :=
    ⟨by rw [← HeightOneSpectrum.under_asIdeal, w₁.2]⟩
  have htri := Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime K L hprime
    v.asIdeal v.ne_bot w₁.1.asIdeal
  have hmem : ∀ w : v.Extension (𝓞 L), w.1.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := by
    intro w
    refine ⟨w.1.isPrime, ⟨?_⟩⟩
    rw [← HeightOneSpectrum.under_asIdeal, w.2]
  have hnot1 : (v.asIdeal.primesOver (𝓞 L)).ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have e1 : w₁.1.asIdeal = a := by simpa [ha] using hmem w₁
    have e2 : w₂.1.asIdeal = a := by simpa [ha] using hmem w₂
    exact hne (Subtype.ext (HeightOneSpectrum.ext (e1.trans e2.symm)))
  have hef : v.asIdeal.ramificationIdx' w₁.1.asIdeal = 1 ∧ v.asIdeal.inertiaDeg' w₁.1.asIdeal = 1 := by
    rcases htri with h | h | h
    · exact ⟨h.2.1, h.2.2⟩
    · exact absurd h.1 hnot1
    · exact absurd h.1 hnot1

  have hfin : Module.finrank (v.adicCompletion K) (w₁.1.adicCompletion L) = 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w₁,
      hef.1, hef.2]
  haveI : Module.Finite (v.adicCompletion K) (w₁.1.adicCompletion L) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact one_pos)
  have hbij : Function.Bijective (algebraMap (v.adicCompletion K) (w₁.1.adicCompletion L)) := by
    have hinj : Function.Injective (algebraMap (v.adicCompletion K) (w₁.1.adicCompletion L)) :=
      (algebraMap (v.adicCompletion K) (w₁.1.adicCompletion L)).injective
    refine ⟨hinj, ?_⟩
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Algebra.linearMap (v.adicCompletion K) (w₁.1.adicCompletion L))
      (by rw [Module.finrank_self, hfin])).mp hinj
    exact this
  let e : v.adicCompletion K ≃+* w₁.1.adicCompletion L :=
    RingEquiv.ofBijective (algebraMap (v.adicCompletion K) (w₁.1.adicCompletion L)) hbij

  refine ⟨{ toRingHom := e.symm.toRingHom.comp (algebraMap L (w₁.1.adicCompletion L)), commutes' := fun k => ?_ }⟩
  show e.symm (algebraMap L (w₁.1.adicCompletion L) (algebraMap K L k)) = algebraMap K (v.adicCompletion K) k
  apply e.injective
  rw [RingEquiv.apply_symm_apply]
  change algebraMap L (w₁.1.adicCompletion L) (algebraMap K L k) =
    (w₁.adicCompletionSemialgHom K L) (algebraMap K (v.adicCompletion K) k)
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe K L w₁ (WithVal.toVal _ k)).symm

end S_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
end P2MW
export P2MW.S_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime (solution)
