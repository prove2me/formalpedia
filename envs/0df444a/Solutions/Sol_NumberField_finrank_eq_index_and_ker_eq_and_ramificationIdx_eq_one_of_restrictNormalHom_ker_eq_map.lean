-- Prove2me | solution 1 for NumberField.finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/28ba7d06-b1ed-547c-9979-ccf6762382f1

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem solution
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F'] [IsGalois E F]
    [IsMulCommutative (F' ≃ₐ[E] F')]
    (r' : (AdeleRing (𝓞 E) E)ˣ →* (F' ≃ₐ[E] F')) (hsurj : Function.Surjective r')
    (H₀ : Subgroup (AdeleRing (𝓞 E) E)ˣ) (hH₀ : r'.ker ≤ H₀)
    (hΓ : (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker = H₀.map r') :
    Module.finrank E F = H₀.index ∧
    (∀ rF : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F), Function.Surjective rF → H₀ ≤ rF.ker → rF.ker = H₀) ∧
    (∀ v : HeightOneSpectrum (𝓞 E),
      (∀ w' : HeightOneSpectrum (𝓞 F'), w'.asIdeal.under (𝓞 E) = v.asIdeal →
        w'.asIdeal.inertia (F' ≃ₐ[E] F') ≤ H₀.map r') →
      ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal.under (𝓞 E) = v.asIdeal →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) := by
  classical
  haveI : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite ℚ E F'
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F

  have hres : Function.Surjective (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) :=
    AlgEquiv.restrictNormalHom_surjective F'
  have hdeg : Module.finrank E F = H₀.index := by
    rw [← IsGalois.card_aut_eq_finrank, ← Subgroup.index_map_eq H₀ hsurj hH₀, ← hΓ, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hres, Subgroup.card_top]
  refine ⟨hdeg, ?_, ?_⟩
  ·
    intro rF hrF hle
    have hidx : rF.ker.index = H₀.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hrF, Subgroup.card_top, ← hdeg, IsGalois.card_aut_eq_finrank]
    have hne : H₀.index ≠ 0 := by rw [← hdeg]; exact Module.finrank_pos.ne'
    have h1 : H₀.relIndex rF.ker = 1 := by
      have h := Subgroup.relIndex_mul_index hle
      rw [hidx] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (h.trans (one_mul _).symm)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  ·
    intro v hin w hw
    rw [hw]
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩

    obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 F') w.asIdeal
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver w.asIdeal := hQ.2
    haveI : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q
    haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
    haveI : IsGalois F F' := IsGalois.tower_top_of_isGalois E F F'
    haveI : FiniteDimensional F F' := Module.Finite.of_restrictScalars_finite ℚ F F'

    have hfix : ∀ σ : F' ≃ₐ[E] F', σ ∈ Q.inertia (F' ≃ₐ[E] F') → ∀ x : F, σ (algebraMap F F' x) = algebraMap F F' x := by
      intro σ hσ x
      have hk : σ ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker := by
        rw [hΓ]; exact hin ⟨Q, hQ.1, hQne⟩ (Q.over_def v.asIdeal).symm hσ
      rw [MonoidHom.mem_ker] at hk
      have hk' : σ.restrictNormal F = 1 := hk
      have := AlgEquiv.restrictNormal_commutes σ F x
      rw [hk', AlgEquiv.one_apply] at this
      exact this.symm

    let ι : Q.inertia (F' ≃ₐ[E] F') → Q.inertia (F' ≃ₐ[F] F') := fun σ =>
      ⟨AlgEquiv.ofRingEquiv (f := (σ : F' ≃ₐ[E] F').toRingEquiv) (hfix σ σ.2), fun x => σ.2 x⟩
    have hι : Function.Injective ι := by
      intro σ τ h
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun ρ : Q.inertia (F' ≃ₐ[F] F') => (ρ : F' ≃ₐ[F] F') x) h
    have hcardle : Nat.card (Q.inertia (F' ≃ₐ[E] F')) ≤ Nat.card (Q.inertia (F' ≃ₐ[F] F')) :=
      Nat.card_le_card_of_injective ι hι

    haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    haveI : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
    letI : Field (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.field _
    letI : Field (𝓞 F' ⧸ Q) := Ideal.Quotient.field _
    have hE : Nat.card (Q.inertia (F' ≃ₐ[E] F')) = v.asIdeal.ramificationIdx' Q := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal Q,
        Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (F' ≃ₐ[E] F'),
        ← Ideal.ramificationIdx'_eq_ramificationIdx (p := v.asIdeal) (q := Q) v.ne_bot]
    have hF : Nat.card (Q.inertia (F' ≃ₐ[F] F')) = w.asIdeal.ramificationIdx' Q := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn w.asIdeal Q,
        Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal Q (F' ≃ₐ[F] F'),
        ← Ideal.ramificationIdx'_eq_ramificationIdx (p := w.asIdeal) (q := Q) w.ne_bot]
    have htower : v.asIdeal.ramificationIdx' Q = v.asIdeal.ramificationIdx' w.asIdeal * w.asIdeal.ramificationIdx' Q :=
      Ideal.ramificationIdx_algebra_tower' v.asIdeal w.asIdeal Q
    have hwQ : w.asIdeal.ramificationIdx' Q ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero
        ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 F'))).not.mpr w.ne_bot)
        inferInstance (Ideal.map_le_iff_le_comap.mpr (Q.over_def w.asIdeal).le)
    have hvw : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero
        ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 F))).not.mpr v.ne_bot)
        inferInstance (Ideal.map_le_iff_le_comap.mpr hw.symm.le)
    rw [hE, hF, htower] at hcardle
    have h1 : v.asIdeal.ramificationIdx' w.asIdeal ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by simpa using hcardle) (Nat.pos_of_ne_zero hwQ)
    omega

end S_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
end P2MW
export P2MW.S_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map (solution)
