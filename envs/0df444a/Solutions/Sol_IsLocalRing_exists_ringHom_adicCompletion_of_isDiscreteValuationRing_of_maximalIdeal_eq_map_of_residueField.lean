-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f40ff64a-a7f8-5eaa-b603-8889890bfca5

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable
import Theorems.Thm_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField

set_option autoImplicit false

open IsLocalRing Polynomial

set_option autoImplicit false

open IsLocalRing

theorem solution
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]

    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [Module.Finite (ResidueField A₀) (ResidueField W₀)]
    [Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀)]

    (χ : ResidueField W₀ →+* ResidueField A)
    (hχ : ∀ a : A₀, χ (residue W₀ (algebraMap A₀ W₀ a)) = residue A (algebraMap A₀ A a)) :
    ∃ ψ : W₀ →+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
      (∀ a : A₀, ψ (algebraMap A₀ W₀ a) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (algebraMap A₀ A a)) ∧
      (∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
      (∀ w : W₀, ∃ a : A, residue A a = χ (residue W₀ w) ∧
        ψ w - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
          (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))  := by
  classical

  obtain ⟨P, θ, hPmonic, hPirr, hPsep, hPθ, hsurj, hker⟩ :=
    IsDiscreteValuationRing.exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable A₀ W₀ hW₀

  let ι : A →+* AdicCompletion (maximalIdeal A) A := algebraMap A (AdicCompletion (maximalIdeal A) A)
  have h𝔪fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hkerev : ∀ n : ℕ, RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) n) =
      (maximalIdeal A ^ n).map ι := fun n => AdicCompletion.ker_evalₐ_eq_map_pow _ h𝔪fg n

  have hH : (χ.comp (residue W₀)).comp (algebraMap A₀ W₀) = (residue A).comp (algebraMap A₀ A) :=
    RingHom.ext hχ
  have hres₀ : (residue W₀).comp (algebraMap A₀ W₀) =
      (algebraMap (ResidueField A₀) (ResidueField W₀)).comp (residue A₀) :=
    RingHom.ext fun a => (IsLocalRing.ResidueField.algebraMap_residue (R := A₀) (S := W₀) a).symm

  have hθbar : aeval (residue W₀ θ) (P.map (residue A₀)) = 0 := by
    rw [aeval_def, eval₂_map, ← hres₀, ← hom_eval₂, ← aeval_def, hPθ, map_zero]

  let PA : Polynomial A := P.map (algebraMap A₀ A)
  have hPAmonic : PA.Monic := hPmonic.map _
  let r : ResidueField A := χ (residue W₀ θ)
  have hr : (PA.map (residue A)).eval r = 0 := by
    show ((P.map (algebraMap A₀ A)).map (residue A)).eval (χ (residue W₀ θ)) = 0
    rw [Polynomial.map_map, ← hH, eval_map,
      show χ (residue W₀ θ) = (χ.comp (residue W₀)) θ from rfl, ← hom_eval₂, ← aeval_def, hPθ, map_zero]
  have hr' : (PA.map (residue A)).derivative.eval r ≠ 0 := by
    show ((P.map (algebraMap A₀ A)).map (residue A)).derivative.eval (χ (residue W₀ θ)) ≠ 0
    rw [Polynomial.map_map, ← hH, derivative_map, eval_map,
      show χ (residue W₀ θ) = (χ.comp (residue W₀)) θ from rfl, ← hom_eval₂, RingHom.comp_apply,
      map_ne_zero_iff _ χ.injective]
    have key := hPsep.aeval_derivative_ne_zero hθbar
    rw [derivative_map, aeval_def, eval₂_map, ← hres₀, ← hom_eval₂] at key
    exact key

  obtain ⟨t, a₀, hPt, ha₀, hta₀⟩ :=
    IsLocalRing.exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero A PA hPAmonic r hr hr'

  let evθ : Polynomial A₀ →+* W₀ := (aeval θ : Polynomial A₀ →ₐ[A₀] W₀).toRingHom
  have hevθ : ∀ g, evθ g = aeval θ g := fun g => rfl
  let evt : Polynomial A₀ →+* AdicCompletion (maximalIdeal A) A := eval₂RingHom (ι.comp (algebraMap A₀ A)) t
  have hevt : ∀ g, evt g = eval₂ (ι.comp (algebraMap A₀ A)) t g := fun g => rfl
  have hevtP : evt P = 0 := by
    rw [hevt, ← eval₂_map, ← aeval_def]; exact hPt
  have hevtC : ∀ c : A₀, evt (C c) = ι (algebraMap A₀ A c) := fun c => by
    rw [hevt, eval₂_C]; rfl
  have hm0 : (maximalIdeal A₀).map (algebraMap A₀ A) ≤ maximalIdeal A :=
    ((local_hom_TFAE (algebraMap A₀ A)).out 0 2).mp (by infer_instance)

  have hvan : ∀ (n : ℕ) (g : Polynomial A₀), aeval θ g ∈ maximalIdeal W₀ ^ n →
      evt g ∈ (maximalIdeal A ^ n).map ι := by
    intro n g hg
    have hg' := (hker n g).mp hg
    have hle : (Ideal.span {P} ⊔ (maximalIdeal A₀ ^ n).map (C : A₀ →+* Polynomial A₀)).map evt ≤
        (maximalIdeal A ^ n).map ι := by
      rw [Ideal.map_sup, sup_le_iff, Ideal.map_span, Set.image_singleton, hevtP, Ideal.map_map]
      refine ⟨by rw [Ideal.span_singleton_le_iff_mem]; exact Ideal.zero_mem _, ?_⟩
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.comp_apply, hevtC]
      refine Ideal.mem_map_of_mem ι ?_
      have h1 : algebraMap A₀ A c ∈ ((maximalIdeal A₀).map (algebraMap A₀ A)) ^ n := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc
      exact Ideal.pow_right_mono hm0 n h1
    exact hle (Ideal.mem_map_of_mem evt hg')

  have hφsurj : ∀ n : ℕ, Function.Surjective ((Ideal.Quotient.mk (maximalIdeal W₀ ^ n)).comp evθ) := by
    intro n w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨g, hg⟩ := hsurj n w
    refine ⟨g, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hevθ, ← Ideal.neg_mem_iff, neg_sub]
    exact hg
  let σ : ∀ n : ℕ, Polynomial A₀ →+* A ⧸ maximalIdeal A ^ n := fun n =>
    (AdicCompletion.evalₐ (maximalIdeal A) n : AdicCompletion (maximalIdeal A) A →+* A ⧸ maximalIdeal A ^ n).comp evt
  have hσ : ∀ n g, σ n g = AdicCompletion.evalₐ (maximalIdeal A) n (evt g) := fun n g => rfl
  have hσker : ∀ (n : ℕ) (g : Polynomial A₀),
      g ∈ RingHom.ker ((Ideal.Quotient.mk (maximalIdeal W₀ ^ n)).comp evθ) → σ n g = 0 := by
    intro n g hg
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hg
    rw [hσ, ← RingHom.mem_ker, hkerev]
    exact hvan n g hg
  let ρ : ∀ n : ℕ, W₀ →+* A ⧸ maximalIdeal A ^ n := fun n =>
    (Ideal.Quotient.lift _ (σ n) (hσker n)).comp
      ((RingHom.quotientKerEquivOfSurjective (hφsurj n)).symm.toRingHom.comp
        (Ideal.Quotient.mk (maximalIdeal W₀ ^ n)))
  have hρdef : ∀ n w, ρ n w = (Ideal.Quotient.lift _ (σ n) (hσker n))
      ((RingHom.quotientKerEquivOfSurjective (hφsurj n)).symm
        (Ideal.Quotient.mk (maximalIdeal W₀ ^ n) w)) := fun n w => rfl

  have hρ : ∀ (n : ℕ) (w : W₀) (g : Polynomial A₀), w - aeval θ g ∈ maximalIdeal W₀ ^ n →
      ρ n w = σ n g := by
    intro n w g hwg
    have h1 : Ideal.Quotient.mk (maximalIdeal W₀ ^ n) w =
        ((Ideal.Quotient.mk (maximalIdeal W₀ ^ n)).comp evθ) g := by
      rw [RingHom.comp_apply, Ideal.Quotient.eq, hevθ]; exact hwg
    rw [hρdef, h1, ← RingHom.quotientKerEquivOfSurjective_apply_mk (hφsurj n) g,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

  have hfev : ∀ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion (maximalIdeal A) A),
      Ideal.Quotient.factorPow (maximalIdeal A) hle (AdicCompletion.evalₐ (maximalIdeal A) n x) =
        AdicCompletion.evalₐ (maximalIdeal A) m x := by
    intro m n hle x
    obtain ⟨a, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (maximalIdeal A) h𝔪fg n x
    have hyn : AdicCompletion.evalₐ (maximalIdeal A) n y = 0 := by
      rw [← RingHom.mem_ker, hkerev]; exact hy
    have hym : AdicCompletion.evalₐ (maximalIdeal A) m y = 0 := by
      rw [← RingHom.mem_ker, hkerev]; exact Ideal.map_mono (Ideal.pow_le_pow_right hle) hy
    have e1 : AdicCompletion.evalₐ (maximalIdeal A) n (algebraMap A _ a + y) = Ideal.Quotient.mk _ a := by
      rw [map_add, hyn, add_zero, AdicCompletion.evalₐ_algebraMap]
    have e2 : AdicCompletion.evalₐ (maximalIdeal A) m (algebraMap A _ a + y) = Ideal.Quotient.mk _ a := by
      rw [map_add, hym, add_zero, AdicCompletion.evalₐ_algebraMap]
    rw [e1, e2]
    rfl
  have hρcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (ρ n) = ρ m := by
    intro m n hle
    ext w
    obtain ⟨g, hg⟩ := hsurj n w
    rw [RingHom.comp_apply, hρ n w g hg, hρ m w g (Ideal.pow_le_pow_right hle hg), hσ, hσ, hfev]

  let ψ : W₀ →+* AdicCompletion (maximalIdeal A) A :=
    AdicCompletion.liftRingHom (maximalIdeal A) ρ hρcompat
  have hψev : ∀ (n : ℕ) (w : W₀), AdicCompletion.evalₐ (maximalIdeal A) n (ψ w) = ρ n w :=
    fun n w => AdicCompletion.evalₐ_liftRingHom _ _ hρcompat n w

  have hcongr : ∀ (J : Ideal (AdicCompletion (maximalIdeal A) A)) (x y : AdicCompletion (maximalIdeal A) A)
      (g : Polynomial A₀), x - y ∈ J →
      eval₂ (ι.comp (algebraMap A₀ A)) x g - eval₂ (ι.comp (algebraMap A₀ A)) y g ∈ J := by
    intro J x y g hxy
    rw [← Ideal.Quotient.eq, hom_eval₂, hom_eval₂, (Ideal.Quotient.eq).mpr hxy]
  refine ⟨ψ, ?_, ?_, ?_⟩
  ·
    intro a
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [hψev, hρ n (algebraMap A₀ W₀ a) (C a) (by rw [aeval_C, sub_self]; exact Ideal.zero_mem _),
      hσ, hevtC]
  ·
    intro w hw
    rw [AdicCompletion.mem_maximalIdeal_iff, hψev,
      hρ 1 w 0 (by rw [map_zero, sub_zero, pow_one]; exact hw), map_zero]
  ·
    intro w
    obtain ⟨g, hg⟩ := hsurj 1 w
    refine ⟨(g.map (algebraMap A₀ A)).eval a₀, ?_, ?_⟩
    ·
      have hw1 : residue W₀ w = residue W₀ (aeval θ g) := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← pow_one (maximalIdeal W₀)]; exact hg
      rw [hw1, eval_map, hom_eval₂, ha₀, aeval_def, ← RingHom.comp_apply (χ) (residue W₀),
        hom_eval₂, hH]
      rfl
    · have hk1 : (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
          RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
        rw [hkerev, pow_one]
      rw [hk1, RingHom.mem_ker, map_sub, hψev, hρ 1 w g hg, hσ, ← map_sub, ← RingHom.mem_ker, ← hk1,
        hevt, eval_map, hom_eval₂]
      exact hcongr _ t (ι a₀) g hta₀

end S_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField (solution)
