-- Prove2me | solution 1 for MvFormalGroup.CartierModule.map_injective_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1ff2566c-3772-515a-a6c8-e5c9835c7a87

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_map_injective_of_finite_quotient

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcCartierIsogInj

open MvPowerSeries

theorem exists_X_pow_mem {k : Type u} [Field k] {σ : Type*} (I : Ideal (MvPowerSeries σ k))
    (hfin : Module.Finite k (MvPowerSeries σ k ⧸ I)) (i : σ) :
    ∃ r : ℕ, (X i : MvPowerSeries σ k) ^ r ∈ I := by
  classical
  set A := MvPowerSeries σ k

  haveI : Algebra.IsIntegral k (A ⧸ I) := Algebra.IsIntegral.of_finite k (A ⧸ I)
  have hint : IsIntegral k (Ideal.Quotient.mk I (X i : A)) := Algebra.IsIntegral.isIntegral _
  obtain ⟨P, hPmonic, hP⟩ := hint
  have hP0 : P ≠ 0 := hPmonic.ne_zero

  have hPmem : Polynomial.aeval (X i : A) P ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) (X i : A) P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [← h]
    rwa [← Polynomial.aeval_def] at hP

  set r := P.natTrailingDegree with hr
  have hdvd : (Polynomial.X : Polynomial k) ^ r ∣ P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm
  obtain ⟨U, hU⟩ := hdvd
  have hU0 : U.coeff 0 ≠ 0 := by
    have h1 : P.coeff r = U.coeff 0 := by
      rw [hU, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [← h1]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hP0

  have hunit : IsUnit (Polynomial.aeval (X i : A) U) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have hc : constantCoeff (Polynomial.aeval (X i : A) U) = U.coeff 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, constantCoeff_X, Polynomial.eval₂_at_zero]
      have hcomp : (constantCoeff : A →+* k).comp (algebraMap k A) = RingHom.id k := by
        ext c
        show constantCoeff (algebraMap k (MvPowerSeries σ k) c) = c
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C]
      rw [hcomp, RingHom.id_apply]
    rw [hc]
    exact isUnit_iff_ne_zero.mpr hU0
  refine ⟨r, ?_⟩
  have hmem : (X i : A) ^ r * Polynomial.aeval (X i : A) U ∈ I := by
    have : Polynomial.aeval (X i : A) P = (X i : A) ^ r * Polynomial.aeval (X i : A) U := by
      rw [hU, map_mul, map_pow, Polynomial.aeval_X]
    rw [← this]
    exact hPmem
  exact (Ideal.mul_unit_mem_iff_mem I hunit).mp hmem

theorem exists_forall_X_pow_mem {k : Type u} [Field k] {σ : Type*} [Fintype σ]
    (I : Ideal (MvPowerSeries σ k)) (hfin : Module.Finite k (MvPowerSeries σ k ⧸ I)) :
    ∃ s : ℕ, ∀ i : σ, (X i : MvPowerSeries σ k) ^ s ∈ I := by
  classical
  choose r hr using exists_X_pow_mem I hfin
  refine ⟨Finset.univ.sup r, fun i => ?_⟩
  exact Ideal.pow_mem_of_pow_mem I (hr i) (Finset.le_sup (Finset.mem_univ i))

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}

theorem map_injective_of_X_pow_mem [IsDomain R] {Φ : MvFormalGroup d R} [Φ.IsComm]
    {Φ' : MvFormalGroup d' R} [Φ'.IsComm] (φ : Φ.Hom Φ') (s : ℕ)
    (hs : ∀ i : Fin d, (X i : MvPowerSeries (Fin d) R) ^ s ∈ Ideal.span (Set.range φ.toPowerSeries)) :
    Function.Injective (MvFormalGroup.CartierModule.map (p := p) φ) := by
  rw [injective_iff_map_eq_zero]
  intro f hf

  set S : MvPowerSeries (Fin d) R →ₐ[R] MvPowerSeries ℕ R := substAlgHom f.hasSubst_toPowerSeries
    with hSdef
  have hφ : ∀ j : Fin d', S (φ.toPowerSeries j) = 0 := by
    intro j
    have h := congrArg (fun g : MvFormalGroup.CartierModule p Φ' => g.toPowerSeries j) hf
    simp only [MvFormalGroup.CartierModule.toPowerSeries_map] at h
    rw [hSdef, substAlgHom_apply]
    exact h
  have hker : Ideal.span (Set.range φ.toPowerSeries) ≤ RingHom.ker S.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  apply MvFormalGroup.CartierModule.ext
  funext i
  have hi : S ((X i : MvPowerSeries (Fin d) R) ^ (s + 1)) = 0 := by
    apply hker
    rw [pow_succ']
    exact Ideal.mul_mem_left _ _ (hs i)
  rw [map_pow, hSdef, substAlgHom_apply, subst_X f.hasSubst_toPowerSeries] at hi
  exact (pow_eq_zero_iff (Nat.succ_ne_zero s)).mp hi

end P2mKcCartierIsogInj

open P2mKcCartierIsogInj in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] {d d' : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (Φ' : MvFormalGroup d' k) [Φ'.IsComm] (φ : Φ.Hom Φ')
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range φ.toPowerSeries))) :
    Function.Injective (MvFormalGroup.CartierModule.map (p := p) φ) := by
  obtain ⟨s, hs⟩ := exists_forall_X_pow_mem _ hfin
  exact map_injective_of_X_pow_mem φ s hs

end

end S_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_map_injective_of_finite_quotient (solution)
