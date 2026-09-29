-- Prove2me | solution 1 for IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9b545924-0dd0-55e9-b1ec-63f9fa3c87ec

import Mathlib
import Theorems.Thm_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
import Theorems.Thm_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map

set_option autoImplicit false

universe u v w

p2m_open "IsLocalRing P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map.IsLocalRing"

namespace IsLocalRing
p2m_export "IsLocalRing" "maximalIdeal_le_jacobson maximalIdeal maximalIdeal.isMaximal mem_maximalIdeal residue_surjective of_surjective' residue exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span"
namespace SmoothPowerSeriesAux
p2m_open "IsLocalRing"

section Quot

variable {S : Type u} [CommRing S] [IsLocalRing S]

theorem isLocalRing_quotient (I : Ideal S) (hI : I ≤ maximalIdeal S) : IsLocalRing (S ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hI)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

theorem mk_mem_maximalIdeal (I : Ideal S) [IsLocalRing (S ⧸ I)] (hI : I ≤ maximalIdeal S) {x : S}
    (hx : x ∈ maximalIdeal S) : Ideal.Quotient.mk I x ∈ maximalIdeal (S ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq] at hy
  have h1 : (1 : S) ∈ maximalIdeal S := by
    have h2 : x * s - (x * s - 1) = 1 := by ring
    rw [← h2]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hx) (hI hy)
  exact (maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem surjective_residue_comp_algebraMap_quotient {Λ : Type v} [CommRing Λ] [Algebra Λ S]
    (I : Ideal S) [IsLocalRing (S ⧸ I)] (hI : I ≤ maximalIdeal S)
    (h : Function.Surjective (⇑(residue S) ∘ ⇑(algebraMap Λ S))) :
    Function.Surjective (⇑(residue (S ⧸ I)) ∘ ⇑(algebraMap Λ (S ⧸ I))) := by
  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨l, hl⟩ := h (residue S s)
  refine ⟨l, ?_⟩
  simp only [Function.comp_apply] at hl ⊢
  have hmem : algebraMap Λ S l - s ∈ maximalIdeal S := by
    rw [← Ideal.Quotient.eq]; exact hl
  change residue (S ⧸ I) (Ideal.Quotient.mk I (algebraMap Λ S l)) = residue (S ⧸ I) (Ideal.Quotient.mk I s)
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [← map_sub]
  exact mk_mem_maximalIdeal I hI hmem

theorem isArtinianRing_quotient [IsNoetherianRing S] (I : Ideal S) (N : ℕ) (hN : maximalIdeal S ^ N ≤ I) :
    IsArtinianRing (S ⧸ I) := by
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨inferInstance, Ring.KrullDimLE.mk₀ fun P hP => ?_⟩
  set Q := P.comap (Ideal.Quotient.mk I) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hIQ : I ≤ Q := by
    intro x hx
    rw [hQ, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem |> fun _ => P.zero_mem
  have hmQ : maximalIdeal S ≤ Q := by
    intro x hx
    exact hQp.mem_of_pow_mem N (hIQ (hN (Ideal.pow_mem_pow hx N)))
  have hQm : Q = maximalIdeal S := ((maximalIdeal.isMaximal S).eq_of_le hQp.ne_top hmQ).symm
  have hPQ : P = Q.map (Ideal.Quotient.mk I) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (I := maximalIdeal S) (maximalIdeal.isMaximal S) with h | h
  · exact absurd (by rw [hPQ, hQm, h]) hP.ne_top
  · rw [hPQ, hQm]; exact h

end Quot

section Eval

variable {Λ : Type u} [CommRing Λ] {B : Type v} [CommRing B] [Algebra Λ B]

theorem algHom_coe_polynomial (θ : PowerSeries Λ →ₐ[Λ] B) (p : Polynomial Λ) :
    θ (p : PowerSeries Λ) = Polynomial.aeval (θ PowerSeries.X) p := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.coe_C, Polynomial.aeval_C, PowerSeries.C_eq_algebraMap, θ.commutes]
  | add p q hp hq => rw [Polynomial.coe_add, map_add, map_add, hp, hq]
  | monomial n a _ =>
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow,
      PowerSeries.C_eq_algebraMap, θ.commutes, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

theorem algHom_apply_eq_aeval_trunc (θ : PowerSeries Λ →ₐ[Λ] B) (M : ℕ) (hM : θ PowerSeries.X ^ M = 0)
    (f : PowerSeries Λ) : θ f = Polynomial.aeval (θ PowerSeries.X) (PowerSeries.trunc M f) := by
  have hdvd : (PowerSeries.X : PowerSeries Λ) ^ M ∣ f - (PowerSeries.trunc M f : PowerSeries Λ) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hf : f = (PowerSeries.trunc M f : PowerSeries Λ) + PowerSeries.X ^ M * g := by
    rw [← hg]; ring
  conv_lhs => rw [hf]
  rw [map_add, map_mul, map_pow, hM, zero_mul, add_zero, algHom_coe_polynomial]

theorem aeval_add_eq_of_mul_self_eq_zero (p : Polynomial Λ) (x δ : B) (hδδ : δ * δ = 0) (hδx : δ * x = 0) :
    Polynomial.aeval (x + δ) p =
      Polynomial.aeval x p + algebraMap Λ B ((Polynomial.derivative p).coeff 0) * δ := by
  rw [← Polynomial.eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ (by rw [sq, hδδ]),
    Polynomial.eval_map_algebraMap, Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
  congr 1
  set p' := Polynomial.derivative p
  have hp' : p' = Polynomial.X * Polynomial.divX p' + Polynomial.C (p'.coeff 0) := (Polynomial.X_mul_divX_add p').symm
  conv_lhs => rw [hp']
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, add_mul, mul_comm x, mul_assoc, mul_comm x δ, hδx,
    mul_zero, zero_add]

end Eval

section Kernel

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
variable {R : Type v} [CommRing R] [IsLocalRing R] [Algebra Λ R]

theorem X_mem_maximalIdeal : (PowerSeries.X : (PowerSeries Λ)) ∈ maximalIdeal (PowerSeries Λ) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem C_mem_maximalIdeal {a : Λ} (ha : a ∈ maximalIdeal Λ) : (PowerSeries.C a : (PowerSeries Λ)) ∈ maximalIdeal (PowerSeries Λ) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]
  exact ha

theorem constantCoeff_mem_of_mem_maximalIdeal {f : (PowerSeries Λ)} (hf : f ∈ maximalIdeal (PowerSeries Λ)) :
    PowerSeries.constantCoeff f ∈ maximalIdeal Λ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
  rwa [PowerSeries.isUnit_iff_constantCoeff] at hf

theorem surjective_residue_comp_algebraMap_powerSeries :
    Function.Surjective (⇑(residue (PowerSeries Λ)) ∘ ⇑(algebraMap Λ (PowerSeries Λ))) := by
  intro y
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨PowerSeries.constantCoeff f, ?_⟩
  simp only [Function.comp_apply]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [PowerSeries.algebraMap_eq]
  have h : PowerSeries.C (PowerSeries.constantCoeff f) - f =
      -(PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) := by
    conv_lhs => arg 2; rw [PowerSeries.eq_X_mul_shift_add_const f]
    ring
  rw [h]
  exact neg_mem (Ideal.mul_mem_right _ _ X_mem_maximalIdeal)

variable (φ : (PowerSeries Λ) →ₐ[Λ] R)

theorem ker_le : RingHom.ker φ ≤ (maximalIdeal (PowerSeries Λ)) := by
  intro f hf
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hf' : φ f = 0 := by simpa [RingHom.mem_ker] using hf
  have h1 : IsUnit (φ f) := hu.map φ
  rw [hf'] at h1
  exact not_isUnit_zero h1

theorem apply_mem_maximalIdeal (hφ : Function.Surjective φ) {f : (PowerSeries Λ)} (hf : f ∈ (maximalIdeal (PowerSeries Λ))) : φ f ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := hφ v
  have hk : f * s - 1 ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker]
    change φ (f * s - 1) = 0
    rw [map_sub, map_mul, map_one, hv, sub_self]
  have h1 : (1 : (PowerSeries Λ)) ∈ (maximalIdeal (PowerSeries Λ)) := by
    have h2 : f * s - (f * s - 1) = 1 := by ring
    rw [← h2]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hf) (ker_le φ hk)
  exact (maximalIdeal.isMaximal (PowerSeries Λ)).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

variable [IsNoetherianRing Λ]

theorem ker_le_mul_sup_pow (hφ : Function.Surjective φ)
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (ht : φ PowerSeries.X ∉ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R)) (N : ℕ) :
    RingHom.ker φ ≤ maximalIdeal (PowerSeries Λ) * RingHom.ker φ ⊔ maximalIdeal (PowerSeries Λ) ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [pow_zero, Ideal.one_eq_top, sup_top_eq]; exact le_top
  intro f hfK
  have hφf : φ f = 0 := by simpa [RingHom.mem_ker] using hfK
  set 𝔫 : Ideal (PowerSeries Λ) := maximalIdeal (PowerSeries Λ) with h𝔫def
  set K : Ideal (PowerSeries Λ) := RingHom.ker φ with hKdef
  set I : Ideal (PowerSeries Λ) := 𝔫 * K ⊔ 𝔫 ^ N with hIdef
  set J : Ideal (PowerSeries Λ) := K ⊔ 𝔫 ^ N with hJdef
  have hKn : K ≤ 𝔫 := ker_le φ
  have hIJ : I ≤ J := sup_le_sup_right Ideal.mul_le_right _
  have hJn : J ≤ 𝔫 := sup_le hKn (Ideal.pow_le_self hN.ne')
  have hIn : I ≤ 𝔫 := hIJ.trans hJn
  have hnI : 𝔫 ^ N ≤ I := le_sup_right
  have hnJ : 𝔫 ^ N ≤ J := le_sup_right
  have hKJ : K ≤ J := le_sup_left
  haveI : IsLocalRing (PowerSeries Λ ⧸ I) := isLocalRing_quotient I hIn
  haveI : IsLocalRing (PowerSeries Λ ⧸ J) := isLocalRing_quotient J hJn
  haveI : IsArtinianRing (PowerSeries Λ ⧸ I) := isArtinianRing_quotient I N hnI
  haveI : IsArtinianRing (PowerSeries Λ ⧸ J) := isArtinianRing_quotient J N hnJ
  have hresS := surjective_residue_comp_algebraMap_powerSeries (Λ := Λ)
  have hA := surjective_residue_comp_algebraMap_quotient J hJn hresS
  have hB := surjective_residue_comp_algebraMap_quotient I hIn hresS

  let e : (PowerSeries Λ ⧸ K) ≃ₐ[Λ] R := Ideal.quotientKerAlgEquivOfSurjective hφ
  let g : R →ₐ[Λ] PowerSeries Λ ⧸ J := (Ideal.Quotient.factorₐ Λ hKJ).comp (e.symm : R →ₐ[Λ] PowerSeries Λ ⧸ K)
  let π : PowerSeries Λ ⧸ I →ₐ[Λ] PowerSeries Λ ⧸ J := Ideal.Quotient.factorₐ Λ hIJ
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I s, rfl⟩

  have hJn0 : ∀ s ∈ J, ∀ n ∈ 𝔫, Ideal.Quotient.mk I s * Ideal.Quotient.mk I n = 0 := by
    intro s hs n hn
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨k, hk, m, hm, hkm⟩ := Submodule.mem_sup.mp hs
    rw [← hkm, add_mul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · have h := Ideal.mul_mem_mul hn hk
      rwa [mul_comm n k] at h
    · exact Ideal.mul_mem_right _ _ hm
  have hsmall : ∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal (PowerSeries Λ ⧸ I), x * y = 0 := by
    intro x hx y hy
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs : s ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    have hn : n ∈ 𝔫 := by
      by_contra hn
      have hnu : IsUnit n := by
        by_contra hnu
        exact hn ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      exact ((IsLocalRing.mem_maximalIdeal _).mp hy) (hnu.map (Ideal.Quotient.mk I))
    exact hJn0 s hs n hn
  obtain ⟨g', hg'⟩ := hsmooth (PowerSeries Λ ⧸ J) (PowerSeries Λ ⧸ I) hA hB π hπ hsmall g

  let χ : PowerSeries Λ →ₐ[Λ] PowerSeries Λ ⧸ I := g'.comp φ
  have hes : ∀ s, e.symm (φ s) = Ideal.Quotient.mk K s := by
    intro s
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hφ s).symm
  have hχ : ∀ s, π (χ s) = Ideal.Quotient.mk J s := by
    intro s
    change π (g' (φ s)) = _
    rw [← AlgHom.comp_apply, hg']
    change Ideal.Quotient.factorₐ Λ hKJ (e.symm (φ s)) = _
    rw [hes]
    rfl

  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (χ PowerSeries.X)
  set d : PowerSeries Λ := w - PowerSeries.X with hddef
  have hdJ : d ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : π (Ideal.Quotient.mk I d) = 0 := by
      rw [hddef, map_sub, map_sub, hw, hχ]
      exact sub_self _
    exact h1
  have hdn : ∀ n ∈ 𝔫, Ideal.Quotient.mk I d * Ideal.Quotient.mk I n = 0 := fun n hn => hJn0 d hdJ n hn
  set xb : PowerSeries Λ ⧸ I := Ideal.Quotient.mk I PowerSeries.X with hxbdef
  set δ : PowerSeries Λ ⧸ I := Ideal.Quotient.mk I d with hδdef
  have hu : χ PowerSeries.X = xb + δ := by
    rw [hδdef, hddef, map_sub, hw, hxbdef]; ring
  have hδδ : δ * δ = 0 := hdn d (hJn hdJ)
  have hδx : δ * xb = 0 := hdn _ X_mem_maximalIdeal

  have hxbN : xb ^ N = 0 := by
    rw [hxbdef, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hnI (Ideal.pow_mem_pow X_mem_maximalIdeal N)
  set M : ℕ := 2 * (N + 1) with hMdef
  have hxbM : xb ^ M = 0 := pow_eq_zero_of_le (by omega) hxbN
  have hu2 : χ PowerSeries.X ^ 2 = xb ^ 2 := by
    rw [hu, add_sq, mul_assoc, mul_comm xb δ, hδx, mul_zero, add_zero, sq δ, hδδ, add_zero]
  have huM : χ PowerSeries.X ^ M = 0 := by
    rw [hMdef, pow_mul, hu2, ← pow_mul]
    exact pow_eq_zero_of_le (by omega) hxbN

  set p : Polynomial Λ := PowerSeries.trunc M f with hpdef
  have h1 : χ f = Polynomial.aeval (χ PowerSeries.X) p := algHom_apply_eq_aeval_trunc χ M huM f
  have h2 : Ideal.Quotient.mk I f = Polynomial.aeval xb p :=
    algHom_apply_eq_aeval_trunc (Ideal.Quotient.mkₐ Λ I) M hxbM f
  have hχf : χ f = 0 := by
    change g' (φ f) = 0
    rw [hφf, map_zero]
  set c : Λ := (Polynomial.derivative p).coeff 0 with hcdef
  have htaylor := aeval_add_eq_of_mul_self_eq_zero p xb δ hδδ hδx
  rw [← hu, ← h1, hχf] at htaylor
  have hkey : Polynomial.aeval xb p = -(algebraMap Λ (PowerSeries Λ ⧸ I) c * δ) :=
    eq_neg_of_add_eq_zero_left htaylor.symm
  by_cases hcm : c ∈ maximalIdeal Λ
  ·
    have h0 : algebraMap Λ (PowerSeries Λ ⧸ I) c * δ = 0 := by
      change Ideal.Quotient.mk I (algebraMap Λ (PowerSeries Λ) c) * δ = 0
      rw [mul_comm, PowerSeries.algebraMap_eq]
      exact hdn _ (C_mem_maximalIdeal hcm)
    change f ∈ I
    rw [← Ideal.Quotient.eq_zero_iff_mem, h2, hkey, h0, neg_zero]
  ·
    exfalso
    have hcu : IsUnit c := by
      by_contra h
      exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have hM1 : 1 < M := by omega
    have hc1 : c = PowerSeries.coeff 1 f := by
      rw [hcdef, Polynomial.coeff_derivative, hpdef, PowerSeries.coeff_trunc, if_pos hM1]
      simp

    set f₁ : PowerSeries Λ := PowerSeries.mk fun q => PowerSeries.coeff (q + 1) f with hf₁def
    set f₂ : PowerSeries Λ := PowerSeries.mk fun q => PowerSeries.coeff (q + 1) f₁ with hf₂def
    have hf : f = PowerSeries.X * f₁ + PowerSeries.C (PowerSeries.constantCoeff f) :=
      PowerSeries.eq_X_mul_shift_add_const f
    have hf₁ : f₁ = PowerSeries.X * f₂ + PowerSeries.C c := by
      have h := PowerSeries.eq_X_mul_shift_add_const f₁
      have hcc : PowerSeries.constantCoeff f₁ = c := by
        rw [hc1, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf₁def, PowerSeries.coeff_mk]
      rw [hcc] at h
      exact h
    have ha₀ : PowerSeries.constantCoeff f ∈ maximalIdeal Λ :=
      constantCoeff_mem_of_mem_maximalIdeal (hKn hfK)
    have htm : φ PowerSeries.X ∈ maximalIdeal R := apply_mem_maximalIdeal φ hφ X_mem_maximalIdeal

    have hrel : φ PowerSeries.X * algebraMap Λ R c =
        -(algebraMap Λ R (PowerSeries.constantCoeff f)) - φ PowerSeries.X * φ PowerSeries.X * φ f₂ := by
      have h := hφf
      rw [hf, hf₁, map_add, map_mul, map_add, map_mul, PowerSeries.C_eq_algebraMap, PowerSeries.C_eq_algebraMap,
        AlgHom.commutes, AlgHom.commutes] at h
      linear_combination h
    have hmem : φ PowerSeries.X * algebraMap Λ R c ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) := by
      rw [hrel]
      refine Ideal.sub_mem _ (Ideal.mem_sup_right (neg_mem (Ideal.mem_map_of_mem _ ha₀))) (Ideal.mem_sup_left ?_)
      rw [pow_two]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul htm htm)
    apply ht
    obtain ⟨cu, hcu'⟩ := (hcu.map (algebraMap Λ R)).exists_right_inv
    have : φ PowerSeries.X = φ PowerSeries.X * algebraMap Λ R c * cu := by
      rw [mul_assoc, hcu', mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hmem

theorem injective_of_lifts (hφ : Function.Surjective φ)
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (ht : φ PowerSeries.X ∉ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R)) :
    Function.Injective φ := by
  set 𝔫 : Ideal (PowerSeries Λ) := maximalIdeal (PowerSeries Λ) with h𝔫def
  set K : Ideal (PowerSeries Λ) := RingHom.ker φ with hKdef
  have hA : ∀ N : ℕ, K ≤ 𝔫 * K ⊔ 𝔫 ^ N := fun N => ker_le_mul_sup_pow φ hφ hsmooth ht N
  have hnK : 𝔫 * K ≤ 𝔫 := Ideal.mul_le_left
  have hB : K ≤ 𝔫 * K := by
    intro f hf
    haveI : IsLocalRing (PowerSeries Λ ⧸ 𝔫 * K) := isLocalRing_quotient _ hnK
    have hker : Ideal.comap (Ideal.Quotient.mk (𝔫 * K)) ⊥ = 𝔫 * K := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    have hne : 𝔫.map (Ideal.Quotient.mk (𝔫 * K)) ≠ ⊤ := by
      intro htop
      have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (𝔫 * K)) Ideal.Quotient.mk_surjective 𝔫
      rw [htop, Ideal.comap_top, hker] at h
      have h2 : (⊤ : Ideal (PowerSeries Λ)) ≤ 𝔫 := by
        rw [h]; exact sup_le le_rfl hnK
      exact (maximalIdeal.isMaximal (PowerSeries Λ)).ne_top (top_le_iff.mp h2)
    have hkrull := Ideal.iInf_pow_eq_bot_of_isLocalRing (𝔫.map (Ideal.Quotient.mk (𝔫 * K))) hne
    have hmem : Ideal.Quotient.mk (𝔫 * K) f ∈ ⨅ i : ℕ, (𝔫.map (Ideal.Quotient.mk (𝔫 * K))) ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      rw [← Ideal.map_pow]
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hA i hf)
      rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
      exact Ideal.mem_map_of_mem _ hb
    rw [hkrull, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hmem
  have hK : K = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔫 K (IsNoetherian.noetherian K)
      (by rw [Ideal.smul_eq_mul]; exact hB) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact (RingHom.injective_iff_ker_eq_bot φ).mpr hK

end Kernel

section Assembly

variable {Λ : Type u} [CommRing Λ]

theorem exists_algHom_powerSeries_mvPowerSeries_fin_one :
    ∃ E : PowerSeries Λ →ₐ[Λ] MvPowerSeries (Fin 1) Λ, E PowerSeries.X = MvPowerSeries.X 0 ∧ Function.Surjective E := by
  obtain ⟨e₁, he₁, -⟩ := MvPowerSeries.exists_algEquiv_powerSeries_fin_succ Λ 0

  have hbij : Function.Bijective (Algebra.ofId Λ (MvPowerSeries (Fin 0) Λ)) := by
    have hC : ∀ a : Λ, Algebra.ofId Λ (MvPowerSeries (Fin 0) Λ) a = MvPowerSeries.C a := by
      intro a
      rw [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    refine ⟨fun a b h => MvPowerSeries.C_injective (by rwa [hC, hC] at h), fun f => ?_⟩
    obtain ⟨a, ha⟩ := MvPowerSeries.C_surjective f
    exact ⟨a, by rw [hC, ha]⟩
  let ι₀ : Λ ≃ₐ[Λ] MvPowerSeries (Fin 0) Λ := AlgEquiv.ofBijective _ hbij
  let F : PowerSeries Λ →ₐ[Λ] PowerSeries (MvPowerSeries (Fin 0) Λ) := PowerSeries.mapAlgHom (ι₀ : Λ →ₐ[Λ] _)
  have hFX : F PowerSeries.X = PowerSeries.X := by
    change PowerSeries.map _ PowerSeries.X = PowerSeries.X
    exact PowerSeries.map_X _
  have hFs : Function.Surjective F := by
    intro f
    refine ⟨PowerSeries.map (ι₀.symm : MvPowerSeries (Fin 0) Λ →ₐ[Λ] Λ) f, ?_⟩
    change PowerSeries.map _ (PowerSeries.map _ f) = f
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact ι₀.apply_symm_apply _
  refine ⟨(e₁.symm : PowerSeries (MvPowerSeries (Fin 0) Λ) →ₐ[Λ] MvPowerSeries (Fin 1) Λ).comp F, ?_, ?_⟩
  · change e₁.symm (F PowerSeries.X) = MvPowerSeries.X 0
    rw [hFX, AlgEquiv.symm_apply_eq]
    exact he₁.symm
  · exact e₁.symm.surjective.comp hFs

end Assembly

end IsLocalRing.SmoothPowerSeriesAux

open IsLocalRing.SmoothPowerSeriesAux in

theorem solution
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra Λ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (t : R) (htm : t ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span {t} ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R))
    (ht : t ∉ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R)) :
    ∃ e : PowerSeries Λ ≃ₐ[Λ] R, e PowerSeries.X = t := by
  obtain ⟨ψ, hψX, hψs⟩ :=
    IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span (𝒪 := Λ) (R := R) hres
      (r := 1) (fun _ => t) (fun _ => htm) (by rwa [Set.range_const])
  obtain ⟨E, hEX, hEs⟩ := exists_algHom_powerSeries_mvPowerSeries_fin_one (Λ := Λ)
  let φ : PowerSeries Λ →ₐ[Λ] R := ψ.comp E
  have hφX : φ PowerSeries.X = t := by
    change ψ (E PowerSeries.X) = t
    rw [hEX, hψX]
  have hφs : Function.Surjective φ := hψs.comp hEs
  have hφi : Function.Injective φ := injective_of_lifts φ hφs hsmooth (by rw [hφX]; exact ht)
  exact ⟨AlgEquiv.ofBijective φ ⟨hφi, hφs⟩, hφX⟩

end S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map
end P2MW
export P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map (solution)
