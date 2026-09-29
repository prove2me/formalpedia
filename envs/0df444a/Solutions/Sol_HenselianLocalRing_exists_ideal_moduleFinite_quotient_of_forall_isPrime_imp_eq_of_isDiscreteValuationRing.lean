-- Prove2me | solution 1 for HenselianLocalRing.exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bd910d81-70fe-585a-a794-6856fbd55ad0

import Mathlib
import Theorems.Thm_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
import Theorems.Thm_Algebra_QuasiFiniteAt_of_minimal_of_maximal
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing

set_option autoImplicit false

universe u v

open IsLocalRing

namespace H2

theorem isIdempotentElem_eq_zero_or_one {L : Type*} [CommRing L] [IsLocalRing L] {e : L} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    have : e * e = e * 1 := by rw [mul_one]; exact he.eq
    exact hu.mul_left_cancel this
  · left
    have h1 : IsIdempotentElem (1 - e) := he.one_sub
    have : (1 - e) * (1 - e) = (1 - e) * 1 := by rw [mul_one]; exact h1.eq
    have h2 := hu.mul_left_cancel this

    have : e = 1 - (1 - e) := by ring
    rw [this, h2, sub_self]

end H2

open H2 in
set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {A : Type v} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (hRA : Function.Injective (algebraMap R A))
    (𝔪 : Ideal A) [𝔪.IsMaximal] (hϖ𝔪 : algebraMap R A ϖ ∈ 𝔪)
    (t : A) (ht : t ∈ 𝔪)

    (hisol : ∀ P : Ideal A, P.IsPrime → t ∈ P → algebraMap R A ϖ ∈ P → P ≤ 𝔪 → P = 𝔪)

    (hreg : ∀ a : A, t * a ∈ Ideal.span {algebraMap R A ϖ} →
      ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {algebraMap R A ϖ}) :
    ∃ I : Ideal A,
      (∀ a : A, a ∈ I ↔ ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {t}) ∧
      t ∈ I ∧ I ≤ 𝔪 ∧
      Module.Finite R (A ⧸ I) ∧
      (∀ y : A ⧸ I, algebraMap R (A ⧸ I) ϖ * y = 0 → y = 0) ∧
      (∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ 𝔪) := by
  classical
  haveI : IsNoetherianRing R := inferInstance
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have : maximalIdeal R = ⊥ := by rw [hϖ, h, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField R ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr this)
  have hϖA0 : algebraMap R A ϖ ≠ 0 := fun h => hϖ0 (hRA (by rw [h, map_zero]))

  set J : Ideal A := Ideal.span {t} with hJ
  have hJ𝔪 : J ≤ 𝔪 := by rw [hJ, Ideal.span_singleton_le_iff_mem]; exact ht
  set qb : Ideal (A ⧸ J) := 𝔪.map (Ideal.Quotient.mk J) with hqb
  have hmemqb : ∀ x : A, Ideal.Quotient.mk J x ∈ qb ↔ x ∈ 𝔪 := fun x => Ideal.mem_quotient_iff_mem hJ𝔪
  haveI hqbmax : qb.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective ‹𝔪.IsMaximal› with h | h
    · exfalso
      have : Ideal.Quotient.mk J 1 ∈ qb := by rw [← hqb] at h; rw [h]; trivial
      rw [hmemqb] at this
      exact ‹𝔪.IsMaximal›.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    · exact h
  haveI : qb.IsPrime := hqbmax.isPrime

  let φ : A →ₐ[R] Localization.AtPrime qb :=
    (IsScalarTower.toAlgHom R (A ⧸ J) (Localization.AtPrime qb)).comp (Ideal.Quotient.mkₐ R J)
  have hφ : ∀ a : A, φ a = algebraMap (A ⧸ J) (Localization.AtPrime qb) (Ideal.Quotient.mk J a) := fun _ => rfl

  have hmemI : ∀ a : A, a ∈ RingHom.ker (φ : A →+* Localization.AtPrime qb) ↔ ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ J := by
    intro a
    rw [RingHom.mem_ker]
    change φ a = 0 ↔ _
    rw [hφ, IsLocalization.map_eq_zero_iff qb.primeCompl]
    constructor
    · rintro ⟨⟨m, hm⟩, hma⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨s, fun hs => hm ((hmemqb s).mpr hs), ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]; exact hma
    · rintro ⟨s, hs, hsa⟩
      refine ⟨⟨Ideal.Quotient.mk J s, fun h => hs ((hmemqb s).mp h)⟩, ?_⟩
      show Ideal.Quotient.mk J s * Ideal.Quotient.mk J a = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hsa
  set I : Ideal A := RingHom.ker (φ : A →+* Localization.AtPrime qb) with hIdef
  have htI : t ∈ I := (hmemI t).mpr ⟨1, fun h => ‹𝔪.IsMaximal›.ne_top ((Ideal.eq_top_iff_one _).mpr h),
    by rw [one_mul]; exact Ideal.subset_span rfl⟩
  have hI𝔪 : I ≤ 𝔪 := by
    intro a ha
    obtain ⟨s, hs, hsa⟩ := (hmemI a).mp ha
    exact ((‹𝔪.IsMaximal›.isPrime.mem_or_mem (hJ𝔪 hsa)).resolve_left hs)

  have hcomapqb : qb.comap (Ideal.Quotient.mk J) = 𝔪 := Ideal.ext fun x => by rw [Ideal.mem_comap, hmemqb]
  have h𝔪R : 𝔪.comap (algebraMap R A) = maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ 𝔪)
    · rw [hϖ, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact hϖ𝔪
  have halg : algebraMap R (A ⧸ J) = (Ideal.Quotient.mk J).comp (algebraMap R A) := rfl
  have hq : qb.comap (algebraMap R (A ⧸ J)) = maximalIdeal R := by
    rw [halg, ← Ideal.comap_comap, hcomapqb, h𝔪R]
  have hfix : ∀ P : Ideal (A ⧸ J), P.IsPrime →
      P.comap (algebraMap R (A ⧸ J)) = qb.comap (algebraMap R (A ⧸ J)) → P ≤ qb → P = qb := by
    intro P hPp hPc hPle
    haveI := hPp
    have hP'p : (P.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ P
    have htP' : t ∈ P.comap (Ideal.Quotient.mk J) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl : t ∈ J)]
      exact P.zero_mem
    have hϖP' : algebraMap R A ϖ ∈ P.comap (Ideal.Quotient.mk J) := by
      have h1 : ϖ ∈ P.comap (algebraMap R (A ⧸ J)) := by
        rw [hPc, hq, hϖ]; exact Ideal.subset_span rfl
      exact h1
    have hP'le : P.comap (Ideal.Quotient.mk J) ≤ 𝔪 := fun x hx => (hmemqb x).mp (hPle hx)
    have hP'𝔪 := hisol _ hP'p htP' hϖP' hP'le
    calc P = (P.comap (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk J) :=
          (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm
      _ = qb := by rw [hP'𝔪]
  have hmin : Minimal (fun P : Ideal (A ⧸ J) => P.IsPrime ∧
      P.comap (algebraMap R (A ⧸ J)) = qb.comap (algebraMap R (A ⧸ J))) qb :=
    ⟨⟨inferInstance, rfl⟩, fun y hy hyle => (hfix y hy.1 hy.2 hyle).symm.le⟩
  have hmax : Maximal (fun P : Ideal (A ⧸ J) => P.IsPrime ∧
      P.comap (algebraMap R (A ⧸ J)) = qb.comap (algebraMap R (A ⧸ J))) qb :=
    ⟨⟨inferInstance, rfl⟩, fun y hy hle => (hqbmax.eq_of_le hy.1.ne_top hle).symm.le⟩
  haveI : Algebra.QuasiFiniteAt R qb := Algebra.QuasiFiniteAt.of_minimal_of_maximal qb hmin hmax
  haveI hLfin : Module.Finite R (Localization.AtPrime qb) :=
    HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt qb hq

  let ψ : (A ⧸ I) →ₐ[R] Localization.AtPrime qb := Ideal.kerLiftAlg φ
  have hψ : Function.Injective ψ := Ideal.kerLiftAlg_injective φ
  have hfin : Module.Finite R (A ⧸ I) := Module.Finite.of_injective ψ.toLinearMap hψ

  have htors : ∀ y : A ⧸ I, algebraMap R (A ⧸ I) ϖ * y = 0 → y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h1 : algebraMap R A ϖ * a ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]; exact hy
    obtain ⟨s, hs, hsa⟩ := (hmemI _).mp h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsa
    obtain ⟨s₁, hs₁, hs₁b⟩ := hreg b (Ideal.mem_span_singleton'.mpr ⟨s * a, by linear_combination (-1 : A) * hb⟩)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs₁b
    have h2 : algebraMap R A ϖ * (s₁ * s * a - c * t) = 0 := by linear_combination (-s₁) * hb - t * hc
    have h3 : s₁ * s * a = c * t := by
      have := (mul_eq_zero.mp h2).resolve_left hϖA0
      exact sub_eq_zero.mp this
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    refine (hmemI a).mpr ⟨s₁ * s, fun h => ?_, ?_⟩
    · exact ((‹𝔪.IsMaximal›.isPrime.mem_or_mem h).elim hs₁ hs)
    · rw [h3]; exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

  have hloc : ∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ 𝔪 := by
    intro P hP hIP
    haveI := hfin
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    suffices hM𝔪 : M = 𝔪 from hPM.trans hM𝔪.le
    by_contra hne

    have hbar : ∀ N : Ideal A, N.IsMaximal → I ≤ N → (N.map (Ideal.Quotient.mk I)).IsMaximal := by
      intro N hN hIN
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hN with h | h
      · exfalso
        have : Ideal.Quotient.mk I 1 ∈ N.map (Ideal.Quotient.mk I) := by rw [h]; trivial
        rw [Ideal.mem_quotient_iff_mem hIN] at this
        exact hN.ne_top ((Ideal.eq_top_iff_one _).mpr this)
      · exact h
    obtain ⟨hft, e, hcoi, hnot, -, -⟩ :=
      HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
        (R := R) (S := A ⧸ I)

    have hone : ∀ m : MaximalSpectrum (A ⧸ I), e m = 1 := by
      intro m
      have hid : IsIdempotentElem (ψ (e m)) := (hcoi.idem m).map ψ
      rcases isIdempotentElem_eq_zero_or_one hid with h0 | h1
      · exfalso
        apply hnot m
        have : e m = 0 := hψ (by rw [h0, map_zero])
        rw [this]; exact (m.asIdeal).zero_mem
      · exact hψ (by rw [h1, map_one])
    let m₁ : MaximalSpectrum (A ⧸ I) := ⟨M.map (Ideal.Quotient.mk I), hbar M hM (hIP.trans hPM)⟩
    let m₂ : MaximalSpectrum (A ⧸ I) := ⟨𝔪.map (Ideal.Quotient.mk I), hbar 𝔪 inferInstance hI𝔪⟩
    have hm : m₁ ≠ m₂ := by
      intro h
      apply hne
      have h' : M.map (Ideal.Quotient.mk I) = 𝔪.map (Ideal.Quotient.mk I) := congrArg MaximalSpectrum.asIdeal h
      have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h'
      rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        sup_eq_left.mpr (hIP.trans hPM), sup_eq_left.mpr hI𝔪] at this
    have h0 : e m₁ * e m₂ = 0 := hcoi.ortho hm
    rw [hone, hone, mul_one] at h0
    exact (hbar 𝔪 inferInstance hI𝔪).ne_top ((Ideal.eq_top_iff_one _).mpr (by rw [h0]; exact Ideal.zero_mem _))
  exact ⟨I, hmemI, htI, hI𝔪, hfin, htors, hloc⟩

end S_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
end P2MW
export P2MW.S_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing (solution)
