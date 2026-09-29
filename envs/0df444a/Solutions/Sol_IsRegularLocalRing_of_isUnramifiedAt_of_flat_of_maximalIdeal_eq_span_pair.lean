-- Prove2me | solution 1 for IsRegularLocalRing.of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fcf85948-6b04-5033-98bc-05b08324b89c

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing
open scoped TensorProduct

namespace L1BP3

theorem hdimle (T : Type*) [CommRing T] [IsNoetherianRing T] [IsLocalRing T] (a : T)
    (ha : maximalIdeal T = Ideal.span {a}) : ringKrullDim T ≤ 1 := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal T).trans ?_
  rw [ha]
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans
    (by rw [Set.ncard_singleton])

theorem toNZD (T : Type*) [CommRing T] (x : T) (hx : IsSMulRegular T x) : x ∈ nonZeroDivisors T := by
  have hinj : Function.Injective (fun y : T => x * y) := fun a b hab => hx (by simpa [smul_eq_mul] using hab)
  refine mem_nonZeroDivisors_iff.mpr ⟨fun y hy => hinj (by simpa using hy), fun y hy => hinj (by simpa [mul_comm] using hy)⟩

end L1BP3

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {O O' : Type*} [CommRing O] [IsRegularLocalRing O] [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Flat O O'] [Algebra.EssFiniteType O O']
    [Algebra.IsUnramifiedAt O (maximalIdeal O')]
    (ϖ s : O) (hmax : maximalIdeal O = Ideal.span {ϖ, s}) (hdim : ringKrullDim O = 2)
    {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (π : O →+* D) (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {s}) :
    IsRegularLocalRing O' ∧ ringKrullDim O' = 2 ∧
      maximalIdeal O' = Ideal.span {algebraMap O O' ϖ, algebraMap O O' s} ∧
      (Ideal.span {algebraMap O O' s}).IsPrime ∧
      ∃ (_ : IsDomain (O' ⧸ Ideal.span {algebraMap O O' s})),
        IsDiscreteValuationRing (O' ⧸ Ideal.span {algebraMap O O' s}) := by
  classical
  haveI : IsNoetherianRing O := inferInstance
  haveI : IsDomain O := IsRegularLocalRing.isDomain O
  set φ := algebraMap O O' with hφ

  have hπϖ : π ϖ ≠ 0 := by
    intro h0
    have hmem : ϖ ∈ Ideal.span {s} := by rw [← hker]; exact h0
    have : maximalIdeal O = Ideal.span {s} := by
      rw [hmax]; apply le_antisymm
      · rw [Ideal.span_le]; rintro x (rfl | rfl); exacts [hmem, Ideal.subset_span rfl]
      · exact Ideal.span_mono (by simp)
    have := L1BP3.hdimle O s this
    rw [hdim] at this; exact absurd this (by decide)
  have hs0 : s ≠ 0 := by
    intro h0
    have : maximalIdeal O = Ideal.span {ϖ} := by
      rw [hmax, h0]; apply le_antisymm
      · rw [Ideal.span_le]; rintro x (rfl | rfl); exacts [Ideal.subset_span rfl, Ideal.zero_mem _]
      · exact Ideal.span_mono (by simp)
    have := L1BP3.hdimle O ϖ this
    rw [hdim] at this; exact absurd this (by decide)

  haveI hlocz : IsLocalization.AtPrime O' (maximalIdeal O') :=
    IsLocalization.of_le_isUnit (fun x hx => by simp [mem_nonunits_iff] at hx; exact hx)
  haveI : Algebra.FormallyUnramified O O' := by
    have hU : Algebra.FormallyUnramified O (Localization.AtPrime (maximalIdeal O')) :=
      ‹Algebra.IsUnramifiedAt O (maximalIdeal O')›
    let e : Localization.AtPrime (maximalIdeal O') ≃ₐ[O'] O' :=
      IsLocalization.algEquiv (maximalIdeal O').primeCompl (Localization.AtPrime (maximalIdeal O')) O'
    exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars O)
  have hmap : (maximalIdeal O).map φ = maximalIdeal O' := Algebra.FormallyUnramified.map_maximalIdeal
  have hmax' : maximalIdeal O' = Ideal.span {φ ϖ, φ s} := by
    rw [← hmap, hmax, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  have hspan' : (maximalIdeal O').spanFinrank ≤ 2 := by
    rw [hmax']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))

  have hsreg : φ s ∈ nonZeroDivisors O' :=
    L1BP3.toNZD O' (φ s) ((IsSMulRegular.of_ne_zero hs0).of_flat (S := O'))

  set I : Ideal O' := Ideal.span {φ s} with hI
  have hIne : I ≠ ⊤ := by
    intro htop
    have : φ s ∈ maximalIdeal O' := by rw [hmax']; exact Ideal.subset_span (by simp)
    exact (mem_maximalIdeal _).mp this (Ideal.span_singleton_eq_top.mp htop)
  haveI : Nontrivial (O' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : IsLocalRing (O' ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (O' ⧸ I) := inferInstance
  have hmax'' : maximalIdeal (O' ⧸ I) = Ideal.span {Ideal.Quotient.mk I (φ ϖ)} := by
    have h1 : (maximalIdeal O').map (Ideal.Quotient.mk I) = maximalIdeal (O' ⧸ I) := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (IsLocalRing.maximalIdeal.isMaximal O') with h | h
      · exfalso
        have hI𝔪 : I ≤ maximalIdeal O' := by
          rw [hI, Ideal.span_le, Set.singleton_subset_iff, hmax']; exact Ideal.subset_span (by simp)
        have h1mem : (1 : O' ⧸ I) ∈ (maximalIdeal O').map (Ideal.Quotient.mk I) := by rw [h]; trivial
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1mem
        obtain ⟨m, hm, hm1⟩ := h1mem
        rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hm1
        apply (IsLocalRing.maximalIdeal.isMaximal O').ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : O') = m - (m - 1) := by ring
        rw [this]; exact Ideal.sub_mem _ hm (hI𝔪 hm1)
      · exact IsLocalRing.eq_maximalIdeal h
    rw [← h1, hmax', Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl : φ s ∈ I)]
    apply le_antisymm
    · rw [Ideal.span_le]; rintro x (rfl | rfl)
      · exact Ideal.subset_span rfl
      · exact Ideal.zero_mem _
    · exact Ideal.span_mono (by simp)

  set J : Ideal O := Ideal.span {s} with hJ
  have hIJ : I = J.map φ := by rw [hI, hJ, Ideal.map_span, Set.image_singleton]
  have hregJ : IsSMulRegular (O ⧸ J) ϖ := by

    let eD : O ⧸ J ≃+* D := (Ideal.quotEquivOfEq (hJ.trans hker.symm)).trans (RingHom.quotientKerEquivOfSurjective hπ)
    have heD : ∀ x : O, eD (Ideal.Quotient.mk J x) = π x := fun x => rfl
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : Ideal.Quotient.mk J (ϖ * a) = Ideal.Quotient.mk J (ϖ * b) := by
      simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hab
    have h2 := congrArg eD h1
    rw [heD, heD, map_mul, map_mul] at h2
    have h3 : π a = π b := mul_left_cancel₀ hπϖ h2
    apply eD.injective
    rw [heD, heD]; exact h3
  have hregT : IsSMulRegular (O' ⊗[O] (O ⧸ J)) (φ ϖ) :=
    hregJ.of_flat_of_isBaseChange (TensorProduct.isBaseChange O (O ⧸ J) O')
  let tq : (O' ⧸ I) ≃ₐ[O'] O' ⊗[O] (O ⧸ J) :=
    (Ideal.quotientEquivAlgOfEq O' hIJ).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot O' J)
  have hregQ : IsSMulRegular (O' ⧸ I) (φ ϖ) := by
    intro a b hab
    apply tq.injective
    apply hregT
    show φ ϖ • tq a = φ ϖ • tq b
    rw [← map_smul, ← map_smul]
    exact congrArg tq hab
  have hϖreg : Ideal.Quotient.mk I (φ ϖ) ∈ nonZeroDivisors (O' ⧸ I) := by
    apply L1BP3.toNZD
    intro a b hab
    exact hregQ (by simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, smul_eq_mul] using hab)

  have hϖne : Ideal.span {Ideal.Quotient.mk I (φ ϖ)} ≠ (⊤ : Ideal (O' ⧸ I)) := by
    intro htop
    have hmem : Ideal.Quotient.mk I (φ ϖ) ∈ maximalIdeal (O' ⧸ I) := by rw [hmax'']; exact Ideal.subset_span rfl
    exact (mem_maximalIdeal _).mp hmem (Ideal.span_singleton_eq_top.mp htop)
  have hdimQ1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (O' ⧸ I) := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hϖreg
    haveI : Nontrivial ((O' ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I (φ ϖ)}) := Ideal.Quotient.nontrivial_iff.mpr hϖne
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim ((O' ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I (φ ϖ)}) :=
      ringKrullDim_nonneg_of_nontrivial
    calc (1 : WithBot ℕ∞) = 0 + 1 := by norm_num
      _ ≤ ringKrullDim ((O' ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I (φ ϖ)}) + 1 := add_le_add h0 le_rfl
      _ ≤ ringKrullDim (O' ⧸ I) := h
  have hspanQ : (maximalIdeal (O' ⧸ I)).spanFinrank ≤ 1 := by
    rw [hmax'']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)).trans (by rw [Set.ncard_singleton])
  haveI hregQ' : IsRegularLocalRing (O' ⧸ I) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (le_trans (by exact_mod_cast hspanQ) hdimQ1)
  have hdimQle : ringKrullDim (O' ⧸ I) ≤ 1 := L1BP3.hdimle (O' ⧸ I) _ hmax''
  obtain ⟨hdomQ, -⟩ := IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one (O' ⧸ I) hdimQle
  haveI := hdomQ
  have hprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp hdomQ
  have hnf : ¬ IsField (O' ⧸ I) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax'', Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hϖreg
  have hdvr : IsDiscreteValuationRing (O' ⧸ I) := by
    have hprinc : Submodule.IsPrincipal (maximalIdeal (O' ⧸ I)) :=
      ⟨⟨Ideal.Quotient.mk I (φ ϖ), by rw [hmax'', Ideal.submodule_span_eq]⟩⟩
    exact ((IsDiscreteValuationRing.TFAE (O' ⧸ I) hnf).out 4 0).mp hprinc

  have hge : (2 : WithBot ℕ∞) ≤ ringKrullDim O' := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hsreg
    calc (2 : WithBot ℕ∞) = 1 + 1 := by norm_num
      _ ≤ ringKrullDim (O' ⧸ I) + 1 := add_le_add hdimQ1 le_rfl
      _ ≤ ringKrullDim O' := h
  have hle : ringKrullDim O' ≤ 2 := (ringKrullDim_le_spanFinrank_maximalIdeal O').trans (by exact_mod_cast hspan')
  have hdim' : ringKrullDim O' = 2 := le_antisymm hle hge
  have hreg : IsRegularLocalRing O' :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le O' (by rw [hdim']; exact_mod_cast hspan')
  exact ⟨hreg, hdim', hmax', hprime, ⟨hdomQ, hdvr⟩⟩

end S_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair
end P2MW
export P2MW.S_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair (solution)
