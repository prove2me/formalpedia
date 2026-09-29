-- Prove2me | solution 1 for Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6c536828-b279-5ab5-9a75-8cf36d3329a0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton

set_option autoImplicit false

universe u

namespace FinSuppLen

open IsLocalizedModule

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {S : Type u} [CommRing S] [Algebra k S]

noncomputable abbrev loclen (𝔪 : MaximalSpectrum S) (H : Type u) [AddCommGroup H] [Module S H] : ℕ∞ :=
  Module.length (Localization.AtPrime 𝔪.asIdeal) (LocalizedModule 𝔪.asIdeal.primeCompl H)

theorem loclen_of_equiv_quotient (N : Type u) [AddCommGroup N] [Module S N]
    (𝔪₀ : Ideal S) (e : N ≃ₗ[S] S ⧸ 𝔪₀) (𝔪 : MaximalSpectrum S) :
    loclen 𝔪 N = Module.length (Localization.AtPrime 𝔪.asIdeal)
      (Localization.AtPrime 𝔪.asIdeal ⧸ 𝔪₀.map (algebraMap S (Localization.AtPrime 𝔪.asIdeal))) := by
  set A := Localization.AtPrime 𝔪.asIdeal
  have hbc := IsLocalizedModule.isBaseChange 𝔪.asIdeal.primeCompl A
    (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl N)
  let e1 : LocalizedModule 𝔪.asIdeal.primeCompl N ≃ₗ[A] TensorProduct S A N := hbc.equiv.symm
  let e2 : TensorProduct S A N ≃ₗ[A] TensorProduct S A (S ⧸ 𝔪₀) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e
  let e3 : TensorProduct S A (S ⧸ 𝔪₀) ≃ₗ[A] A ⧸ 𝔪₀.map (algebraMap S A) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A 𝔪₀).toLinearEquiv.symm
  exact (e1.trans (e2.trans e3)).length_eq

theorem loclen_eq_one_of_equiv_quotient (N : Type u) [AddCommGroup N] [Module S N]
    (𝔪₀ : Ideal S) (h𝔪₀ : 𝔪₀.IsMaximal) (e : N ≃ₗ[S] S ⧸ 𝔪₀) :
    loclen ⟨𝔪₀, h𝔪₀⟩ N = 1 := by
  rw [loclen_of_equiv_quotient N 𝔪₀ e ⟨𝔪₀, h𝔪₀⟩]
  change Module.length (Localization.AtPrime 𝔪₀) (Localization.AtPrime 𝔪₀ ⧸ 𝔪₀.map (algebraMap S _)) = 1
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  haveI : IsSimpleModule (Localization.AtPrime 𝔪₀)
      (Localization.AtPrime 𝔪₀ ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪₀)) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one _ _

theorem loclen_eq_zero_of_equiv_quotient (N : Type u) [AddCommGroup N] [Module S N]
    (𝔪₀ : Ideal S) (h𝔪₀ : 𝔪₀.IsMaximal) (e : N ≃ₗ[S] S ⧸ 𝔪₀) (𝔪 : MaximalSpectrum S)
    (h : 𝔪 ≠ ⟨𝔪₀, h𝔪₀⟩) : loclen 𝔪 N = 0 := by
    rw [loclen_of_equiv_quotient N 𝔪₀ e 𝔪]

    have hne : ¬ 𝔪₀ ≤ 𝔪.asIdeal := by
      intro hle
      apply h
      have := h𝔪₀.eq_of_le 𝔪.isMaximal.ne_top hle
      exact MaximalSpectrum.ext this.symm
    obtain ⟨r, hr0, hr⟩ := Set.not_subset.mp hne
    have hu : IsUnit (algebraMap S (Localization.AtPrime 𝔪.asIdeal) r) :=
      IsLocalization.map_units (M := 𝔪.asIdeal.primeCompl) _ ⟨r, hr⟩
    have htop : 𝔪₀.map (algebraMap S (Localization.AtPrime 𝔪.asIdeal)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hr0) hu
    rw [htop]
    haveI : Subsingleton (Localization.AtPrime 𝔪.asIdeal ⧸ (⊤ : Ideal (Localization.AtPrime 𝔪.asIdeal))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero

theorem finrank_eq_one_of_equiv_quotient [Algebra.FiniteType k S] (N : Type u) [AddCommGroup N] [Module S N]
    [Module k N] [IsScalarTower k S N]
    (𝔪₀ : Ideal S) (h𝔪₀ : 𝔪₀.IsMaximal) (e : N ≃ₗ[S] S ⧸ 𝔪₀) : Module.finrank k N = 1 := by
  letI : Field (S ⧸ 𝔪₀) := Ideal.Quotient.field 𝔪₀
  haveI : IsJacobsonRing k := inferInstance
  haveI : Module.Finite k (S ⧸ 𝔪₀) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ 𝔪₀)
  haveI : Algebra.IsIntegral k (S ⧸ 𝔪₀) := Algebra.IsIntegral.of_finite k (S ⧸ 𝔪₀)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S ⧸ 𝔪₀)
  have h1 : Module.finrank k (S ⧸ 𝔪₀) = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId k (S ⧸ 𝔪₀)) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [← h1]
  exact (e.restrictScalars k).finrank_eq

theorem loclen_eq_add (H : Type u) [AddCommGroup H] [Module S H] (N : Submodule S H) (𝔪 : MaximalSpectrum S) :
    loclen 𝔪 H = loclen 𝔪 N + loclen 𝔪 (H ⧸ N) := by
  set p := 𝔪.asIdeal.primeCompl
  set A := Localization.AtPrime 𝔪.asIdeal
  let f := IsLocalizedModule.map p (LocalizedModule.mkLinearMap p N) (LocalizedModule.mkLinearMap p H) N.subtype
  let g := IsLocalizedModule.map p (LocalizedModule.mkLinearMap p H) (LocalizedModule.mkLinearMap p (H ⧸ N)) N.mkQ
  have hf : Function.Injective f := IsLocalizedModule.map_injective p _ _ _ N.injective_subtype
  have hg : Function.Surjective g := IsLocalizedModule.map_surjective p _ _ _ (Submodule.mkQ_surjective N)
  have hfg : Function.Exact f g := LocalizedModule.map_exact p _ _ (LinearMap.exact_subtype_mkQ N)
  exact Module.length_eq_add_of_exact (f.extendScalarsOfIsLocalization p A) (g.extendScalarsOfIsLocalization p A)
    hf hg hfg

theorem subsingleton_submodule (H : Type u) [AddCommGroup H] [Module S H] (N : Submodule S H) (𝔪 : MaximalSpectrum S)
    (h : Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl N) := by
  set p := 𝔪.asIdeal.primeCompl
  let f := IsLocalizedModule.map p (LocalizedModule.mkLinearMap p N) (LocalizedModule.mkLinearMap p H) N.subtype
  have hf : Function.Injective f := IsLocalizedModule.map_injective p _ _ _ N.injective_subtype
  exact hf.subsingleton

theorem subsingleton_quotient (H : Type u) [AddCommGroup H] [Module S H] (N : Submodule S H) (𝔪 : MaximalSpectrum S)
    (h : Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl (H ⧸ N)) := by
  set p := 𝔪.asIdeal.primeCompl
  let g := IsLocalizedModule.map p (LocalizedModule.mkLinearMap p H) (LocalizedModule.mkLinearMap p (H ⧸ N)) N.mkQ
  have hg : Function.Surjective g := IsLocalizedModule.map_surjective p _ _ _ (Submodule.mkQ_surjective N)
  exact hg.subsingleton

theorem finrank_eq_sum_aux [Algebra.FiniteType k S] (T : Finset (MaximalSpectrum S)) (d : ℕ) :
    ∀ (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H] [Module.Finite k H],
      (∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) →
      Module.finrank k H = d → (Module.finrank k H : ℕ∞) = ∑ 𝔪 ∈ T, loclen 𝔪 H := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro H _ _ _ _ _ hT hd
  by_cases hH : Subsingleton H
  · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
    symm
    refine Finset.sum_eq_zero fun 𝔪 _ => ?_
    haveI : Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
      have hinj := IsLocalizedModule.map_injective 𝔪.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H) (LocalizedModule.mkLinearMap 𝔪.asIdeal.primeCompl H)
        (0 : H →ₗ[S] H) (fun a b _ => Subsingleton.elim a b)
      refine ⟨fun a b => hinj ?_⟩
      simp
    exact Module.length_eq_zero
  · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    haveI : IsArtinian S H := isArtinian_of_tower k (inferInstance : IsArtinian k H)
    haveI : IsAtomic (Submodule S H) :=
      isAtomic_of_orderBot_wellFounded_lt (wellFounded_lt : WellFounded ((· < ·) : Submodule S H → Submodule S H → Prop))
    obtain ⟨N, hNat⟩ := IsAtomic.exists_atom (Submodule S H)
    haveI hN : IsSimpleModule S N := isSimpleModule_iff_isAtom.mpr hNat
    obtain ⟨𝔪₀, h𝔪₀, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hN
    have hN1 : Module.finrank k N = 1 := finrank_eq_one_of_equiv_quotient (k := k) N 𝔪₀ h𝔪₀ e

    have hmemT : (⟨𝔪₀, h𝔪₀⟩ : MaximalSpectrum S) ∈ T := by
      by_contra hnot
      have hsub := subsingleton_submodule H N ⟨𝔪₀, h𝔪₀⟩ (hT _ hnot)
      have h0 : loclen ⟨𝔪₀, h𝔪₀⟩ N = 0 := @Module.length_eq_zero _ _ _ _ _ hsub
      rw [loclen_eq_one_of_equiv_quotient N 𝔪₀ h𝔪₀ e] at h0
      exact one_ne_zero h0

    haveI : Module.Finite k (H ⧸ N) :=
      Module.Finite.of_surjective (N.mkQ.restrictScalars k) (Submodule.mkQ_surjective N)
    have hq : Module.finrank k (H ⧸ N) = Module.finrank k H - Module.finrank k N := Submodule.finrank_quotient N
    have hpos : 0 < Module.finrank k H := Module.finrank_pos
    have hlt : Module.finrank k (H ⧸ N) < d := by rw [hq, hN1, ← hd]; omega
    have ihq := ih _ hlt (H ⧸ N) (fun 𝔪 h𝔪 => subsingleton_quotient H N 𝔪 (hT 𝔪 h𝔪)) rfl

    have hsumN : ∑ 𝔪 ∈ T, loclen 𝔪 N = 1 := by
      rw [Finset.sum_eq_single_of_mem (⟨𝔪₀, h𝔪₀⟩ : MaximalSpectrum S) hmemT
        (fun 𝔪 _ h𝔪 => loclen_eq_zero_of_equiv_quotient N 𝔪₀ h𝔪₀ e 𝔪 h𝔪)]
      exact loclen_eq_one_of_equiv_quotient N 𝔪₀ h𝔪₀ e
    calc (Module.finrank k H : ℕ∞) = ((1 + Module.finrank k (H ⧸ N) : ℕ) : ℕ∞) := by
          congr 1; rw [hq, hN1]; omega
      _ = 1 + ∑ 𝔪 ∈ T, loclen 𝔪 (H ⧸ N) := by rw [Nat.cast_add, Nat.cast_one, ihq]
      _ = ∑ 𝔪 ∈ T, loclen 𝔪 N + ∑ 𝔪 ∈ T, loclen 𝔪 (H ⧸ N) := by rw [hsumN]
      _ = ∑ 𝔪 ∈ T, loclen 𝔪 H := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun 𝔪 _ => (loclen_eq_add H N 𝔪).symm

omit [IsAlgClosed k] in

theorem isMaximal_of_isPrime_of_annihilator_le [Algebra.FiniteType k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module.Finite S H]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H))
    (P : Ideal S) (hP : P.IsPrime) (hle : Module.annihilator S H ≤ P) : P.IsMaximal := by
  classical
  haveI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  have hjac : P.jacobson = P := (isJacobsonRing_iff_prime_eq.mp inferInstance) P hP

  have key : ∀ (J : Ideal S) (hJ : J.IsMaximal), P ≤ J → (⟨J, hJ⟩ : MaximalSpectrum S) ∈ T := by
    intro J hJ hPJ
    by_contra hnot
    have hsub := hT ⟨J, hJ⟩ hnot
    have hmem : (⟨J, hJ.isPrime⟩ : PrimeSpectrum S) ∈ Module.support S H :=
      Module.mem_support_iff_of_finite.mpr (hle.trans hPJ)
    exact (@not_subsingleton _ (Module.mem_support_iff.mp hmem)) hsub
  let T' := T.filter (fun 𝔪 => P ≤ 𝔪.asIdeal)
  have hprod : T'.prod (fun 𝔪 => 𝔪.asIdeal) ≤ P := by
    rw [← hjac]
    refine le_sInf fun J hJ => ?_
    obtain ⟨hPJ, hJmax⟩ := hJ
    have hJT' : (⟨J, hJmax⟩ : MaximalSpectrum S) ∈ T' := Finset.mem_filter.mpr ⟨key J hJmax hPJ, hPJ⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hJT')
  obtain ⟨𝔪, h𝔪T', h𝔪P⟩ := (Ideal.IsPrime.prod_le hP).mp hprod
  have hP𝔪 : P ≤ 𝔪.asIdeal := (Finset.mem_filter.mp h𝔪T').2
  rw [le_antisymm hP𝔪 h𝔪P]
  exact 𝔪.isMaximal

omit [IsAlgClosed k] in
theorem finite_of_forall_subsingleton [Algebra.FiniteType k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H] [Module.Finite S H]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Module.Finite k H := by
  set J := Module.annihilator S H

  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    refine Ring.krullDimLE_zero_iff.mpr fun I hI => ?_
    have hle : Module.annihilator S H ≤ I.comap (Ideal.Quotient.mk J) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact I.zero_mem
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ I.comap (Ideal.Quotient.mk J) := by
      rw [Ideal.mk_ker]; exact hle
    haveI hPmax : (I.comap (Ideal.Quotient.mk J)).IsMaximal :=
      isMaximal_of_isPrime_of_annihilator_le (k := k) H T hT _ (Ideal.comap_isPrime _ I) hle
    have := Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (m := I.comap (Ideal.Quotient.mk J)) hker
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  haveI : Module.Finite k (S ⧸ J) := (Module.finite_iff_krullDimLE_zero k (S ⧸ J)).mpr hdim

  letI : Module (S ⧸ J) H := Module.quotientAnnihilator
  haveI : IsScalarTower S (S ⧸ J) H := Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator S H)
  haveI : IsScalarTower k (S ⧸ J) H := Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator S H)
  haveI : Module.Finite (S ⧸ J) H := Module.Finite.of_restrictScalars_finite S (S ⧸ J) H
  exact Module.Finite.trans (S ⧸ J) H

end FinSuppLen

open FinSuppLen in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H] [Module.Finite S H]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Module.Finite k H ∧ IsFiniteLength S H ∧
      (Module.finrank k H : ℕ∞) =
        ∑ 𝔪 ∈ T, Module.length (Localization.AtPrime 𝔪.asIdeal) (LocalizedModule 𝔪.asIdeal.primeCompl H) := by
  haveI hfin : Module.Finite k H := finite_of_forall_subsingleton (k := k) H T hT
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : IsNoetherian S H := inferInstance
  haveI : IsArtinian S H := isArtinian_of_tower k (inferInstance : IsArtinian k H)
  refine ⟨hfin, isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  exact finrank_eq_sum_aux (k := k) T (Module.finrank k H) H hT rfl

end S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
end P2MW
export P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton (solution)
