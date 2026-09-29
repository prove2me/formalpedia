-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_of_isReduced_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f03d6646-6b6f-5109-9474-d5142a71ef00

import Mathlib
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open Coalgebra HopfAlgebra HopfAlgebra.HopfTower WithConv

universe u v w

namespace SmoothCase

section Points

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type*} [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_algHom_ker_eq (m : Ideal R) [hm : m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, RingHom.ker φ = m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  let e : k ≃ₐ[k] R ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(e.symm : R ⧸ m →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext x
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_algHom,
    map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

omit [IsAlgClosed k] [Algebra.FiniteType k R] in
theorem ker_isMaximal (φ : R →ₐ[k] k) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ fun c => ⟨algebraMap k R c, φ.commutes c⟩

scoped instance ker_isPrime' {S : Type*} [CommRing S] [Algebra k S] (φ : S →ₐ[k] k) :
    (RingHom.ker φ).IsPrime :=
  (RingHom.ker_isMaximal_of_surjective φ fun c => ⟨algebraMap k S c, φ.commutes c⟩).isPrime

theorem exists_algHom [Nontrivial R] : ∃ φ : R →ₐ[k] k, True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨φ, -⟩ := exists_algHom_ker_eq (k := k) m
  exact ⟨φ, trivial⟩

end Points

section Transport

variable {k : Type u} [Field k] {K : Type v} [CommRing K] [HopfAlgebra k K]
  {H : Type w} [CommRing H] [HopfAlgebra k H] [Algebra K H] [IsScalarTower k K H]

theorem flat_localization_of_algEquiv (τ : H ≃ₐ[k] H) (σ : K ≃ₐ[k] K)
    (hτσ : ∀ x, τ (algebraMap K H x) = algebraMap K H (σ x))
    (P Q : Ideal H) [P.IsPrime] [Q.IsPrime] (hPQ : ∀ x, x ∈ P ↔ τ x ∈ Q)
    [Module.Flat K (Localization.AtPrime Q)] : Module.Flat K (Localization.AtPrime P) := by
  have hmap : P.primeCompl.map (τ : H ≃+* H).toMonoidHom = Q.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    change (∃ x, x ∉ P ∧ τ x = y) ↔ _
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun h => hx ((hPQ x).mpr h)
    · intro hy
      refine ⟨τ.symm y, fun h => hy ?_, by simp⟩
      simpa using (hPQ _).mp h
  let e : Localization.AtPrime P ≃+* Localization.AtPrime Q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q)
      (τ : H ≃+* H) hmap
  have he : ∀ x : H, e (algebraMap H (Localization.AtPrime P) x) =
      algebraMap H (Localization.AtPrime Q) (τ x) := fun x =>
    IsLocalization.ringEquivOfRingEquiv_eq hmap x
  have hQ : (algebraMap K (Localization.AtPrime Q)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : algebraMap K (Localization.AtPrime P) =
      (e.symm : _ →+* _).comp ((algebraMap K (Localization.AtPrime Q)).comp (σ : K →+* K)) := by
    ext x
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply K H (Localization.AtPrime Q), ← hτσ, ← he,
      RingEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply]
  rw [← RingHom.flat_algebraMap_iff (R := K) (S := Localization.AtPrime P), hcomp]
  exact RingHom.Flat.comp (RingHom.Flat.comp (.of_bijective σ.bijective) hQ) (.of_bijective e.symm.bijective)

scoped instance augIdeal_isMaximal : (augIdeal k H).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom k H)
    fun c => ⟨algebraMap k H c, by simp⟩

variable [IsHopfTower k K H]

theorem translate_algebraMap' (g : H →ₐ[k] k) (x : K) :
    translateEquiv k H g (algebraMap K H x) =
      algebraMap K H (translateEquiv k K (g.comp (IsScalarTower.toAlgHom k K H)) x) :=
  translate_algebraMap k K H (IsHopfTower.comul_algebraMap (k := k)) g x

theorem mem_ker_iff_translate_mem (g : H →ₐ[k] k) (x : H) :
    x ∈ RingHom.ker g ↔ translateEquiv k H g x ∈ augIdeal k H := by
  rw [← comap_translate_augIdeal g, Ideal.mem_comap]
  rfl

theorem flat_localization_ker (g : H →ₐ[k] k) [(RingHom.ker g).IsPrime]
    [Module.Flat K (Localization.AtPrime (augIdeal k H))] :
    Module.Flat K (Localization.AtPrime (RingHom.ker g)) :=
  flat_localization_of_algEquiv (translateEquiv k H g)
    (translateEquiv k K (g.comp (IsScalarTower.toAlgHom k K H))) (translate_algebraMap' g)
    (RingHom.ker g) (augIdeal k H) (mem_ker_iff_translate_mem g)

theorem flat_localization_augIdeal (g : H →ₐ[k] k) [(RingHom.ker g).IsPrime]
    [Module.Flat K (Localization.AtPrime (RingHom.ker g))] :
    Module.Flat K (Localization.AtPrime (augIdeal k H)) := by
  refine flat_localization_of_algEquiv (translateEquiv k H g).symm
    (translateEquiv k K (g.comp (IsScalarTower.toAlgHom k K H))).symm (fun x => ?_)
    (augIdeal k H) (RingHom.ker g) (fun x => ?_)
  · rw [AlgEquiv.symm_apply_eq, translate_algebraMap', AlgEquiv.apply_symm_apply]
  · rw [mem_ker_iff_translate_mem, AlgEquiv.apply_symm_apply]

variable [IsAlgClosed k] [Algebra.FiniteType k H]

theorem flat_of_flat_localization_augIdeal [Module.Flat K (Localization.AtPrime (augIdeal k H))] :
    Module.Flat K H := by
  refine Module.flat_of_isLocalized_maximal H H (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap H (Localization.AtPrime P)) fun P hP => ?_
  obtain ⟨g, hg⟩ := exists_algHom_ker_eq (k := k) P
  subst hg
  exact flat_localization_ker g

end Transport

section Domain

variable {K : Type v} [CommRing K] [IsNoetherianRing K] [IsReduced K] [Nontrivial K]

theorem exists_isDomain_localization_away : ∃ f : K, IsDomain (Localization.Away f) := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing K
  obtain ⟨𝔭, h𝔭⟩ : (minimalPrimes K).Nonempty := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal K
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal K) ≤ m from bot_le)
    exact ⟨p, hp⟩
  have h𝔭p : 𝔭.IsPrime := h𝔭.1.1

  have hx : ∀ 𝔮 : (hfin.toFinset.erase 𝔭 : Finset (Ideal K)), ∃ x : K, x ∈ (𝔮 : Ideal K) ∧ x ∉ 𝔭 := by
    rintro ⟨𝔮, h𝔮⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔮
    by_contra h
    push_neg at h
    have hle : 𝔮 ≤ 𝔭 := fun x hx => h x hx
    exact h𝔮.1 (le_antisymm hle (h𝔭.2 ⟨h𝔮.2.1.1, bot_le⟩ hle))
  choose x hx𝔮 hx𝔭 using hx
  let f : K := ∏ 𝔮 : (hfin.toFinset.erase 𝔭 : Finset (Ideal K)), x 𝔮
  have hf𝔭 : f ∉ 𝔭 := by
    intro hf
    obtain ⟨𝔮, -, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := h𝔭p)).mp hf
    exact hx𝔭 𝔮 h

  have hf𝔮 : ∀ 𝔮 ∈ minimalPrimes K, 𝔮 ≠ 𝔭 → f ∈ 𝔮 := fun 𝔮 h𝔮 hne => by
    have hmem : 𝔮 ∈ hfin.toFinset.erase 𝔭 := by
      rw [Finset.mem_erase, Set.Finite.mem_toFinset]; exact ⟨hne, h𝔮⟩
    have := Finset.dvd_prod_of_mem (fun 𝔮 : (hfin.toFinset.erase 𝔭 : Finset (Ideal K)) => x 𝔮)
      (Finset.mem_univ (⟨𝔮, hmem⟩ : (hfin.toFinset.erase 𝔭 : Finset (Ideal K))))
    exact Ideal.mem_of_dvd _ this (hx𝔮 ⟨𝔮, hmem⟩)

  have hpf : ∀ y ∈ 𝔭, f * y = 0 := fun y hy => by
    have hmem : f * y ∈ nilradical K := by
      rw [nilradical, ← Ideal.sInf_minimalPrimes, Ideal.minimalPrimes]
      change f * y ∈ sInf (minimalPrimes K)
      rw [Submodule.mem_sInf]
      intro 𝔮 h𝔮
      by_cases hne : 𝔮 = 𝔭
      · subst hne; exact Ideal.mul_mem_left _ f hy
      · exact Ideal.mul_mem_right y _ (hf𝔮 𝔮 h𝔮 hne)
    simpa [nilradical_eq_zero] using hmem
  refine ⟨f, ?_⟩

  have hntriv : Nontrivial (Localization.Away f) := by
    refine ⟨⟨algebraMap K _ 1, 0, fun h => hf𝔭 ?_⟩⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at h
    obtain ⟨⟨m, n, rfl⟩, hm⟩ := h
    simp only [mul_one] at hm
    exact h𝔭p.mem_of_pow_mem n (by rw [hm]; exact 𝔭.zero_mem)
  have hnzd : NoZeroDivisors (Localization.Away f) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨⟨ya, sa⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) a
    obtain ⟨⟨yb, sb⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hab
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := hab
    have hmem : f ^ n * (ya * yb) ∈ 𝔭 := by simp only at hc; rw [hc]; exact 𝔭.zero_mem
    rcases h𝔭p.mem_or_mem (h𝔭p.mem_or_mem hmem |>.resolve_left
      (fun h => hf𝔭 (h𝔭p.mem_of_pow_mem n h))) with h | h
    · left
      rw [IsLocalization.mk'_eq_zero_iff]
      exact ⟨⟨f, Submonoid.mem_powers f⟩, hpf ya h⟩
    · right
      rw [IsLocalization.mk'_eq_zero_iff]
      exact ⟨⟨f, Submonoid.mem_powers f⟩, hpf yb h⟩
  exact NoZeroDivisors.to_isDomain _

end Domain

section Generic

variable {K : Type v} [CommRing K] {H : Type w} [CommRing H] [Algebra K H] (f : K)

local notation "Kf" => Localization.Away f
local notation "Hf" => Localization (Algebra.algebraMapSubmonoid H (Submonoid.powers f))

scoped instance isLocalization_away_Hf : IsLocalization.Away (algebraMap K H f) Hf := by
  have : Algebra.algebraMapSubmonoid H (Submonoid.powers f) = Submonoid.powers (algebraMap K H f) :=
    Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← this]
  infer_instance

theorem finiteType_H_Hf : Algebra.FiniteType H Hf :=
  haveI := IsLocalization.Away.finitePresentation (algebraMap K H f) (S := Hf)
  inferInstance

theorem algebraMap_Kf_Hf_injective (hinj : Function.Injective (algebraMap K H)) :
    Function.Injective (algebraMap Kf Hf) :=
  IsLocalization.map_injective_of_injective (Submonoid.powers f) Kf Hf hinj

variable {k : Type u} [Field k] [hk : IsAlgClosed k] [HopfAlgebra k K] [HopfAlgebra k H]
  [IsScalarTower k K H] [hK : Algebra.FiniteType k K] [hH : Algebra.FiniteType k H]

include hH in
theorem finiteType_Kf_Hf : Algebra.FiniteType Kf Hf :=
  haveI : Algebra.FiniteType K H := Algebra.FiniteType.of_restrictScalars_finiteType k K H
  haveI : Algebra.FiniteType K Hf := Algebra.FiniteType.trans (S := H) inferInstance (finiteType_H_Hf f)
  Algebra.FiniteType.of_restrictScalars_finiteType K Kf Hf

theorem finiteType_k_Hf : Algebra.FiniteType k Hf :=
  Algebra.FiniteType.trans (S := H) inferInstance (finiteType_H_Hf f)

variable {f}

include hk hK hH

theorem exists_flat_localization_of_flat (b : Hf) (hb : ∀ n : ℕ, b ^ n ≠ 0)
    [Module.Flat K (Localization (Submonoid.powers b))] :
    ∃ (P : Ideal H) (_ : P.IsMaximal), Module.Flat K (Localization.AtPrime P) := by

  haveI : Nontrivial (Localization (Submonoid.powers b)) := by
    refine ⟨⟨algebraMap Hf _ 1, 0, fun h => ?_⟩⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers b)] at h
    obtain ⟨⟨m, n, rfl⟩, hm⟩ := h
    exact hb n (by simpa using hm)
  haveI : Algebra.FiniteType k (Localization (Submonoid.powers b)) :=
    Algebra.FiniteType.trans (S := Hf) (finiteType_k_Hf f) inferInstance
  obtain ⟨𝔑, h𝔑⟩ := Ideal.exists_maximal (Localization (Submonoid.powers b))
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (k := k) 𝔑

  have hker : Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑 =
      RingHom.ker (ψ.comp (IsScalarTower.toAlgHom k H (Localization (Submonoid.powers b)))) := by
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← hψ, RingHom.mem_ker]
  have hmax : (Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑).IsMaximal := by
    rw [hker]; exact ker_isMaximal _
  refine ⟨Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑, hmax, ?_⟩

  haveI : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid H (Submonoid.powers f)) (Submonoid.powers b))
      (Localization (Submonoid.powers b)) :=
    IsLocalization.localization_localization_isLocalization _ (Submonoid.powers b) _
  haveI h1 : IsLocalization.AtPrime (Localization.AtPrime 𝔑)
      (Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid H (Submonoid.powers f)) (Submonoid.powers b))
      (Localization.AtPrime 𝔑) 𝔑
  let e : Localization.AtPrime 𝔑 ≃ₐ[H]
      Localization.AtPrime (Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑) :=
    IsLocalization.algEquiv
      (Ideal.comap (algebraMap H (Localization (Submonoid.powers b))) 𝔑).primeCompl _ _
  exact Module.Flat.of_linearEquiv (e.toLinearEquiv.restrictScalars K).symm

variable (f)

theorem exists_flat_localization (hinj : Function.Injective (algebraMap K H)) [IsDomain Kf] :
    ∃ (P : Ideal H) (_ : P.IsMaximal), Module.Flat K (Localization.AtPrime P) := by
  haveI : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  haveI : Algebra.FiniteType Kf Hf := finiteType_Kf_Hf (k := k) (H := H) f
  obtain ⟨a, ha, hflat⟩ :=
    Module.Flat.exists_ne_zero_flat_localization_tensorProduct (A := Kf) (B := Hf) (M := Hf)
  have hb : ∀ n : ℕ, (algebraMap Kf Hf a) ^ n ≠ 0 := fun n h => by
    rw [← map_pow, ← (algebraMap Kf Hf).map_zero] at h
    have h' := algebraMap_Kf_Hf_injective f hinj h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (one_ne_zero (α := Kf)) (by simpa using h')
    · exact ha ((pow_eq_zero_iff hn.ne').mp h')

  haveI : Module.Flat Kf (Localization (Submonoid.powers (algebraMap Kf Hf a))) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.rid Hf (Localization (Submonoid.powers (algebraMap Kf Hf a)))).restrictScalars
        Kf).symm
  haveI : Module.Flat K Kf := IsLocalization.flat Kf (Submonoid.powers f)
  haveI : Module.Flat K (Localization (Submonoid.powers (algebraMap Kf Hf a))) :=
    Module.Flat.trans K Kf _
  exact exists_flat_localization_of_flat (k := k) (algebraMap Kf Hf a) hb

end Generic

section Flat

variable {k : Type u} [Field k] {K : Type v} [CommRing K] [hkK : HopfAlgebra k K]
  {H : Type w} [CommRing H] [HopfAlgebra k H]

include hkK in

theorem nontrivial_of_hopfAlgebra : Nontrivial K :=
  ⟨⟨1, 0, fun h => (one_ne_zero (α := k))
    (by simpa using congr(Coalgebra.counit (R := k) (A := K) $h))⟩⟩

variable [Algebra K H] [IsScalarTower k K H] [hT : IsHopfTower k K H] [hk : IsAlgClosed k]
  [hK : Algebra.FiniteType k K] [hH : Algebra.FiniteType k H] [IsReduced K]

include hT hk hK hH in

private theorem _root_.SmoothCase.flat (hinj : Function.Injective (algebraMap K H)) : Module.Flat K H := by
  haveI : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  haveI : Nontrivial K := nontrivial_of_hopfAlgebra (k := k)
  obtain ⟨f, hf⟩ := exists_isDomain_localization_away (K := K)
  haveI := hf
  obtain ⟨P, hP, hPflat⟩ := exists_flat_localization (k := k) f hinj
  obtain ⟨g, hg⟩ := exists_algHom_ker_eq (k := k) P
  subst hg
  haveI := hPflat
  haveI := flat_localization_augIdeal (K := K) g
  exact flat_of_flat_localization_augIdeal (k := k)

p2m_export "SmoothCase" "flat"
end Flat

section Twist

variable (k : Type u) [Field k] (K : Type v) [CommRing K] [HopfAlgebra k K]
  (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra K H] [IsScalarTower k K H]

def Twist (_σ : K →ₐ[k] K) : Type w := H

namespace Twist

variable (σ : K →ₐ[k] K)

scoped instance instCommRing : CommRing (Twist k K H σ) := inferInstanceAs (CommRing H)

noncomputable scoped instance instHopfAlgebra : HopfAlgebra k (Twist k K H σ) :=
  inferInstanceAs (HopfAlgebra k H)

scoped instance instFiniteType [Algebra.FiniteType k H] : Algebra.FiniteType k (Twist k K H σ) :=
  inferInstanceAs (Algebra.FiniteType k H)

noncomputable scoped instance instAlgebra : Algebra K (Twist k K H σ) :=
  ((IsScalarTower.toAlgHom k K H).comp σ).toRingHom.toAlgebra

theorem algebraMap_apply (x : K) :
    (algebraMap K (Twist k K H σ) x : H) = algebraMap K H (σ x) := rfl

scoped instance instIsScalarTower : IsScalarTower k K (Twist k K H σ) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k H c = algebraMap K H (σ (algebraMap k K c))
    rw [σ.commutes, ← IsScalarTower.algebraMap_apply]

end Twist
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.SmoothCase.Twist"

end Twist
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.SmoothCase.Twist"

section Faithful

variable {k : Type u} [Field k] {K : Type v} [CommRing K] [HopfAlgebra k K]
  {H : Type w} [CommRing H] [HopfAlgebra k H] [Algebra K H] [IsScalarTower k K H]
  [hT : IsHopfTower k K H] [hk : IsAlgClosed k] [hK : Algebra.FiniteType k K]
  [hH : Algebra.FiniteType k H]

include hT hk hK hH in

theorem smul_top_ne_top [Module.Flat K H] (hinj : Function.Injective (algebraMap K H))
    (m : Ideal K) [hm : m.IsMaximal] : m • (⊤ : Submodule K H) ≠ ⊤ := by
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
  let σ : K →ₐ[k] K := translate k K φ
  have hσ : Function.Injective σ := (translateEquiv k K φ).injective

  haveI : Nontrivial H := nontrivial_of_hopfAlgebra (k := k)
  haveI : Nontrivial (H ⊗[K] Twist k K H σ) := by
    have hj : Function.Injective (Algebra.linearMap K (Twist k K H σ)) := fun x y hxy =>
      hσ (hinj hxy)
    have h1 : Function.Injective ((Algebra.linearMap K (Twist k K H σ)).lTensor H) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hj
    exact (h1.comp (TensorProduct.rid K H).symm.injective).nontrivial
  haveI : Algebra.FiniteType K H := Algebra.FiniteType.of_restrictScalars_finiteType k K H
  haveI : Algebra.FiniteType K (Twist k K H σ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k K _
  haveI : Algebra.FiniteType H (H ⊗[K] Twist k K H σ) := Algebra.FiniteType.baseChange H
  haveI : Algebra.FiniteType K (H ⊗[K] Twist k K H σ) :=
    Algebra.FiniteType.trans (S := H) inferInstance inferInstance
  haveI : Algebra.FiniteType k (H ⊗[K] Twist k K H σ) :=
    Algebra.FiniteType.trans (S := K) inferInstance inferInstance

  obtain ⟨M, hM⟩ := Ideal.exists_maximal (H ⊗[K] Twist k K H σ)
  obtain ⟨β, -⟩ := exists_algHom_ker_eq (k := k) M
  let g₁ : H →ₐ[k] k := β.comp (Algebra.TensorProduct.includeLeft (S := k))
  let g₂ : Twist k K H σ →ₐ[k] k :=
    β.comp ((Algebra.TensorProduct.includeRight (R := K) (A := H) (B := Twist k K H σ)).restrictScalars k)
  have hrel : ∀ x : K, g₁ (algebraMap K H x) = g₂ (algebraMap K (Twist k K H σ) x) := fun x => by
    simp only [g₁, g₂, AlgHom.comp_apply, AlgHom.coe_restrictScalars', AlgHom.commutes,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.algebraMap_apply]

  let ιₐ : K →ₐ[k] H := IsScalarTower.toAlgHom k K H
  let g₂' : H →ₐ[k] k := g₂
  have hpts' : g₁.comp ιₐ = (g₂'.comp ιₐ).comp (translate k K φ) := by
    ext x; exact hrel x
  have hpts : toConv (g₁.comp ιₐ) = toConv (g₂'.comp ιₐ) * toConv φ := by
    rw [hpts', HopfTower.comp_translate]

  let w : H →ₐ[k] k := ofConv (toConv (g₂'.comp (HopfTower.antipodeAlgHom k H)) * toConv g₁)
  have hw : w.comp ιₐ = φ := by
    apply WithConv.toConv_injective
    have h1 := comp_antipodeAlgHom_convMul (g₂'.comp ιₐ)
    have h2 : (g₂'.comp ιₐ).comp (HopfTower.antipodeAlgHom k K) = (g₂'.comp (HopfTower.antipodeAlgHom k H)).comp ιₐ := by
      ext x
      simp only [AlgHom.comp_apply, HopfTower.antipodeAlgHom_apply, ιₐ, IsScalarTower.coe_toAlgHom',
        IsHopfTower.algebraMap_antipode]
    calc toConv (w.comp ιₐ)
        = toConv ((g₂'.comp (HopfTower.antipodeAlgHom k H)).comp ιₐ) * toConv (g₁.comp ιₐ) := by
          have := AlgHom.convMul_comp_bialgHom_distrib (toConv (g₂'.comp (HopfTower.antipodeAlgHom k H)))
            (toConv g₁) (IsHopfTower.toBialgHom k K H)
          exact congrArg toConv this
      _ = toConv ((g₂'.comp ιₐ).comp (HopfTower.antipodeAlgHom k K)) * (toConv (g₂'.comp ιₐ) * toConv φ) := by
          rw [h2, hpts]
      _ = toConv φ := by rw [← mul_assoc, h1, one_mul]

  intro htop
  have hle : m ≤ Ideal.comap (algebraMap K H) (RingHom.ker w) := fun x hx => by
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hx0 : φ x = 0 := by rw [← RingHom.mem_ker, hφ]; exact hx
    rw [← hx0, ← hw]
    rfl
  have h1 : (1 : H) ∈ m • (⊤ : Submodule K H) := by rw [htop]; exact Submodule.mem_top
  rw [Ideal.smul_top_eq_map] at h1
  have h1' : (1 : H) ∈ m.map (algebraMap K H) := h1
  have h2 : (1 : H) ∈ RingHom.ker w := (Ideal.map_le_iff_le_comap.mpr hle) h1'
  rw [RingHom.mem_ker, map_one] at h2
  exact one_ne_zero h2

end Faithful
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.SmoothCase.Twist"

end SmoothCase
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.SmoothCase.Twist P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.SmoothCase"

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {K : Type v} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K] [IsReduced K]
    {H : Type w} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H]
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K H) (IsScalarTower.toAlgHom k K H)
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    (hinj : Function.Injective (algebraMap K H)) :
    Module.FaithfullyFlat K H := by
  haveI : IsHopfTower k K H := ⟨hcomul, hcounit⟩
  haveI : Module.Flat K H := SmoothCase.flat (k := k) hinj
  have key : ∀ (m : Ideal K) [m.IsMaximal], m • (⊤ : Submodule K H) ≠ ⊤ := fun m _ =>
    SmoothCase.smul_top_ne_top (k := k) hinj m
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
  apply key m
  refine top_le_iff.mp ?_
  calc (⊤ : Submodule K H) = I • ⊤ := hI.symm
    _ ≤ m • ⊤ := Submodule.smul_mono_left hIm

end S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed (solution)
