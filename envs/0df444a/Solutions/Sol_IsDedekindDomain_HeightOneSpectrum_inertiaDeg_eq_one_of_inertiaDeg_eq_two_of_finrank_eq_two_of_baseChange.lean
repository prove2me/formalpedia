-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5f3c980e-eacd-5af6-805f-0eaf5f0513b9

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

namespace UQAux

theorem eq_top_of_forall_mem {K L K' M : Type} [Field K] [Field L] [Field K'] [Field M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M] [IsScalarTower K K' M]
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (S : Subalgebra K M) (hK' : ∀ k : K', algebraMap K' M k ∈ S) (hL : ∀ y : L, algebraMap L M y ∈ S) :
    S = ⊤ := by
  let S' : Subalgebra K' M :=
    { carrier := S
      mul_mem' := fun ha hb => S.mul_mem ha hb
      one_mem' := S.one_mem
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := hK' }
  have h : Algebra.adjoin K' (Set.range (algebraMap L M)) ≤ S' :=
    Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact hL y)
  rw [eq_top_iff]
  intro x _
  exact h (hcomp x)

theorem normal_of_compositum (K L K' M : Type) [Field K] [Field L] [Field K'] [Field M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [Normal K L] [Normal K K']
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M))) : Normal K M := by
  let fL : L →ₐ[K] M := IsScalarTower.toAlgHom K L M
  let fK : K' →ₐ[K] M := IsScalarTower.toAlgHom K K' M
  haveI hnL : Normal K fL.fieldRange := Normal.of_algEquiv (AlgEquiv.ofInjectiveField fL)
  haveI hnK : Normal K fK.fieldRange := Normal.of_algEquiv (AlgEquiv.ofInjectiveField fK)
  have htop : fL.fieldRange ⊔ fK.fieldRange = ⊤ := by
    have h := eq_top_of_forall_mem hcomp (fL.fieldRange ⊔ fK.fieldRange).toSubalgebra
      (fun k => (le_sup_right : fK.fieldRange ≤ fL.fieldRange ⊔ fK.fieldRange) ⟨k, rfl⟩)
      (fun y => (le_sup_left : fL.fieldRange ≤ fL.fieldRange ⊔ fK.fieldRange) ⟨y, rfl⟩)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (fL.fieldRange ⊔ fK.fieldRange).toSubalgebra := by rw [h]; trivial
    exact hx
  haveI : Normal K (fL.fieldRange ⊔ fK.fieldRange : IntermediateField K M) :=
    IntermediateField.normal_sup K M _ _
  exact Normal.of_algEquiv ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

theorem mul_self_eq_one (K L K' M : Type) [Field K] [Field L] [Field K'] [Field M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M]
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K K'] [IsGalois K K']
    (hL : Module.finrank K L = 2) (hK' : Module.finrank K K' = 2)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M))) (σ : M ≃ₐ[K] M) :
    σ * σ = 1 := by
  have hL1 : (σ * σ).restrictNormal L = 1 := by
    show AlgEquiv.restrictNormalHom L (σ * σ) = 1
    rw [map_mul, ← sq, ← hL, ← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  have hK1 : (σ * σ).restrictNormal K' = 1 := by
    show AlgEquiv.restrictNormalHom K' (σ * σ) = 1
    rw [map_mul, ← sq, ← hK', ← IsGalois.card_aut_eq_finrank K K']
    exact pow_card_eq_one'
  have hLfix : ∀ y : L, (σ * σ) (algebraMap L M y) = algebraMap L M y := fun y => by
    rw [← AlgEquiv.restrictNormal_commutes (σ * σ) L y, hL1, AlgEquiv.one_apply]
  have hKfix : ∀ k : K', (σ * σ) (algebraMap K' M k) = algebraMap K' M k := fun k => by
    rw [← AlgEquiv.restrictNormal_commutes (σ * σ) K' k, hK1, AlgEquiv.one_apply]
  have htop := eq_top_of_forall_mem hcomp
    (AlgHom.equalizer ((σ * σ : M ≃ₐ[K] M) : M →ₐ[K] M) (AlgHom.id K M))
    (fun k => by simpa [AlgHom.mem_equalizer] using hKfix k)
    (fun y => by simpa [AlgHom.mem_equalizer] using hLfix y)
  ext x
  have hx : x ∈ AlgHom.equalizer ((σ * σ : M ≃ₐ[K] M) : M →ₐ[K] M) (AlgHom.id K M) := by
    rw [htop]; trivial
  simpa [AlgHom.mem_equalizer] using hx

end UQAux

attribute [local instance] Ideal.Quotient.field in

theorem solution
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hL : Module.finrank K L = 2) (hK' : Module.finrank K K' = 2)
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (h𝔳 : Ideal.inertiaDeg' v.asIdeal 𝔳.1.asIdeal = 2)
    (𝔴 : 𝔳.1.Extension (𝓞 M)) :
    Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal = 1 := by
  classical

  haveI : FiniteDimensional K K' := Module.finite_of_finrank_eq_succ hK'
  haveI : Algebra.IsQuadraticExtension K K' := ⟨hK'⟩
  haveI : IsGalois K K' := Algebra.IsQuadraticExtension.isGalois K K'
  haveI : FiniteDimensional K' M := Module.finite_of_finrank_eq_succ (hdisj.trans hL)
  haveI : FiniteDimensional K M := Module.Finite.trans K' M
  haveI : Normal K M := UQAux.normal_of_compositum K L K' M hcomp
  haveI : IsGalois K M := IsGalois.mk

  haveI : (𝔴.1.asIdeal).IsMaximal := 𝔴.1.isMaximal
  haveI : (𝔳.1.asIdeal).IsMaximal := 𝔳.1.isMaximal
  haveI : (v.asIdeal).IsMaximal := v.isMaximal
  haveI hPq : (𝔴.1.asIdeal).LiesOver 𝔳.1.asIdeal := ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal 𝔴.2
    simp only [HeightOneSpectrum.under_asIdeal] at h
    exact h.symm⟩
  haveI hqp : (𝔳.1.asIdeal).LiesOver v.asIdeal := ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal 𝔳.2
    simp only [HeightOneSpectrum.under_asIdeal] at h
    exact h.symm⟩
  haveI hPp : (𝔴.1.asIdeal).LiesOver v.asIdeal := Ideal.LiesOver.trans 𝔴.1.asIdeal 𝔳.1.asIdeal v.asIdeal

  have hexp : ∀ τ : ((𝓞 M ⧸ 𝔴.1.asIdeal) ≃ₐ[𝓞 K ⧸ v.asIdeal] (𝓞 M ⧸ 𝔴.1.asIdeal)), τ ^ 2 = 1 := by
    intro τ
    obtain ⟨σ, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective (M ≃ₐ[K] M) v.asIdeal 𝔴.1.asIdeal τ
    have hσ : σ ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
      exact UQAux.mul_self_eq_one K L K' M hL hK' hcomp σ.1)
    rw [← map_pow, hσ, map_one]
  have hdvd : Ideal.inertiaDeg' v.asIdeal 𝔴.1.asIdeal ∣ 2 := by
    rw [Ideal.inertiaDeg_algebraMap,
      ← IsGalois.card_aut_eq_finrank (𝓞 K ⧸ v.asIdeal) (𝓞 M ⧸ 𝔴.1.asIdeal), ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp

  rw [Ideal.inertiaDeg_algebra_tower v.asIdeal 𝔳.1.asIdeal 𝔴.1.asIdeal, h𝔳] at hdvd
  have hpos : 0 < Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal := Ideal.inertiaDeg'_pos 𝔳.1.asIdeal 𝔴.1.asIdeal
  have hle : 2 * Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal ≤ 2 := Nat.le_of_dvd two_pos hdvd
  omega

end S_IsDedekindDomain_HeightOneSpectrum_inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange (solution)
