-- Prove2me | solution 1 for GlobalTheory.LocalizationIntegrallyClosedDomain.isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:01.870851+00:00
-- url     : https://prove2.me/submissions/7caead8f-932a-4bbb-8569-864209628d6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
import Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_algebraMap_eq_zero_of_sub
import Theorems.Thm_GlobalTheory_LocalizationIntegrallyClosedDomain_algebraMap_eq_zero_of_witness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.LocalizationIntegrallyClosedDomain
variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]
set_option maxHeartbeats 1600000
namespace GlobalTheory.LocalizationIntegrallyClosedDomain
theorem _root_.solution
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q))
    [IsDomain (Localization.AtPrime Q)] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro z hz
  have hf : ∀ x ∈ Q.primeCompl, algebraMap B (FractionRing (Localization.AtPrime Q)) x ≠ 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))]
    exact ((IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hx⟩ : Q.primeCompl)).map (algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).ne_zero
  have key : ∀ (b : B) (v : Q.primeCompl),
      algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) b v) * algebraMap B (FractionRing (Localization.AtPrime Q)) v = algebraMap B (FractionRing (Localization.AtPrime Q)) b := by
    intro b v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) v, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) b, ← map_mul,
      IsLocalization.mk'_spec]

  obtain ⟨D, A0, hD, hDz⟩ : ∃ D A0 : B, algebraMap B (FractionRing (Localization.AtPrime Q)) D ≠ 0 ∧
      algebraMap B (FractionRing (Localization.AtPrime Q)) D * z = algebraMap B (FractionRing (Localization.AtPrime Q)) A0 := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := (Localization.AtPrime Q)) z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    have hyK : algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) c t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hcK : algebraMap B (FractionRing (Localization.AtPrime Q)) c ≠ 0 := by
      intro h0
      apply hyK
      have h1 := key c t
      rw [h0] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hf _ t.2)
    refine ⟨c * s, a * t, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hcK (hf _ s.2)
    · have k1 := key a s
      have k2 := key c t
      rw [map_mul, map_mul, ← k1, ← k2]
      field_simp
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
  obtain ⟨p, hpm, hp⟩ := hm
  set A : B := (m : B) * A0 with hA
  have hDA : algebraMap B (FractionRing (Localization.AtPrime Q)) D * (m • z) = algebraMap B (FractionRing (Localization.AtPrime Q)) A := by
    rw [Submonoid.smul_def, Algebra.smul_def, hA, map_mul, ← hDz]; ring
  have hE : algebraMap B (Localization.AtPrime Q) (p.scaleRoots D |>.eval A) = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap B (FractionRing (Localization.AtPrime Q))) (m • z) D
    rw [hp, mul_zero, hDA, Polynomial.eval₂_at_apply, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))] at h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).mp h1
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).mp hE
  obtain ⟨C, hC, hCq⟩ := H (insert A (insert D (insert (u : B) p.coeffs)))
  have hAC : A ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hDC : D ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have huC : (u : B) ∈ C := hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have hcoef : (↑p.coeffs : Set B) ⊆ (C : Set B) := fun x hx => hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
  set p' := p.toSubring C hcoef with hp'
  have hp'm : p'.Monic := (Polynomial.monic_toSubring p C hcoef).mpr hpm
  set A' : C := ⟨A, hAC⟩
  set D' : C := ⟨D, hDC⟩
  set u' : C := ⟨u, huC⟩
  haveI : Nontrivial B := (algebraMap B (Localization.AtPrime Q)).domain_nontrivial
  have hlc : C.subtype p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hsub : C.subtype ((p'.scaleRoots D').eval A') = (p.scaleRoots D).eval A := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ hlc,
      Polynomial.map_toSubring]
    rfl
  have hE' : u' * (p'.scaleRoots D').eval A' = 0 := by
    apply Subtype.ext
    have : (u : B) * C.subtype ((p'.scaleRoots D').eval A') = 0 := by rw [hsub]; exact hu
    simpa using this
  haveI := (hCq (Q.comap C.subtype)).1
  haveI := (hCq (Q.comap C.subtype)).2
  have hgE : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) ((p'.scaleRoots D').eval A') = 0 :=
    algebraMap_eq_zero_of_witness Q C u' _ u.2 hE'
  have hgD : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' ≠ 0 := by
    intro h0
    have h1 : algebraMap B (Localization.AtPrime Q) D = 0 := algebraMap_eq_zero_of_sub Q C D' h0
    apply hD
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)), h1, map_zero]
  have hhD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))))).mpr hgD
  set x : (FractionRing (Localization.AtPrime (Q.comap C.subtype))) := algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') / algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') with hx
  have hxD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') * x = algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') := by
    rw [hx]; field_simp
  have hlc2 : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hxint : IsIntegral (Localization.AtPrime (Q.comap C.subtype)) x := by
    refine ⟨p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype))), hp'm.map _, ?_⟩
    have h2 := Polynomial.scaleRoots_eval₂_mul (p := p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype)))) (algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))) x
      (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D')
    rw [hxD, ← Polynomial.map_scaleRoots _ _ _ hlc2, Polynomial.eval₂_at_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hgE, map_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hhD)
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Localization.AtPrime (Q.comap C.subtype)) (K := FractionRing (Localization.AtPrime (Q.comap C.subtype)))).mp hxint
  have hwD : w * algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A' := by
    apply IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))
    rw [map_mul, hw, mul_comm, hxD]
  obtain ⟨⟨e, v⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap C.subtype).primeCompl w
  have hev : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (e * D') = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (A' * v) := by
    rw [map_mul, map_mul, ← hwD, ← IsLocalization.mk'_spec (Localization.AtPrime (Q.comap C.subtype)) e v]; ring
  obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists (Q.comap C.subtype).primeCompl (Localization.AtPrime (Q.comap C.subtype))).mp hev
  have hnB : ((n : C) : B) * ((e : B) * D) = ((n : C) : B) * (A * ((v : C) : B)) := by
    simpa using congrArg Subtype.val hn
  have hK := congrArg (algebraMap B (FractionRing (Localization.AtPrime Q))) hnB
  simp only [map_mul, hA] at hK
  have hfn : algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) ≠ 0 := hf _ (by exact n.2)
  have hfv : algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B) ≠ 0 := hf _ (by exact v.2)
  have hfm : algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) ≠ 0 := hf _ m.2
  let v'' : Q.primeCompl := ⟨((v : C) : B), by exact v.2⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) (e : B) (m * v''), ?_⟩
  have key2 := key (e : B) (m * v'')
  simp only [Submonoid.coe_mul, map_mul] at key2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfn hD) (mul_ne_zero hfm hfv))
  linear_combination (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) D) * key2
    - (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B)) * hDz + hK
end GlobalTheory.LocalizationIntegrallyClosedDomain
