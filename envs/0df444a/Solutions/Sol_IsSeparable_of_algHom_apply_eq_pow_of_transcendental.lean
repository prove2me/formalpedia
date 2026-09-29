-- Prove2me | solution 1 for IsSeparable.of_algHom_apply_eq_pow_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/55a9c35a-b50b-5c58-97ce-8f09f47189b4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsSeparable_of_algHom_apply_eq_pow_of_transcendental

set_option autoImplicit false

open Polynomial

namespace HDescent

section Part1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem apply_coeff_minpoly_eq {L : IntermediateField K F} (σ₁ σ₂ : F →+* F)
    (hL : ∀ x ∈ L, ∃ y ∈ L, σ₁ x = σ₂ y)
    (g : F) (hgint : IsIntegral L g) (hg : σ₁ g = σ₂ g) (i : ℕ) :
    σ₁ ((minpoly L g).coeff i : F) = σ₂ ((minpoly L g).coeff i : F) := by
  set m := minpoly L g with hm
  have hmonic : m.Monic := minpoly.monic hgint
  set ι : L →+* F := algebraMap L F with hι
  set M₁ : F[X] := m.map (σ₁.comp ι) with hM₁
  set M₂ : F[X] := m.map (σ₂.comp ι) with hM₂
  have hM₁m : M₁.Monic := hmonic.map _
  have hM₂m : M₂.Monic := hmonic.map _
  have hdeg₁ : M₁.degree = m.degree := hmonic.degree_map _
  have hdeg₂ : M₂.degree = m.degree := hmonic.degree_map _

  have heval : ∀ σ : F →+* F, (m.map (σ.comp ι)).eval (σ g) = 0 := by
    intro σ
    rw [eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hDγ : (M₁ - M₂).eval (σ₂ g) = 0 := by
    rw [eval_sub, hM₂, heval σ₂, hM₁, ← hg, heval σ₁, sub_zero]

  by_contra hne
  have hD0 : M₁ - M₂ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg (fun P : F[X] => P.coeff i) (sub_eq_zero.mp h)
    simp only [hM₁, hM₂, coeff_map, RingHom.coe_comp, Function.comp_apply] at h'
    exact h'
  have hDdeg : (M₁ - M₂).degree < m.degree := by
    have h := degree_sub_lt (hdeg₁.trans hdeg₂.symm) hM₁m.ne_zero
      (by rw [hM₁m.leadingCoeff, hM₂m.leadingCoeff])
    rwa [hdeg₁] at h

  have hcoef : ∀ j, ∃ y ∈ L, σ₂ y = (M₁ - M₂).coeff j := by
    intro j
    rw [coeff_sub, hM₁, hM₂, coeff_map, coeff_map]
    obtain ⟨y, hy, hyeq⟩ := hL _ (m.coeff j).2
    refine ⟨y - m.coeff j, sub_mem hy (m.coeff j).2, ?_⟩
    rw [map_sub, ← hyeq]
    rfl
  have hlift : (M₁ - M₂) ∈ Polynomial.lifts (σ₂.comp ι) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    obtain ⟨y, hy, hyeq⟩ := hcoef j
    exact ⟨⟨y, hy⟩, hyeq⟩
  obtain ⟨P, hPmap, hPdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts hlift
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hPmap
    exact hD0 hPmap.symm
  have hPg : aeval g P = 0 := by
    apply σ₂.injective
    rw [map_zero, aeval_def, hom_eval₂, ← eval_map, hPmap, hDγ]
  have hle := minpoly.degree_le_of_ne_zero L g hP0 hPg
  rw [hPdeg] at hle
  exact absurd (hle.trans_lt hDdeg) (lt_irrefl _)

theorem exists_mem_adjoin_apply_eq_iterateFrobenius {p : ℕ} [Fact p.Prime] [CharP F p] (r : ℕ)
    (φ : F →ₐ[K] F) (t : F) (hφt : φ t = t ^ p ^ r) (hK : ∀ a : K, ∃ b : K, b ^ p ^ r = a) :
    ∀ x ∈ IntermediateField.adjoin K ({t} : Set F), ∃ y ∈ IntermediateField.adjoin K ({t} : Set F),
      (φ : F →+* F) x = iterateFrobenius F p r y := by
  intro x hx
  have key : (IntermediateField.adjoin K ({t} : Set F)).toSubfield ≤
      (((IntermediateField.adjoin K ({t} : Set F)).toSubfield.map (iterateFrobenius F p r)).comap
        (φ : F →+* F)) := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · obtain ⟨b, hb⟩ := hK a
      refine Subfield.mem_comap.mpr (Subfield.mem_map.mpr ⟨algebraMap K F b, ?_, ?_⟩)
      · exact Subfield.subset_closure (Or.inl ⟨b, rfl⟩)
      · rw [iterateFrobenius_def, ← map_pow, hb]
        simp
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      refine Subfield.mem_comap.mpr (Subfield.mem_map.mpr ⟨z, Subfield.subset_closure (Or.inr rfl), ?_⟩)
      rw [iterateFrobenius_def]
      simpa using hφt.symm
  obtain ⟨y, hy, hyeq⟩ := Subfield.mem_map.mp (Subfield.mem_comap.mp (key hx))
  exact ⟨y, hy, hyeq.symm⟩

end Part1

section Part2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ringHom_aeval (σ : F →+* F) (τ : K →+* K)
    (hστ : ∀ a : K, σ (algebraMap K F a) = algebraMap K F (τ a)) (x : F) (a : K[X]) :
    σ (aeval x a) = aeval (σ x) (a.map τ) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
  congr 1
  exact RingHom.ext hστ

theorem aeval_mem_closure (t : F) (a : K[X]) (S : Subfield F) (ht : t ∈ S)
    (ha : ∀ i, algebraMap K F (a.coeff i) ∈ S) : aeval t a ∈ S := by
  rw [aeval_eq_sum_range]
  refine Subfield.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subfield.mul_mem _ (ha i) (Subfield.pow_mem _ ht i)

theorem mem_closure_of_apply_eq_pow {p : ℕ} [Fact p.Prime] [CharP F p] (r : ℕ)
    (φ : F →ₐ[K] F) (t : F) (ht : Transcendental K t) (hφt : φ t = t ^ p ^ r)
    {c : F} (hc : c ∈ IntermediateField.adjoin K ({t} : Set F)) (hφc : φ c = c ^ p ^ r) :
    c ∈ Subfield.closure ({x : F | x ^ p ^ r = x} ∪ {t}) := by
  haveI : CharP K p := (Algebra.charP_iff K F p).mpr inferInstance
  set S := Subfield.closure ({x : F | x ^ p ^ r = x} ∪ {t}) with hS
  have htS : t ∈ S := Subfield.subset_closure (Or.inr rfl)

  set σ : F →+* F := iterateFrobenius F p r with hσdef
  set τ : K →+* K := iterateFrobenius K p r with hτdef
  have hσ : ∀ x : F, σ x = x ^ p ^ r := fun x => iterateFrobenius_def ..
  have hτ : ∀ a : K, τ a = a ^ p ^ r := fun a => iterateFrobenius_def ..
  have hστ : ∀ a : K, σ (algebraMap K F a) = algebraMap K F (τ a) := by
    intro a
    rw [hσ, hτ, map_pow]

  obtain ⟨a₀, b₀, hab₀⟩ := (IntermediateField.mem_adjoin_simple_iff K c).mp hc
  have hinj : Function.Injective (aeval (R := K) t) := transcendental_iff_injective.mp ht
  by_cases hb₀ : b₀ = 0
  · rw [hab₀, hb₀, map_zero, div_zero]
    exact S.zero_mem

  set f : RatFunc K := algebraMap K[X] (RatFunc K) a₀ / algebraMap K[X] (RatFunc K) b₀ with hf
  set a : K[X] := f.num with ha
  set b : K[X] := f.denom with hb
  have hrel : a * b₀ = a₀ * b := (RatFunc.num_mul_eq_mul_denom_iff hb₀).mpr hf
  have hcop : IsCoprime a b := RatFunc.isCoprime_num_denom f
  have hbm : b.Monic := RatFunc.monic_denom f
  have hbt : aeval t b ≠ 0 := fun h => hbm.ne_zero (hinj (by rw [h, map_zero]))
  have hb₀t : aeval t b₀ ≠ 0 := fun h => hb₀ (hinj (by rw [h, map_zero]))
  have hcab : c = aeval t a / aeval t b := by
    rw [hab₀, div_eq_div_iff hb₀t hbt, ← map_mul, ← map_mul, ← hrel, mul_comm]

  have hQ : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  set s : F := t ^ p ^ r with hs
  have hinjs : Function.Injective (aeval (R := K) s) := transcendental_iff_injective.mp (ht.pow hQ)

  set a' : K[X] := a.map τ with ha'
  set b' : K[X] := b.map τ with hb'
  have hb'm : b'.Monic := hbm.map τ
  have hbs : aeval s b ≠ 0 := fun h => hbm.ne_zero (hinjs (by rw [h, map_zero]))
  have hb's : aeval s b' ≠ 0 := fun h => hb'm.ne_zero (hinjs (by rw [h, map_zero]))

  have hφc' : φ c = aeval s a / aeval s b := by
    rw [hcab, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hφt]
  have hσc : c ^ p ^ r = aeval s a' / aeval s b' := by
    rw [← hσ, hcab, map_div₀, ringHom_aeval σ τ hστ, ringHom_aeval σ τ hστ, hσ t]

  have hpoly : a * b' = a' * b := by
    apply hinjs
    rw [map_mul, map_mul, ← div_eq_div_iff hbs hb's, ← hφc', ← hσc, hφc]

  have hcop' : IsCoprime a' b' := by
    have h := hcop.map (mapRingHom τ)
    simpa only [coe_mapRingHom] using h
  have hbb' : b = b' := by
    refine eq_of_monic_of_associated hbm hb'm (associated_of_dvd_dvd ?_ ?_)
    · exact hcop.symm.dvd_of_dvd_mul_left ⟨a', by rw [hpoly]; exact mul_comm a' b⟩
    · exact hcop'.symm.dvd_of_dvd_mul_left ⟨a, by rw [← hpoly]; exact mul_comm a b'⟩
  have haa' : a = a' := by
    rw [← hbb'] at hpoly
    exact mul_right_cancel₀ hbm.ne_zero hpoly

  have hcoefmem : ∀ d : K[X], d.map τ = d → ∀ i, algebraMap K F (d.coeff i) ∈ S := by
    intro d hd i
    have hi : τ (d.coeff i) = d.coeff i := by
      have := congrArg (fun P : K[X] => P.coeff i) hd
      simpa only [coeff_map] using this
    refine Subfield.subset_closure (Or.inl ?_)
    show (algebraMap K F (d.coeff i)) ^ p ^ r = algebraMap K F (d.coeff i)
    rw [← map_pow, ← hτ, hi]
  rw [hcab]
  exact div_mem (aeval_mem_closure t a S htS (hcoefmem a haa'.symm))
    (aeval_mem_closure t b S htS (hcoefmem b hbb'.symm))

end Part2

end HDescent

open HDescent in

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 0 < r)
    (φ : F →ₐ[K] F) (t : F) (ht : Transcendental K t) (hφt : φ t = t ^ p ^ r)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (g : F) (hg : φ g = g ^ p ^ r) :
    IsSeparable (Subfield.closure ({c : F | c ^ p ^ r = c} ∪ {t})) g := by
  set L := IntermediateField.adjoin K ({t} : Set F) with hL
  set S := Subfield.closure ({c : F | c ^ p ^ r = c} ∪ {t}) with hS
  have hgsep : IsSeparable L g := Algebra.IsSeparable.isSeparable L g
  have hgint : IsIntegral L g := hgsep.isIntegral
  have hmsep : (minpoly L g).Separable := hgsep
  have hK : ∀ a : K, ∃ b : K, b ^ p ^ r = a := fun a =>
    IsAlgClosed.exists_pow_nat_eq a (pow_pos (Fact.out : p.Prime).pos r)

  have hcoefφ : ∀ i, φ ((minpoly L g).coeff i : F) = ((minpoly L g).coeff i : F) ^ p ^ r := by
    intro i
    have h := apply_coeff_minpoly_eq (L := L) (φ : F →+* F) (iterateFrobenius F p r)
      (exists_mem_adjoin_apply_eq_iterateFrobenius r φ t hφt hK) g hgint
      (by rw [iterateFrobenius_def]; exact hg) i
    rw [iterateFrobenius_def] at h
    exact h

  have hcoefS : ∀ i, ((minpoly L g).coeff i : F) ∈ S := fun i =>
    mem_closure_of_apply_eq_pow r φ t ht hφt ((minpoly L g).coeff i).2 (hcoefφ i)

  have hlift : (minpoly L g).map (algebraMap L F) ∈ Polynomial.lifts (algebraMap S F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_map]
    exact ⟨⟨_, hcoefS i⟩, rfl⟩
  obtain ⟨mS, hmS, -, -⟩ := lifts_and_degree_eq_and_monic hlift ((minpoly.monic hgint).map _)
  have hmSsep : mS.Separable := by
    rw [← separable_map (algebraMap S F), hmS, separable_map]
    exact hmsep
  have hmSg : aeval g mS = 0 := by
    rw [aeval_def, ← eval_map, hmS, eval_map, ← aeval_def]
    exact minpoly.aeval L g
  exact hmSsep.of_dvd (minpoly.dvd S g hmSg)

end S_IsSeparable_of_algHom_apply_eq_pow_of_transcendental
end P2MW
export P2MW.S_IsSeparable_of_algHom_apply_eq_pow_of_transcendental (solution)
