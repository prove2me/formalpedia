-- Prove2me | solution 1 for MasulloGRH.sIntegerFundamentalDomain_finite_translates
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:52:49.023043+00:00
-- url     : https://prove2.me/submissions/560bb781-4828-4cf8-ab64-fe2cfef52c96

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain
import Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_relCompact_and_interior_nonempty

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sIntegerFundamentalDomain_finite_translates

open MasulloGRH
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
/-- The norm on the completion at an infinite place restricts to the place on `F`. -/
theorem norm_algebraMap_completion (w : InfinitePlace F) (ξ : F) :
    ‖algebraMap F w.Completion ξ‖ = w ξ := by
  have h := InfinitePlace.Completion.norm_coe (v := w) ((WithAbs.equiv w.1).symm ξ)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- A compact subset of the completion `F_v` at a finite place is contained in `d⁻¹ 𝒪_v` for
some nonzero `d ∈ 𝒪_F`. -/
theorem exists_ne_zero_forall_valued_mul_le_one (v : HeightOneSpectrum (𝓞 F))
    (K : Set (v.adicCompletion F)) (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ K,
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * x) ≤ (1 : ℤᵐ⁰) := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hπv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < (1 : ℤᵐ⁰) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v π
    exact h.trans_lt ((v.valuation_lt_one_iff_mem π).2 hπ)
  have hπn : ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hπv
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hpos : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hπn
  refine ⟨π ^ n, pow_ne_zero n hπ0, fun x hx ↦ ?_⟩
  rw [← Valued.toNormedField.norm_le_one_iff, map_pow, norm_mul, norm_pow]
  calc ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ ^ n * ‖x‖
      ≤ (max C 1)⁻¹ * max C 1 :=
        mul_le_mul hn.le ((hC x hx).trans (le_max_left _ _)) (norm_nonneg _)
          (inv_pos.mpr hpos).le
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **Discreteness of the `S`-integers in the `S`-adeles**: a compact subset of `𝔸_{F,S}` contains
the diagonal image of only finitely many `S`-integers. -/
theorem finite_sIntegers_mem_of_isCompact (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Set (SAdeleRing F Sf)) (hK : IsCompact K) :
    {ξ : F | ξ ∈ SIntegers (F := F) Sf ∧ sDiagonal Sf ξ ∈ K}.Finite := by
  classical
  -- bounded denominators at the finite places of `S`
  have h1 : ∀ v : Sf, ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ K,
      Valued.v (algebraMap (𝓞 F) ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) d * x.2 v) ≤
        (1 : ℤᵐ⁰) := by
    intro v
    obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_valued_mul_le_one (v : HeightOneSpectrum (𝓞 F))
      ((fun x : SAdeleRing F Sf ↦ x.2 v) '' K)
      (hK.image ((continuous_apply v).comp continuous_snd))
    exact ⟨d, hd0, fun x hx ↦ hd _ ⟨x, hx, rfl⟩⟩
  choose dv hdv0 hdv using h1
  let d : 𝓞 F := ∏ v : Sf, dv v
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ hdv0 v
  have hdF : (algebraMap (𝓞 F) F d) ≠ 0 := by
    simpa using hd0
  -- bounded archimedean absolute values
  have h2 : ∀ w : InfinitePlace F, ∃ C : ℝ, ∀ x ∈ K, ‖x.1 w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ :=
      (hK.image ((continuous_apply w).comp continuous_fst)).isBounded.exists_norm_le
    exact ⟨C, fun x hx ↦ hC _ ⟨x, hx, rfl⟩⟩
  choose C hC using h2
  let B : ℝ := ∑ w : InfinitePlace F, w (algebraMap (𝓞 F) F d) * C w
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  have hinj : Set.InjOn (fun ξ : F ↦ algebraMap (𝓞 F) F d * ξ)
      ((fun ξ : F ↦ algebraMap (𝓞 F) F d * ξ) ⁻¹'
        {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ B}) :=
    (mul_right_injective₀ hdF).injOn
  refine (hfin.preimage hinj).subset ?_
  rintro ξ ⟨hξS, hξK⟩
  have hnonneg : ∀ w : InfinitePlace F, 0 ≤ w (algebraMap (𝓞 F) F d) * C w := by
    intro w
    have h := hC w _ hξK
    exact mul_nonneg (apply_nonneg _ _) ((norm_nonneg _).trans h)
  refine ⟨?_, fun φ ↦ ?_⟩
  · -- `d ξ` is integral at every finite place
    have hmem : algebraMap (𝓞 F) F d * ξ ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v ↦ ?_
      by_cases hv : v ∈ Sf
      · have h := hdv ⟨v, hv⟩ _ hξK
        have h' : v.valuation F (algebraMap (𝓞 F) F (dv ⟨v, hv⟩) * ξ) ≤ 1 := by
          rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
          have e : ((algebraMap (𝓞 F) F (dv ⟨v, hv⟩) * ξ : F) : v.adicCompletion F) =
              algebraMap (𝓞 F) (v.adicCompletion F) (dv ⟨v, hv⟩) *
                (sDiagonal Sf ξ).2 ⟨v, hv⟩ := by
            change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (dv ⟨v, hv⟩) * ξ) =
              algebraMap (𝓞 F) (v.adicCompletion F) (dv ⟨v, hv⟩) *
                algebraMap F (v.adicCompletion F) ξ
            rw [map_mul, ← IsScalarTower.algebraMap_apply]
          rw [e]
          exact h
        have hprod : d = dv ⟨v, hv⟩ * ∏ u ∈ Finset.univ.erase (⟨v, hv⟩ : Sf), dv u :=
          (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
        have e2 : algebraMap (𝓞 F) F d * ξ =
            algebraMap (𝓞 F) F (dv ⟨v, hv⟩) * ξ *
              algebraMap (𝓞 F) F (∏ u ∈ Finset.univ.erase (⟨v, hv⟩ : Sf), dv u) := by
          rw [hprod, map_mul]
          ring
        rw [e2, map_mul]
        exact mul_le_one' h' (v.valuation_le_one _)
      · rw [map_mul]
        exact mul_le_one' (v.valuation_le_one _) (hξS v hv)
    obtain ⟨z, hz⟩ := hmem
    change IsIntegral ℤ (algebraMap (𝓞 F) F d * ξ)
    rw [← hz]
    exact z.isIntegral_coe
  · -- the archimedean absolute values of `d ξ` are bounded
    have h := hC (InfinitePlace.mk φ) _ hξK
    have h' : (InfinitePlace.mk φ) ξ ≤ C (InfinitePlace.mk φ) := by
      rw [← norm_algebraMap_completion]
      exact h
    calc ‖φ (algebraMap (𝓞 F) F d * ξ)‖
        = (InfinitePlace.mk φ) (algebraMap (𝓞 F) F d) * (InfinitePlace.mk φ) ξ := by
          rw [← InfinitePlace.apply, map_mul]
      _ ≤ (InfinitePlace.mk φ) (algebraMap (𝓞 F) F d) * C (InfinitePlace.mk φ) :=
          mul_le_mul_of_nonneg_left h' (apply_nonneg _ _)
      _ ≤ B := Finset.single_le_sum (f := fun w : InfinitePlace F ↦
            w (algebraMap (𝓞 F) F d) * C w) (fun w _ ↦ hnonneg w) (Finset.mem_univ _)

end Sol_MasulloGRH_sIntegerFundamentalDomain_finite_translates

open MasulloGRH
open Sol_MasulloGRH_sIntegerFundamentalDomain_finite_translates

theorem solution
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Set (SAdeleRing F Sf)) (hK : IsCompact K) :
    {ξ : F | ξ ∈ SIntegers (F := F) Sf ∧
      ∃ y ∈ closure (sIntegerFundamentalDomain F b Sf), sDiagonal Sf ξ + y ∈ K}.Finite := by
  -- the closure of the fundamental domain is compact
  have hD : IsCompact (closure (sIntegerFundamentalDomain F b Sf)) :=
    (sIntegerFundamentalDomain_relCompact_and_interior_nonempty F b Sf).1
  -- hence so is the set of differences `K - closure D`
  have hKD : IsCompact ((fun p : SAdeleRing F Sf × SAdeleRing F Sf ↦ p.1 - p.2) ''
      (K ×ˢ closure (sIntegerFundamentalDomain F b Sf))) :=
    (hK.prod hD).image (continuous_fst.sub continuous_snd)
  refine (finite_sIntegers_mem_of_isCompact Sf _ hKD).subset ?_
  rintro ξ ⟨hξ, y, hy, hyK⟩
  exact ⟨hξ, (sDiagonal Sf ξ + y, y), ⟨hyK, hy⟩, add_sub_cancel_right _ _⟩
