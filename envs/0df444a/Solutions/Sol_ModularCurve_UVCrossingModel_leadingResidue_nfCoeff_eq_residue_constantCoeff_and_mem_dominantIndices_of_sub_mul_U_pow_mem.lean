-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7515e15c-f4f7-5428-aafc-1565f2b184d9

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem
set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel

namespace X5S

variable {W : Type u} [CommRing W]

theorem snd_eq_single_of_mem_antidiagonal_single_zero {j : ℕ} {p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single (0 : Fin 2) j)) :
    p.2 = Finsupp.single (0 : Fin 2) (p.2 0) := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : p.1 1 + p.2 1 = 0 := by
    have := DFunLike.congr_fun hp 1
    simpa [Finsupp.add_apply, Finsupp.single_apply] using this
  ext i
  fin_cases i
  · simp
  · simp only [Fin.mk_one, Finsupp.single_apply, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, if_false]
    omega

theorem dvd_coeff_single_zero_of_mem (ϖ : W) (e : ℕ) (he : 1 ≤ e)
    (F : MvPowerSeries (Fin 2) W)
    (hF : F ∈ Ideal.span ({MvPowerSeries.C ϖ, MvPowerSeries.X 1,
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)} :
          Set (MvPowerSeries (Fin 2) W))) :
    ∀ j : ℕ, ϖ ∣ MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j) F := by
  refine Submodule.span_induction
    (p := fun F _ => ∀ j : ℕ, ϖ ∣ MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j) F) ?_ ?_ ?_ ?_ hF
  · intro G hG j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl
    · rw [MvPowerSeries.coeff_C]
      split_ifs <;> simp
    · have hX : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) = 0 := by
        rw [MvPowerSeries.coeff_X, if_neg]
        intro h
        have := DFunLike.congr_fun h 1
        simp at this
      rw [hX]; exact dvd_zero ϖ
    · have hX : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) j)
          ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1) = 0 := by
        rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial,
          if_neg]
        intro h
        have := DFunLike.congr_fun h 1
        simp at this
      rw [map_sub, hX, zero_sub, MvPowerSeries.coeff_C]
      split_ifs with h
      · exact (dvd_neg).mpr (dvd_pow_self ϖ (by omega))
      · simp
  · intro j; simp
  · intro G H _ _ hG hH j
    rw [map_add]
    exact dvd_add (hG j) (hH j)
  · intro S G _ hG j
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.dvd_sum fun p hp => ?_
    rw [snd_eq_single_of_mem_antidiagonal_single_zero hp]
    exact dvd_mul_of_dvd_right (hG _) _

theorem nfExponent_nat (m : ℕ) : nfExponent (m : ℤ) = Finsupp.single (0 : Fin 2) m := rfl

theorem nfCoeff_nat {W : Type u} [CommRing W] (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m) (inU ab.1 + inV ab.2) = nfCoeff ab (m : ℤ) := by
  rw [map_add, coeff_inU, coeff_inV]
  simp only [Finsupp.single_apply]
  show _ = nfCoeff ab (Int.ofNat m)
  simp only [nfCoeff]
  rcases m with _ | m
  · simp [hb]
  · simp

end X5S

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)})
    (G : MvPowerSeries (Fin 2) W) (hG : mk (ϖ ^ e) G = γ) :
    leadingResidue ϖ (nfCoeff ab (m : ℤ)) = IsLocalRing.residue W (MvPowerSeries.constantCoeff G) ∧
      (m : ℤ) ∈ dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab := by
  classical

  have hmem : inU ab.1 + inV ab.2 - G * MvPowerSeries.X 0 ^ m ∈
      Ideal.span ({MvPowerSeries.C ϖ, MvPowerSeries.X 1,
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)} :
          Set (MvPowerSeries (Fin 2) W)) := by
    have h1 : mk (ϖ ^ e) (inU ab.1 + inV ab.2 - G * MvPowerSeries.X 0 ^ m)
        ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)} := by
      rw [map_sub, map_mul, map_pow, habx, hG]
      exact hxγ
    have h2 : Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}
        = Ideal.map (mk (ϖ ^ e)) (Ideal.span {MvPowerSeries.C ϖ, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W)}) := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [h2, Ideal.mem_map_iff_of_surjective _ (mk_surjective _)] at h1
    obtain ⟨Pp, hP, hPeq⟩ := h1
    have h3 : Pp - (inU ab.1 + inV ab.2 - G * MvPowerSeries.X 0 ^ m) ∈ uvCrossingIdeal W (ϖ ^ e) :=
      (Ideal.Quotient.eq).mp hPeq
    have h4 : inU ab.1 + inV ab.2 - G * MvPowerSeries.X 0 ^ m
        = Pp - (Pp - (inU ab.1 + inV ab.2 - G * MvPowerSeries.X 0 ^ m)) := by ring
    rw [h4]
    refine Ideal.sub_mem _ (Ideal.span_mono ?_ hP) (Ideal.span_mono ?_ h3)
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto
    · intro y hy
      simp only [Set.mem_singleton_iff] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr hy)

  have hdvd := X5S.dvd_coeff_single_zero_of_mem ϖ e he _ hmem m
  have hcoeffGX : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m) (G * MvPowerSeries.X 0 ^ m)
      = MvPowerSeries.constantCoeff G := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial, if_pos le_rfl, tsub_self, mul_one,
      MvPowerSeries.coeff_zero_eq_constantCoeff]
  rw [map_sub, X5S.nfCoeff_nat ab hb m, hcoeffGX] at hdvd
  have hβ : nfCoeff ab (m : ℤ) - MvPowerSeries.constantCoeff G ∈ IsLocalRing.maximalIdeal W := by
    rw [Irreducible.maximalIdeal_eq hϖ, Ideal.mem_span_singleton]
    exact hdvd
  have hres : IsLocalRing.residue W (nfCoeff ab (m : ℤ)) = IsLocalRing.residue W (MvPowerSeries.constantCoeff G) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hβ

  have hG0 : IsLocalRing.residue W (MvPowerSeries.constantCoeff G) ≠ 0 := by
    let φ : UVCrossingModel W (ϖ ^ e) →+* IsLocalRing.ResidueField W :=
      Ideal.Quotient.lift (uvCrossingIdeal W (ϖ ^ e))
        ((IsLocalRing.residue W).comp (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W →+* W)) (by
          intro a ha
          rw [Ideal.mem_span_singleton] at ha
          obtain ⟨c, rfl⟩ := ha
          rw [RingHom.comp_apply, map_mul, map_mul, map_sub, map_mul, MvPowerSeries.constantCoeff_X,
            MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul, zero_sub, map_neg,
            (IsLocalRing.residue_eq_zero_iff _).mpr, neg_zero, zero_mul]
          rw [Irreducible.maximalIdeal_eq hϖ, Ideal.mem_span_singleton]
          exact dvd_pow_self ϖ (by omega))
    have hφ : φ γ = IsLocalRing.residue W (MvPowerSeries.constantCoeff G) := by
      rw [← hG]
      rfl
    rw [← hφ]
    exact (hγ.map φ).ne_zero
  have hunitβ : IsUnit (nfCoeff ab (m : ℤ)) := by
    by_contra h
    have hm : nfCoeff ab (m : ℤ) ∈ IsLocalRing.maximalIdeal W :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    exact hG0 (hres ▸ hm)

  have hlr : leadingResidue ϖ (nfCoeff ab (m : ℤ)) = IsLocalRing.residue W (nfCoeff ab (m : ℤ)) := by
    have hne : nfCoeff ab (m : ℤ) ≠ 0 := hunitβ.ne_zero
    rw [leadingResidue, if_neg hne]
    have hm0 : multiplicity ϖ (nfCoeff ab (m : ℤ)) = 0 :=
      multiplicity_eq_zero.mpr (fun h => hϖ.not_isUnit (isUnit_of_dvd_unit h hunitβ))
    have h := pow_multiplicity_mul_unitPart ϖ (nfCoeff ab (m : ℤ))
    rw [hm0, pow_zero, one_mul] at h
    rw [h]
  refine ⟨hlr.trans hres, ?_⟩

  have hval : (q : ℕ∞) * IsDiscreteValuationRing.addVal W (nfCoeff ab (m : ℤ)) = 0 := by
    have h0 : IsDiscreteValuationRing.addVal W (nfCoeff ab (m : ℤ)) = 0 := by
      refine le_antisymm ?_ (by simp)
      rw [← (IsDiscreteValuationRing.addVal W).map_one]
      exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (isUnit_iff_dvd_one.mp hunitβ)
    rw [h0, mul_zero]
  have hwt : annulusWeight (q * e) 0 (nfExponent (m : ℤ)) = 0 := by
    rw [X5S.nfExponent_nat]
    simp [annulusWeight]
  show termOrder _ (q * e) 0 ab (m : ℤ) = repGaussOrder _ (q * e) 0 (inU ab.1 + inV ab.2)
  have hterm : termOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab (m : ℤ) = 0 := by
    simp only [termOrder, hwt, Nat.cast_zero, add_zero]
    exact hval
  rw [hterm]
  refine le_antisymm (by simp) ?_
  have h := repGaussOrder_le (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0
    (inU ab.1 + inV ab.2) (nfExponent (m : ℤ))
  rw [hwt, X5S.nfExponent_nat, X5S.nfCoeff_nat ab hb m] at h
  simp only [Nat.cast_zero, add_zero] at h
  rw [hval] at h
  exact h

end S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem (solution)
