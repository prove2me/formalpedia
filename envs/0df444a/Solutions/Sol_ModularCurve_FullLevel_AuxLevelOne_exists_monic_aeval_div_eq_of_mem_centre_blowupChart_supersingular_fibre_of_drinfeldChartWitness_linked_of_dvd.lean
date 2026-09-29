-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_monic_aeval_div_eq_of_mem_centre_blowupChart_supersingular_fibre_of_drinfeldChartWitness_linked_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f4dd9e94-5120-5874-9141-a9e5ffddebaa

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_monic_aeval_div_eq_of_mem_centre_blowupChart_supersingular_fibre_of_drinfeldChartWitness_linked_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace LocalFinAux

set_option linter.unusedVariables false in

theorem core
    (q : ℕ) [hq : Fact q.Prime]
    (W : Type) [CommRing W] [IsLocalRing W] [Nontrivial W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (S : Type) [CommRing S] (φW : W →+* S)
    (T X0 X1 u v h : S) (hu : IsUnit u)
    (hrel : T ^ (q + 1) * v = (X0 * X1 ^ q - X0 ^ q * X1 + h) * u)
    (hh : h ∈ (Ideal.span ({X0, X1} : Set S)) ^ ((q + 1) + 1))
    (P : S) (hP : P = φW π)
    (hconst : ∀ g : S, ∃ w : W, g - φW w ∈ Ideal.span ({P, X0, X1} : Set S))
    (L : Type) [CommRing L] [Algebra S L] (ι : S →+* L) (hιalg : algebraMap S L = ι) (s : S) (inv : L) (hsinv : ι s * inv = 1)
    (hs : s ∈ Ideal.span ({T, X0, X1} : Set S))
    (R : Subalgebra S L)
    (hRdef : ∀ z : L, z ∈ R ↔ z ∈ Algebra.adjoin S {z : L | ∃ i ∈ Ideal.span ({T, X0, X1} : Set S), z * ι s = ι i})
    (x : L) (hxR : x ∈ R) :
    let I : Ideal S := Ideal.span ({T, X0, X1} : Set S)
    let 𝔐 : Ideal S := Ideal.span ({P, X0, X1} : Set S)
    ∃ p : Polynomial W, p.Monic ∧
      ∃ (r : L) (_ : r ∈ R) (n : ℕ) (m : Fin n → S) (r' : Fin n → L),
        (∀ k, m k ∈ 𝔐) ∧ (∀ k, r' k ∈ R) ∧
        Polynomial.eval x (p.map (ι.comp φW)) = (ι T * inv) * r + ∑ k, ι (m k) * r' k := by
  classical
  intro I 𝔐
  have hX0I : X0 ∈ I := Ideal.subset_span (by simp)
  have hX1I : X1 ∈ I := Ideal.subset_span (by simp)
  have htI : T ∈ I := Ideal.subset_span (by simp)
  have hX0𝔐 : X0 ∈ 𝔐 := Ideal.subset_span (by simp)
  have hX1𝔐 : X1 ∈ 𝔐 := Ideal.subset_span (by simp)
  have hπ𝔐 : P ∈ 𝔐 := Ideal.subset_span (by simp)
  have hgenR : ∀ i ∈ I, ι i * inv ∈ R := by
    intro i hi
    refine (hRdef (ι i * inv)).mpr (Algebra.subset_adjoin ?_)
    exact ⟨i, hi, by rw [mul_assoc, mul_comm inv, hsinv, mul_one]⟩
  have hιR : ∀ g : S, ι g ∈ R := fun g => by rw [← hιalg]; exact R.algebraMap_mem g
  have hinvJR : ∀ g : S, g ∈ Ideal.span ({X0, X1} : Set S) → g ∈ I := by
    intro g hg
    have : Ideal.span ({X0, X1} : Set S) ≤ I := by
      refine Ideal.span_le.mpr ?_
      intro g' hg'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with rfl | rfl
      · exact hX0I
      · exact hX1I
    exact this hg
  have hJ𝔐 : ∀ g : S, g ∈ Ideal.span ({X0, X1} : Set S) → g ∈ 𝔐 := by
    intro g hg
    have : Ideal.span ({X0, X1} : Set S) ≤ 𝔐 := by
      refine Ideal.span_le.mpr ?_
      intro g' hg'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with rfl | rfl
      · exact hX0𝔐
      · exact hX1𝔐
    exact this hg

  set ξt : L := ι (T) * inv with hξtdef
  set ξ0 : L := ι (X0) * inv with hξ0def
  set ξ1 : L := ι (X1) * inv with hξ1def
  have hξtR : ξt ∈ R := hgenR _ htI
  have hξ0R : ξ0 ∈ R := hgenR _ hX0I
  have hξ1R : ξ1 ∈ R := hgenR _ hX1I

  let φ : W →+* L := ι.comp φW
  have hφ : ∀ w : W, φ w = ι (φW w) := fun w => rfl
  have hφR : ∀ w : W, φ w ∈ R := fun w => by rw [hφ]; exact hιR _
  let φR : W →+* ↥R.toSubring := φ.codRestrict R.toSubring hφR
  have hφR' : ∀ w : W, ((φR w : ↥R.toSubring) : L) = φ w := fun w => rfl
  let ιR : S → ↥R.toSubring := fun g => ⟨ι g, hιR g⟩
  let 𝔑 : Ideal ↥R.toSubring := Ideal.span {(⟨ξt, hξtR⟩ : ↥R.toSubring)} ⊔ Ideal.span (ιR '' (𝔐 : Set S))
  let mkQ : ↥R.toSubring →+* (↥R.toSubring ⧸ 𝔑) := Ideal.Quotient.mk 𝔑
  let ψ : W →+* (↥R.toSubring ⧸ 𝔑) := mkQ.comp φR
  have hψ : ∀ w : W, ψ w = mkQ ⟨φ w, hφR w⟩ := fun w => rfl

  have hQξt : mkQ ⟨ξt, hξtR⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
  have hQ𝔐 : ∀ g : S, g ∈ 𝔐 → mkQ ⟨ι g, hιR g⟩ = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩))
  have hψπ : ψ π = 0 := by
    rw [hψ]
    have : (⟨φ π, hφR π⟩ : ↥R.toSubring) = ⟨ι P, hιR P⟩ := Subtype.ext (by show φ π = ι P; rw [hφ, hP])
    rw [this]
    exact hQ𝔐 _ hπ𝔐
  have hψmax : ∀ w ∈ IsLocalRing.maximalIdeal W, ψ w = 0 := by
    intro w hw
    rw [hπ, Ideal.mem_span_singleton'] at hw
    obtain ⟨w', rfl⟩ := hw
    rw [map_mul, hψπ, mul_zero]

  have hconstQ : ∀ g : S, ∃ w : W, mkQ ⟨ι g, hιR g⟩ = ψ w := by
    intro g
    obtain ⟨w, hw⟩ := hconst g
    refine ⟨w, ?_⟩
    rw [hψ, eq_comm, ← sub_eq_zero, ← map_sub]
    have : (⟨φ w, hφR w⟩ : ↥R.toSubring) - ⟨ι g, hιR g⟩ = -⟨ι (g - φW w), hιR _⟩ := by
      apply Subtype.ext
      show φ w - ι g = -(ι (g - φW w))
      rw [hφ, map_sub]
      ring
    rw [this, map_neg, hQ𝔐 _ hw, neg_zero]

  obtain ⟨α, s', hs', hsdec⟩ := Ideal.mem_span_insert.mp hs
  obtain ⟨β, s'', hs'', hs'dec⟩ := Ideal.mem_span_insert.mp hs'
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hs''
  have hsexp : s = α * T + β * X0 + γ * X1 := by
    rw [hsdec, hs'dec, ← hγ]; ring
  have hιs : ι s = ι α * ι (T) + ι β * ι (X0) + ι γ * ι (X1) := by
    have h0 := congrArg (⇑ι) hsexp
    rw [map_add, map_add, map_mul, map_mul, map_mul] at h0
    exact h0
  have hone : (1 : L) = ι α * ξt + ι β * ξ0 + ι γ * ξ1 := by
    rw [← hsinv, hιs, hξtdef, hξ0def, hξ1def]
    ring

  have hpow : ∀ n : ℕ, ∀ g ∈ (Ideal.span ({X0, X1} : Set S)) ^ (n + 1),
      ∃ hr : ι g * inv ^ n ∈ R, mkQ ⟨_, hr⟩ = 0 := by
    intro n
    induction n with
    | zero =>
        intro g hg
        rw [zero_add, pow_one] at hg
        refine ⟨by rw [pow_zero, mul_one]; exact hιR _, ?_⟩
        have : (⟨ι g * inv ^ 0, by rw [pow_zero, mul_one]; exact hιR _⟩ : ↥R.toSubring) = ⟨ι g, hιR _⟩ :=
          Subtype.ext (by show ι g * inv ^ 0 = ι g; rw [pow_zero, mul_one])
        rw [this]
        exact hQ𝔐 _ (hJ𝔐 g hg)
    | succ n ih =>
        intro g hg
        rw [pow_succ] at hg
        refine Submodule.mul_induction_on hg ?_ ?_
        · intro a ha b hb
          obtain ⟨har, haQ⟩ := ih a ha
          have hbR : ι b * inv ∈ R := hgenR _ (hinvJR b hb)
          have hmem : ι (a * b) * inv ^ (n + 1) ∈ R := by
            have : ι (a * b) * inv ^ (n + 1) = (ι a * inv ^ n) * (ι b * inv) := by
              rw [map_mul, pow_succ]; ring
            rw [this]; exact R.mul_mem har hbR
          refine ⟨hmem, ?_⟩
          have : (⟨ι (a * b) * inv ^ (n + 1), hmem⟩ : ↥R.toSubring) = ⟨ι a * inv ^ n, har⟩ * ⟨ι b * inv, hbR⟩ :=
            Subtype.ext (by show ι (a * b) * inv ^ (n + 1) = (ι a * inv ^ n) * (ι b * inv); rw [map_mul, pow_succ]; ring)
          rw [this, map_mul, haQ, zero_mul]
        · intro a b ⟨har, haQ⟩ ⟨hbr, hbQ⟩
          have hmem : ι (a + b) * inv ^ (n + 1) ∈ R := by
            have : ι (a + b) * inv ^ (n + 1) = ι a * inv ^ (n + 1) + ι b * inv ^ (n + 1) := by
              rw [map_add]; ring
            rw [this]; exact R.add_mem har hbr
          refine ⟨hmem, ?_⟩
          have : (⟨ι (a + b) * inv ^ (n + 1), hmem⟩ : ↥R.toSubring) = ⟨_, har⟩ + ⟨_, hbr⟩ :=
            Subtype.ext (by show ι (a + b) * inv ^ (n + 1) = ι a * inv ^ (n + 1) + ι b * inv ^ (n + 1); rw [map_add]; ring)
          rw [this, map_add, haQ, hbQ, add_zero]

  set e0 : ↥R.toSubring ⧸ 𝔑 := mkQ ⟨ξ0, hξ0R⟩ with he0
  set e1 : ↥R.toSubring ⧸ 𝔑 := mkQ ⟨ξ1, hξ1R⟩ with he1
  have hrel2 : e0 * e1 ^ q = e0 ^ q * e1 := by
    obtain ⟨hhR, hhQ⟩ := hpow (q + 1) h hh
    obtain ⟨u', hu'⟩ := hu.exists_right_inv

    have hL : ξt ^ (q + 1) * ι v = (ξ0 * ξ1 ^ q - ξ0 ^ q * ξ1) * ι u + (ι h * inv ^ (q + 1)) * ι u := by
      have h0 := congrArg (⇑ι) hrel
      rw [map_mul, map_pow, map_mul, map_add, map_sub, map_mul, map_mul, map_pow, map_pow] at h0
      rw [hξtdef, hξ0def, hξ1def]
      linear_combination (inv ^ (q + 1)) * h0

    let T' : ↥R.toSubring := ⟨ξt, hξtR⟩
    let V' : ↥R.toSubring := ⟨ι v, hιR _⟩
    let U' : ↥R.toSubring := ⟨ι u, hιR _⟩
    let Ui' : ↥R.toSubring := ⟨ι u', hιR _⟩
    let H' : ↥R.toSubring := ⟨ι h * inv ^ (q + 1), hhR⟩
    let E0' : ↥R.toSubring := ⟨ξ0, hξ0R⟩
    let E1' : ↥R.toSubring := ⟨ξ1, hξ1R⟩
    have hLR : T' ^ (q + 1) * V' = (E0' * E1' ^ q - E0' ^ q * E1') * U' + H' * U' := by
      apply Subtype.ext
      show R.toSubring.subtype (T' ^ (q + 1) * V') = R.toSubring.subtype ((E0' * E1' ^ q - E0' ^ q * E1') * U' + H' * U')
      rw [map_mul, map_pow, map_add, map_mul, map_mul, map_sub, map_mul, map_mul, map_pow, map_pow]
      exact hL
    have hB : (E0' * E1' ^ q - E0' ^ q * E1') * U' = T' ^ (q + 1) * V' - H' * U' := by
      rw [hLR]; ring
    have hUU : U' * Ui' = 1 := by
      apply Subtype.ext
      show R.toSubring.subtype (U' * Ui') = R.toSubring.subtype 1
      rw [map_mul, map_one]
      show ι u * ι u' = 1
      rw [← map_mul, hu', map_one]
    have hq1 : q + 1 ≠ 0 := Nat.succ_ne_zero q
    have hA0 : mkQ (T' ^ (q + 1) * V') = 0 := by
      rw [map_mul, map_pow]
      show mkQ ⟨ξt, hξtR⟩ ^ (q + 1) * mkQ V' = 0
      rw [hQξt, zero_pow hq1, zero_mul]
    have hH0 : mkQ (H' * U') = 0 := by
      rw [map_mul]
      show mkQ ⟨ι h * inv ^ (q + 1), hhR⟩ * mkQ U' = 0
      rw [hhQ, zero_mul]
    have hB0 : mkQ ((E0' * E1' ^ q - E0' ^ q * E1') * U') = 0 := by
      rw [hB, map_sub, hA0, hH0, sub_zero]
    have hB1 : mkQ (E0' * E1' ^ q - E0' ^ q * E1') = 0 := by
      have h1 : mkQ ((E0' * E1' ^ q - E0' ^ q * E1') * U' * Ui') = 0 := by
        rw [map_mul, hB0, zero_mul]
      rwa [mul_assoc, hUU, mul_one] at h1
    rw [map_sub, map_mul, map_mul, map_pow, map_pow] at hB1
    rw [he0, he1]
    exact sub_eq_zero.mp hB1

  obtain ⟨b0, hb0⟩ := hconstQ β
  obtain ⟨g0, hg0⟩ := hconstQ γ
  have hrel1 : ψ b0 * e0 + ψ g0 * e1 = 1 := by
    have hR1 : (1 : ↥R.toSubring) = ⟨ι α, hιR _⟩ * ⟨ξt, hξtR⟩ + ⟨ι β, hιR _⟩ * ⟨ξ0, hξ0R⟩ + ⟨ι γ, hιR _⟩ * ⟨ξ1, hξ1R⟩ := by
      apply Subtype.ext
      show R.toSubring.subtype 1 = R.toSubring.subtype (⟨ι α, hιR _⟩ * ⟨ξt, hξtR⟩ + ⟨ι β, hιR _⟩ * ⟨ξ0, hξ0R⟩ + ⟨ι γ, hιR _⟩ * ⟨ξ1, hξ1R⟩)
      rw [map_one, map_add, map_add, map_mul, map_mul, map_mul]
      exact hone
    have := congrArg mkQ hR1
    rw [map_one, map_add, map_add, map_mul, map_mul, map_mul, hQξt, mul_zero, zero_add, hb0, hg0, ← he0, ← he1] at this
    exact this.symm

  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hmon1 : ∀ a b : W, (Polynomial.X ^ (q + 1) - Polynomial.C a * Polynomial.X ^ q + Polynomial.C b * Polynomial.X : Polynomial W).Monic := by
    intro a b
    have e : (Polynomial.X ^ (q + 1) - Polynomial.C a * Polynomial.X ^ q + Polynomial.C b * Polynomial.X : Polynomial W) =
        Polynomial.X ^ (q + 1) + (Polynomial.C b * Polynomial.X - Polynomial.C a * Polynomial.X ^ q) := by ring
    rw [e]
    refine (Polynomial.monic_X_pow (q + 1)).add_of_left ?_
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le b) (by exact_mod_cast (by omega : 1 < q + 1))
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le q a) (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self q))
  have hmon2 : ∀ a : W, (Polynomial.X ^ q - Polynomial.C a * Polynomial.X : Polynomial W).Monic := by
    intro a
    have e : (Polynomial.X ^ q - Polynomial.C a * Polynomial.X : Polynomial W) = Polynomial.X ^ q + (-(Polynomial.C a * Polynomial.X)) := by ring
    rw [e]
    refine (Polynomial.monic_X_pow q).add_of_left ?_
    rw [Polynomial.degree_X_pow, Polynomial.degree_neg]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le a) (by exact_mod_cast (by omega : 1 < q))
  have hint : ∀ (z : L) (hz : z ∈ R), ψ.IsIntegralElem (mkQ ⟨z, hz⟩) := by
    by_cases htriv : (1 : ↥R.toSubring ⧸ 𝔑) = 0
    · intro z hz
      refine ⟨Polynomial.X, Polynomial.monic_X, ?_⟩
      rw [Polynomial.eval₂_X]
      calc mkQ ⟨z, hz⟩ = mkQ ⟨z, hz⟩ * 1 := (mul_one _).symm
        _ = 0 := by rw [htriv, mul_zero]
    haveI hnt : Nontrivial (↥R.toSubring ⧸ 𝔑) := ⟨⟨1, 0, htriv⟩⟩
    have hq0 : ((q : ℕ) : ↥R.toSubring ⧸ 𝔑) = 0 := by
      have := hψmax _ hqW
      rwa [map_natCast] at this
    haveI hchar : CharP (↥R.toSubring ⧸ 𝔑) q := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hq0

    have core : ∀ (a0 a1 : ↥R.toSubring ⧸ 𝔑) (b g : W), IsUnit g →
        ψ b * a0 + ψ g * a1 = 1 → a0 * a1 ^ q = a0 ^ q * a1 →
        ψ.IsIntegralElem a0 ∧ ψ.IsIntegralElem a1 := by
      intro a0 a1 b g hg hlin hfr
      obtain ⟨gi, hgi⟩ := hg.exists_right_inv
      have hgA0 : ψ g * ψ gi = 1 := by rw [← map_mul, hgi, map_one]
      have ha1 : a1 = ψ gi + ψ (-(gi * b)) * a0 := by
        have h1 := congrArg (fun z => ψ gi * z) hlin
        simp only [mul_add, mul_one] at h1
        rw [map_neg, map_mul]
        linear_combination h1 - a1 * hgA0
      have hfrob : (ψ gi + ψ (-(gi * b)) * a0) ^ q = ψ (gi ^ q) + ψ ((-(gi * b)) ^ q) * a0 ^ q := by
        rw [add_pow_char, mul_pow, ← map_pow, ← map_pow]
      have hstar : ψ ((-(gi * b)) ^ q - (-(gi * b))) * a0 ^ (q + 1) - ψ gi * a0 ^ q + ψ (gi ^ q) * a0 = 0 := by
        have h := hfr
        rw [ha1, hfrob] at h
        rw [map_sub]
        linear_combination h
      have hint0 : ψ.IsIntegralElem a0 := by
        by_cases hd : IsUnit ((-(gi * b)) ^ q - (-(gi * b)))
        · obtain ⟨di, hdi⟩ := hd.exists_right_inv
          have hone' : ψ ((-(gi * b)) ^ q - (-(gi * b))) * ψ di = 1 := by rw [← map_mul, hdi, map_one]
          refine ⟨_, hmon1 (di * gi) (di * gi ^ q), ?_⟩
          simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
            Polynomial.eval₂_X_pow, Polynomial.eval₂_X, map_mul]
          have h2 := congrArg (fun z => ψ di * z) hstar
          simp only [mul_zero] at h2
          linear_combination h2 - a0 ^ (q + 1) * hone'
        · have hd0 : ψ ((-(gi * b)) ^ q - (-(gi * b))) = 0 := hψmax _ ((IsLocalRing.mem_maximalIdeal _).mpr hd)
          refine ⟨_, hmon2 (g * gi ^ q), ?_⟩
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
            Polynomial.eval₂_X_pow, Polynomial.eval₂_X, map_mul]
          linear_combination (-(ψ g)) * hstar + (ψ g * a0 ^ (q + 1)) * hd0 - (a0 ^ q) * hgA0
      refine ⟨hint0, ?_⟩
      rw [ha1]
      exact (ψ.isIntegralElem_map).add ψ ((ψ.isIntegralElem_map).mul ψ hint0)

    have he01 : ψ.IsIntegralElem e0 ∧ ψ.IsIntegralElem e1 := by
      by_cases hg : IsUnit g0
      · exact core e0 e1 b0 g0 hg hrel1 hrel2
      · by_cases hb : IsUnit b0
        · have h := core e1 e0 g0 b0 hb (by rw [add_comm]; exact hrel1) (by rw [mul_comm, ← hrel2, mul_comm])
          exact ⟨h.2, h.1⟩
        · exfalso
          apply htriv
          have hb0' : ψ b0 = 0 := hψmax _ ((IsLocalRing.mem_maximalIdeal _).mpr hb)
          have hg0' : ψ g0 = 0 := hψmax _ ((IsLocalRing.mem_maximalIdeal _).mpr hg)
          rw [← hrel1, hb0', hg0', zero_mul, zero_mul, add_zero]

    intro z hz
    have hz' := (hRdef z).mp hz
    revert hz
    induction hz' using Algebra.adjoin_induction with
    | mem z hzgen =>
        intro hz
        obtain ⟨i, hi, hzi⟩ := hzgen
        obtain ⟨a, i', hi', hidec⟩ := Ideal.mem_span_insert.mp hi
        obtain ⟨b, i'', hi'', hi'dec⟩ := Ideal.mem_span_insert.mp hi'
        obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hi''
        have hzeq : z = ι a * ξt + ι b * ξ0 + ι c' * ξ1 := by
          have : z = ι i * inv := by
            calc z = z * (ι s * inv) := by rw [hsinv, mul_one]
              _ = (z * ι s) * inv := by ring
              _ = ι i * inv := by rw [hzi]
          rw [this, hidec, hi'dec, ← hc']
          simp only [map_add, map_mul, hξtdef, hξ0def, hξ1def]
          ring
        obtain ⟨wa, hwa⟩ := hconstQ a
        obtain ⟨wb, hwb⟩ := hconstQ b
        obtain ⟨wc, hwc⟩ := hconstQ c'
        have : mkQ ⟨z, hz⟩ = ψ wa * mkQ ⟨ξt, hξtR⟩ + ψ wb * e0 + ψ wc * e1 := by
          rw [← hwa, ← hwb, ← hwc, he0, he1, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add]
          congr 1
          exact Subtype.ext hzeq
        rw [this, hQξt, mul_zero, zero_add]
        exact ((ψ.isIntegralElem_map).mul ψ he01.1).add ψ ((ψ.isIntegralElem_map).mul ψ he01.2)
    | algebraMap g =>
        intro hz
        obtain ⟨w, hw⟩ := hconstQ g
        have : mkQ ⟨algebraMap S L g, hz⟩ = ψ w := by
          have e : (⟨algebraMap S L g, hz⟩ : ↥R.toSubring) = ⟨ι g, hιR g⟩ := Subtype.ext (by show algebraMap S L g = ι g; rw [hιalg])
          rw [e]; exact hw
        rw [this]
        exact ψ.isIntegralElem_map
    | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
        intro hz
        have h₁ : z₁ ∈ R := (hRdef _).mpr hz₁
        have h₂ : z₂ ∈ R := (hRdef _).mpr hz₂
        have : mkQ ⟨z₁ + z₂, hz⟩ = mkQ ⟨z₁, h₁⟩ + mkQ ⟨z₂, h₂⟩ := by rw [← map_add]; rfl
        rw [this]
        exact (ih₁ h₁).add ψ (ih₂ h₂)
    | mul z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
        intro hz
        have h₁ : z₁ ∈ R := (hRdef _).mpr hz₁
        have h₂ : z₂ ∈ R := (hRdef _).mpr hz₂
        have : mkQ ⟨z₁ * z₂, hz⟩ = mkQ ⟨z₁, h₁⟩ * mkQ ⟨z₂, h₂⟩ := by rw [← map_mul]; rfl
        rw [this]
        exact (ih₁ h₁).mul ψ (ih₂ h₂)

  obtain ⟨p, hpm, hp0⟩ := hint x hxR
  refine ⟨p, hpm, ?_⟩
  have hE : Polynomial.eval₂ φR ⟨x, hxR⟩ p ∈ 𝔑 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := Polynomial.hom_eval₂ p φR mkQ ⟨x, hxR⟩
    rw [this]
    exact hp0
  obtain ⟨y1, hy1, y2, hy2, hsum⟩ := Submodule.mem_sup.mp hE
  obtain ⟨r1, hr1⟩ := Ideal.mem_span_singleton'.mp hy1
  obtain ⟨n, fc, gk, hy2sum⟩ := Submodule.mem_span_set'.mp hy2
  have hgk : ∀ k, ∃ m ∈ (𝔐 : Set S), ιR m = (gk k : ↥R.toSubring) := fun k => (gk k).2
  choose m hm𝔐 hmeq using hgk
  have hgkL : ∀ k, (((gk k : ↥R.toSubring)) : L) = ι (m k) := fun k => by rw [← hmeq k]
  refine ⟨(r1 : L), r1.2, n, m, fun k => ((fc k : ↥R.toSubring) : L), hm𝔐, fun k => (fc k).2, ?_⟩

  have hLHS : Polynomial.eval x (p.map (ι.comp φW)) = ((Polynomial.eval₂ φR ⟨x, hxR⟩ p : ↥R.toSubring) : L) := by
    rw [← Polynomial.eval₂_eq_eval_map]
    have := Polynomial.hom_eval₂ p φR (R.toSubring.subtype) ⟨x, hxR⟩
    exact this.symm
  have e1 : ∀ y : ↥R.toSubring, (y : L) = R.toSubring.subtype y := fun _ => rfl
  have hsumL : (((∑ k, fc k • ((gk k : ↥R.toSubring))) : ↥R.toSubring) : L) = ∑ k, ι (m k) * ((fc k : ↥R.toSubring) : L) := by
    rw [e1, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_eq_mul, map_mul, ← e1, ← e1, hgkL, mul_comm]
  rw [hLHS, ← hsum, ← hr1, ← hy2sum, Subring.coe_add, hsumL, Subring.coe_mul]
  show (r1 : L) * ξt + ∑ k, ι (m k) * ((fc k : ↥R.toSubring) : L) =
    (ι T * inv) * (r1 : L) + ∑ k, ι (m k) * ((fc k : ↥R.toSubring) : L)
  rw [hξtdef]
  ring

end LocalFinAux

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W)) :

      ∀ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
        let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
        ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J →
          ∃ p : Polynomial A, p.Monic ∧
            ∃ (b' : ↥K) (_ : b' ∈ Ba) (n : ℕ) (c : Fin n → ↥(chartAlgFin A (↥K) j)) (b : Fin n → ↥K),
              (∀ k, c k ∈ y) ∧ (∀ k, b k ∈ Ba) ∧
              Polynomial.aeval (((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) p =
                algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * b' +
                  ∑ k, ((c k : ↥(chartAlgFin A (↥K) j)) : ↥K) * b k := by
  classical
  intro a haJ ha0 Ba i hi

  let STK : Type := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
  let CMP : Type := (AdicCompletion (IsLocalRing.maximalIdeal STK) STK)
  let toC : STK →+* CMP := algebraMap STK CMP
  let S : Type := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
  let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
  let germY : ↥(chartAlgFin A (↥K) j) →+* STK :=
    ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
      ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A (↥K) j))).inv.hom)
  let Ψ : ↥(chartAlgFin A (↥K) j) →+* S := (e₁ : CMP →+* S).comp (toC.comp germY)
  let s : S := Ψ a
  let Lₛ : Type := Localization.Away s
  let ι : S →+* Lₛ := algebraMap S Lₛ
  let R : Subalgebra S Lₛ := Algebra.adjoin S {z : Lₛ | ∃ i ∈ Ideal.span ({mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S), z * ι s = ι i}

  have hsinv : ι s * IsLocalization.Away.invSelf (S := Lₛ) s = 1 := IsLocalization.Away.mul_invSelf s
  have hφW : ∀ w : W₁, algebraMap W₁ S w = mkS (MvPowerSeries.C w) := fun w => rfl
  have hrelS : mkS (MvPowerSeries.C (σ₁ (ϖt ^ (q + 1)))) * mkS v₁ = mkS f₁ * mkS u₁ := by
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hmk : mkS (MvPowerSeries.C (σ₁ ϖt)) ^ (q + 1) = mkS (MvPowerSeries.C (σ₁ (ϖt ^ (q + 1)))) := by
    rw [← map_pow, ← map_pow, ← map_pow]
  have hmkf : mkS f₁ = (mkS (MvPowerSeries.X 0) * mkS (MvPowerSeries.X 1) ^ q - mkS (MvPowerSeries.X 0) ^ q * mkS (MvPowerSeries.X 1))
      + mkS (f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_sub, ← map_add]
    congr 1
    simp only [DrinfeldCurve.LocalChart.drinfeldForm]
    ring
  have hrel : mkS (MvPowerSeries.C (σ₁ ϖt)) ^ (q + 1) * mkS v₁ =
      (mkS (MvPowerSeries.X 0) * mkS (MvPowerSeries.X 1) ^ q - mkS (MvPowerSeries.X 0) ^ q * mkS (MvPowerSeries.X 1)
        + mkS (f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁)) * mkS u₁ := by
    rw [hmk, hrelS, hmkf]
  have hh : mkS (f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁) ∈
      (Ideal.span ({mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S)) ^ ((q + 1) + 1) := by
    have h1 := Ideal.mem_map_of_mem mkS hf₁
    rw [Ideal.map_pow, Ideal.map_span, Set.image_pair] at h1
    exact h1

  have hconstW : ∀ g : S, ∃ w : W₁, g - mkS (MvPowerSeries.C w) ∈
      Ideal.span ({mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S) := by
    intro g
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective g
    refine ⟨MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G, ?_⟩
    show mkS G - mkS (MvPowerSeries.C (MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G)) ∈ _
    rw [← map_sub]
    let G' : MvPowerSeries (Fin 2) W₁ := G - MvPowerSeries.C (MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G)
    show mkS G' ∈ _
    have hG'0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G' = 0 := by
      show MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (G - MvPowerSeries.C (MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G)) = 0
      rw [map_sub, MvPowerSeries.coeff_C, if_pos rfl, sub_self]
    let H : MvPowerSeries (Fin 2) W₁ := fun m => if m 0 = 0 then MvPowerSeries.coeff m G' else 0
    have hH : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m H = if m 0 = 0 then MvPowerSeries.coeff m G' else 0 := fun m => rfl
    have hdiv0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁) ∣ G' - H := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hH, if_pos hm, sub_self]
    have hdiv1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W₁) ∣ H := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm1
      rw [hH]
      by_cases hm0 : m 0 = 0
      · rw [if_pos hm0]
        have : m = 0 := by
          ext i; fin_cases i
          · exact hm0
          · exact hm1
        rw [this]; exact hG'0
      · rw [if_neg hm0]
    obtain ⟨A0, hA0⟩ := hdiv0
    obtain ⟨A1, hA1⟩ := hdiv1
    have hGsum : G' = MvPowerSeries.X 0 * A0 + MvPowerSeries.X 1 * A1 := by rw [← hA0, ← hA1]; ring
    rw [hGsum, map_add, map_mul, map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)) (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
    · simp
    · simp

  have hBa : Ba = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A := rfl
  have hxBa : ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba := by
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨i, hi, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩

  have hK2 := ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁.1
  have hK2c := hK2
  obtain ⟨hcen, hdense, hΨconst, hres, hWres, hcomapσ, hSmax1, hSmax2, -⟩ := hK2c
  obtain ⟨hK1i, -, -⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK3 := ModularCurve.FullLevel.AuxLevelOne.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
    q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hcen hdense hres ⟨hSmax1, hSmax2⟩
  have hΨJ := hK3.1

  obtain ⟨Φ, hΦC, hΦJ, -, hΦR, hFIB⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked_of_dvd
      q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ a haJ ha0
  have hconstA : ∀ g : S, ∃ a₀ : A, g - ((algebraMap W₁ S).comp σ₁) a₀ ∈
      Ideal.span ({mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S) := by
    intro g
    obtain ⟨w, hw⟩ := hconstW g
    obtain ⟨a₀, ha₀⟩ := hWres w
    rw [hσ₁, Ideal.mem_span_singleton'] at ha₀
    obtain ⟨r, hr⟩ := ha₀
    refine ⟨a₀, ?_⟩
    have : g - ((algebraMap W₁ S).comp σ₁) a₀ = (g - mkS (MvPowerSeries.C w)) + mkS (MvPowerSeries.C (σ₁ ϖ)) * mkS (MvPowerSeries.C r) := by
      rw [RingHom.comp_apply, hφW, ← map_mul, ← map_mul, mul_comm (σ₁ ϖ) r, hr, map_sub, map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ hw (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have hs : s ∈ Ideal.span ({mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S) := by
    have h1 := Ideal.mem_map_of_mem Ψ haJ
    rw [hΨJ] at h1
    exact h1

  obtain ⟨p, hpm, r, hr, n, m, r', hm, hr', hev⟩ :=
    LocalFinAux.core q A ϖ hϖ hAq S ((algebraMap W₁ S).comp σ₁)
      (mkS (MvPowerSeries.C (σ₁ ϖt))) (mkS (MvPowerSeries.X 0)) (mkS (MvPowerSeries.X 1)) (mkS u₁) (mkS v₁)
      (mkS (f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁)) (hu₁.map mkS) hrel hh
      (mkS (MvPowerSeries.C (σ₁ ϖ))) rfl hconstA Lₛ ι rfl s (IsLocalization.Away.invSelf (S := Lₛ) s) hsinv hs R
      (fun z => Iff.rfl) (Φ ⟨_, hxBa⟩) (hΦR ⟨_, hxBa⟩)

  have hΦalg : Φ.comp (algebraMap A ↥Ba) = ι.comp ((algebraMap W₁ S).comp σ₁) := by
    ext a₀
    have hmemC : ((algebraMap A ↥(chartAlgFin A (↥K) j) a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba := by
      rw [hBa, Subalgebra.mem_restrictScalars]
      exact Subalgebra.algebraMap_mem _ (algebraMap A ↥(chartAlgFin A (↥K) j) a₀)
    have e1 : algebraMap A ↥Ba a₀ = ⟨((algebraMap A ↥(chartAlgFin A (↥K) j) a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K), hmemC⟩ := by
      apply Subtype.ext
      rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
    show Φ (algebraMap A ↥Ba a₀) = ι ((algebraMap W₁ S) (σ₁ a₀))
    rw [e1, hΦC, hΨconst a₀]
    rfl
  have hbeq : Φ (Polynomial.aeval (⟨_, hxBa⟩ : ↥Ba) p) =
      Polynomial.eval (Φ ⟨_, hxBa⟩) (p.map (ι.comp ((algebraMap W₁ S).comp σ₁))) := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hΦalg, Polynomial.eval₂_eq_eval_map]
  have hant : ∃ (r : Lₛ) (_ : r ∈ R) (n : ℕ) (m : Fin n → S) (r' : Fin n → Lₛ),
      (∀ k, m k ∈ Ideal.span ({mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} : Set S)) ∧
      (∀ k, r' k ∈ R) ∧
      Φ (Polynomial.aeval (⟨_, hxBa⟩ : ↥Ba) p) =
        (ι (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lₛ) s) * r + ∑ k, ι (m k) * r' k :=
    ⟨r, hr, n, m, r', hm, hr', hbeq.trans hev⟩
  obtain ⟨b', hb', n', c, b'', hc, hb'', heqK⟩ := hFIB (Polynomial.aeval (⟨_, hxBa⟩ : ↥Ba) p) hant
  refine ⟨p, hpm, b', hb', n', c, b'', hc, hb'', ?_⟩
  rw [← heqK, Polynomial.aeval_subalgebra_coe p Ba ⟨_, hxBa⟩]

end S_ModularCurve_FullLevel_AuxLevelOne_exists_monic_aeval_div_eq_of_mem_centre_blowupChart_supersingular_fibre_of_drinfeldChartWitness_linked_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_monic_aeval_div_eq_of_mem_centre_blowupChart_supersingular_fibre_of_drinfeldChartWitness_linked_of_dvd (solution)
