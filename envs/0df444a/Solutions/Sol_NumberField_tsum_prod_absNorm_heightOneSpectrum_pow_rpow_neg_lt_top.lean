-- Prove2me | solution 1 for NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0d77faa0-fe21-527e-812a-4e86a69f4c19

import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top

set_option Elab.async false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Asymptotics
open scoped Classical ENNReal Topology nonZeroDivisors

namespace AutomorphicForm
namespace WeylIntegrable

section Fin

variable (F : Type) [Field F] [NumberField F]

local notation "HOS" => HeightOneSpectrum (𝓞 F)

def normProd (k : HOS →₀ ℕ) : ℕ := k.prod fun v n => Ideal.absNorm v.asIdeal ^ n

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I; simp
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable

scoped instance countable_heightOneSpectrum : Countable HOS := by
  haveI := countable_ideal F
  exact Function.Injective.countable (f := fun v : HOS => v.asIdeal) fun v w h => HeightOneSpectrum.ext h

scoped instance countable_finsupp : Countable (HOS →₀ ℕ) := inferInstance

def idealOf (k : HOS →₀ ℕ) : Ideal (𝓞 F) := k.prod fun v n => v.asIdeal ^ n

omit [NumberField F] in
theorem idealOf_ne_bot (k : HOS →₀ ℕ) : idealOf F k ≠ ⊥ := by
  rw [idealOf, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot

theorem absNorm_idealOf (k : HOS →₀ ℕ) : Ideal.absNorm (idealOf F k) = normProd F k := by
  rw [idealOf, normProd, Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun v _ => map_pow _ _ _

theorem coe_idealOf (k : HOS →₀ ℕ) :
    (idealOf F k : FractionalIdeal (𝓞 F)⁰ F) =
      (k.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero).prod fun v (n : ℤ) => ((v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ^ n := by
  rw [Finsupp.prod_mapRange_index (fun _ => zpow_zero _), idealOf, Finsupp.prod, Finsupp.prod,
    ← FractionalIdeal.coeIdealHom_apply, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow, zpow_natCast]

theorem idealOf_injective : Function.Injective (idealOf F) := by
  intro k k' h
  ext v
  have hc : FractionalIdeal.count F v (idealOf F k : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (idealOf F k' : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [h]
  rw [coe_idealOf, coe_idealOf, FractionalIdeal.count_finsuppProd, FractionalIdeal.count_finsuppProd, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hc
  exact_mod_cast hc

def idealCount (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

theorem idealCount_nonneg (n : ℕ) : 0 ≤ idealCount F n := Nat.cast_nonneg _

theorem tendsto_sum_idealCount_div :
    ∃ C : ℝ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, idealCount F k) / n) atTop (𝓝 C) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr fun n => ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, idealCount, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

def zetaTerm (t : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else idealCount F n / (n : ℝ) ^ t

theorem zetaTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ zetaTerm F t n := by
  unfold zetaTerm; split_ifs
  · exact le_rfl
  · exact div_nonneg (idealCount_nonneg F n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem summable_zetaTerm {t : ℝ} (ht : 1 < t) : Summable (zetaTerm F t) := by
  obtain ⟨C, hC⟩ := tendsto_sum_idealCount_div F
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, idealCount F k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ C ?_
    · refine Filter.eventually_atTop.mpr ⟨1, fun n hn h => ?_⟩
      exfalso
      rw [Real.rpow_one] at h
      exact (Nat.cast_ne_zero.mpr (by omega) : (n : ℝ) ≠ 0) h
    · refine hC.congr fun n => ?_
      simp only [Pi.div_apply, Real.rpow_one]
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (t : ℂ)) hO (idealCount_nonneg F) zero_le_one
    (by simpa using ht)
  have hn := hL.norm
  refine hn.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  unfold zetaTerm
  split_ifs with h
  · rfl
  · rw [Complex.norm_of_nonneg (idealCount_nonneg F n), Complex.ofReal_re]

theorem tsum_fibre_card_mul (ψ : ℕ → ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) =
      ∑' n : ℕ, (Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} : ℝ≥0∞) * ψ n := by
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1), ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (Ideal.finite_setOf_absNorm_eq n).to_subtype
  haveI : Finite {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} :=
    Finite.of_injective (fun I => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
      (fun I J h => Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => x.1) h)))
  haveI := Fintype.ofFinite {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n}
  have hconst : ∀ I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n},
      ψ (Ideal.absNorm ((Equiv.sigmaFiberEquiv fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1) ⟨n, I⟩).1) = ψ n :=
    fun I => by rw [Equiv.sigmaFiberEquiv_apply, I.2]
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem card_fibre_le (n : ℕ) :
    (Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} : ℝ≥0∞) ≤ ENNReal.ofReal (idealCount F n) := by
  rw [idealCount, ENNReal.ofReal_natCast]
  haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (Ideal.finite_setOf_absNorm_eq n).to_subtype
  exact_mod_cast Nat.card_le_card_of_injective
    (fun I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n} => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
    (fun I J h => Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => x.1) h)))

theorem tsum_normProd_rpow_neg_lt_top {t : ℝ} (ht : 1 < t) : ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) < ∞ := by
  have ht0 : 0 < t := zero_lt_one.trans ht

  let ι : (HOS →₀ ℕ) → {I : Ideal (𝓞 F) // I ≠ ⊥} := fun k => ⟨idealOf F k, idealOf_ne_bot F k⟩
  have hι : Function.Injective ι := fun k k' h => idealOf_injective F (congrArg Subtype.val h)
  let ψ : ℕ → ℝ≥0∞ := fun n => (n : ℝ≥0∞) ^ (-t)
  have h1 : ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) = ∑' k, ψ (Ideal.absNorm (ι k).1) := by
    refine tsum_congr fun k => ?_; simp only [ψ, ι, absNorm_idealOf]
  have h2 : ∑' k, ψ (Ideal.absNorm (ι k).1) ≤ ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) :=
    ENNReal.tsum_comp_le_tsum_of_injective hι (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ψ (Ideal.absNorm I.1))

  have h3 : ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ψ (Ideal.absNorm I.1) ≤ ∑' n, ENNReal.ofReal (zetaTerm F t n) := by
    rw [tsum_fibre_card_mul]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      have : Nat.card {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = 0} = 0 := by
        rw [Nat.card_eq_zero]; left
        exact ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
      rw [this, Nat.cast_zero, zero_mul]; exact bot_le
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hψ : ψ n = ENNReal.ofReal ((n : ℝ) ^ t)⁻¹ := by
        simp only [ψ]
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hnpos, Real.rpow_neg hnpos.le, ]
      rw [hψ, zetaTerm, if_neg (by omega), div_eq_mul_inv,
        ENNReal.ofReal_mul (idealCount_nonneg F n)]
      exact mul_le_mul' (card_fibre_le F n) le_rfl
  have h4 : ∑' n, ENNReal.ofReal (zetaTerm F t n) = ENNReal.ofReal (∑' n, zetaTerm F t n) :=
    (ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg F t) (summable_zetaTerm F ht)).symm
  calc ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-t)) ≤ ∑' n, ENNReal.ofReal (zetaTerm F t n) := h1.le.trans (h2.trans h3)
    _ < ∞ := by rw [h4]; exact ENNReal.ofReal_lt_top

end Fin

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.AutomorphicForm P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.AutomorphicForm"

end
p2m_reactivate "P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.AutomorphicForm P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.AutomorphicForm.WeylIntegrable"

open NumberField IsDedekindDomain
open scoped ENNReal

theorem solution (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) < ⊤ :=
  AutomorphicForm.WeylIntegrable.tsum_normProd_rpow_neg_lt_top F ht

#print axioms solution

end S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
end P2MW
export P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top (solution)
