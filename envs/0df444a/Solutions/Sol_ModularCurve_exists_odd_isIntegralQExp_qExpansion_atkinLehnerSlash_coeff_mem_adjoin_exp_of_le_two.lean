-- Prove2me | solution 1 for ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0adc319d-e807-54eb-b11d-2ae042b9dccb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_EisensteinWeightOne_e1Chi3IsModular
import Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace AUXODDSMALL

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_Γ1 {N : ℕ} : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by simp [Γ1]

theorem Γ1_le_of_dvd {N N' : ℕ} (h : N ∣ N') : Γ1 N' ≤ Γ1 N :=
  Subgroup.map_mono (ModularCurve.Gamma1_le_of_dvd h)

theorem coeff_mem_of_mul_eq {S : Subfield ℂ} {x a b : PowerSeries ℂ}
    (hb : ∀ n, b.coeff n ∈ S) (hb0 : b ≠ 0) (ha : ∀ n, a.coeff n ∈ S) (h : x * b = a) :
    ∀ n, x.coeff n ∈ S := by
  classical
  have hex : ∃ r, b.coeff r ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hb0 (PowerSeries.ext fun n => by simpa using hno n)
  let r := Nat.find hex
  have hr : b.coeff r ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j, j < r → b.coeff j = 0 := fun j hj => by
    have := Nat.find_min hex hj; simpa using this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congrArg (fun s : PowerSeries ℂ => s.coeff (n + r)) h
    simp only [PowerSeries.coeff_mul] at hn
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hn
    have hsplit : ∑ i ∈ Finset.range (n + r + 1), x.coeff i * b.coeff (n + r - i)
        = ∑ i ∈ Finset.range (n + 1), x.coeff i * b.coeff (n + r - i) := by
      have hsub : Finset.range (n + 1) ⊆ Finset.range (n + r + 1) := Finset.range_subset_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      intro i hi hi'
      simp only [Finset.mem_range] at hi hi'
      rw [hlt (n + r - i) (by omega), mul_zero]
    rw [hsplit, Finset.sum_range_succ, Nat.add_sub_cancel_left] at hn
    have hxn : x.coeff n = (a.coeff (n + r) - ∑ i ∈ Finset.range n, x.coeff i * b.coeff (n + r - i)) / b.coeff r := by
      rw [eq_div_iff hr, ← hn]; ring
    rw [hxn]
    refine div_mem (sub_mem (ha _) (sum_mem fun i hi => mul_mem (ih i (Finset.mem_range.mp hi)) (hb _))) (hb r)

theorem isIntegralQExp_mul {N : ℕ} {k k' : ℤ} {f : ModularForm (Γ1 N) k} {h : ModularForm (Γ1 N) k'}
    {r s : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f r) (hh : ModularCurve.IsIntegralQExp h s) :
    ModularCurve.IsIntegralQExp (f.mul h) (r * s) := by
  unfold ModularCurve.IsIntegralQExp at *
  rw [ModularForm.coe_mul, ← ModularForm.coe_mul, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ1, map_mul, hf, hh]

theorem exists_E1 : ∃ E : ModularForm (Γ1 3) 1, ModularCurve.IsIntegralQExp (⇑E) EisensteinWeightOne.e1Chi3 := by
  obtain ⟨E, hE⟩ := EisensteinWeightOne.e1Chi3IsModular
  refine ⟨E, ?_⟩
  set c : ℕ → ℤ := fun n => PowerSeries.coeff n EisensteinWeightOne.e1Chi3 with hc

  have hchi : ∀ d : ℕ, |EisensteinWeightOne.chiNegThree d| ≤ 1 := by
    intro d
    unfold EisensteinWeightOne.chiNegThree
    split_ifs <;> simp
  have hcbound : ∀ n : ℕ, ‖((c n : ℤ) : ℂ)‖ ≤ 6 * n + 1 := by
    intro n
    rw [Complex.norm_intCast]
    simp only [hc, EisensteinWeightOne.e1Chi3, PowerSeries.coeff_mk]
    split_ifs with h0
    · subst h0; simp
    · have h1 : |EisensteinWeightOne.sigmaChi n| ≤ n := by
        unfold EisensteinWeightOne.sigmaChi
        calc |∑ d ∈ n.divisors, EisensteinWeightOne.chiNegThree d|
            ≤ ∑ d ∈ n.divisors, |EisensteinWeightOne.chiNegThree d| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _d ∈ n.divisors, (1 : ℤ) := Finset.sum_le_sum fun d _ => hchi d
          _ = n.divisors.card := by simp
          _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have h2 : |6 * EisensteinWeightOne.sigmaChi n| ≤ 6 * (n : ℤ) + 1 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 6)]; linarith
      rw [← Int.cast_abs]
      exact_mod_cast h2

  have hsum : ∀ z : ℍ, HasSum (fun n : ℕ => ((c n : ℤ) : ℂ) • Function.Periodic.qParam 1 z ^ n) (E z) := by
    intro z
    have hq : ‖Function.Periodic.qParam 1 z‖ < 1 := by
      have : 0 < 2 * Real.pi * z.im / 1 := by have := z.im_pos; positivity
      simpa [Function.Periodic.qParam, Complex.norm_exp, neg_div] using this
    have hterm : ∀ n : ℕ, ((c n : ℤ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))
        = ((c n : ℤ) : ℂ) • Function.Periodic.qParam 1 z ^ n := by
      intro n
      rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hS : Summable (fun n : ℕ => ((c n : ℤ) : ℂ) • Function.Periodic.qParam 1 z ^ n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => (6 * n + 1) * ‖Function.Periodic.qParam 1 z‖ ^ n)
      · have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖Function.Periodic.qParam 1 z‖) (by simpa using hq)
        have h2 := summable_geometric_of_norm_lt_one (K := ℝ) (by simpa using hq : ‖‖Function.Periodic.qParam 1 z‖‖ < 1)
        have := (h1.mul_left 6).add h2
        refine this.congr fun n => ?_
        simp only [pow_one]; ring
      · intro n
        rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hcbound n) (pow_nonneg (norm_nonneg _) _)
    have := hS.hasSum
    have hEz : (∑' n : ℕ, ((c n : ℤ) : ℂ) • Function.Periodic.qParam 1 z ^ n) = E z := by
      rw [hE z]; exact tsum_congr fun n => (hterm n).symm
    rwa [hEz] at this
  have hcoef : ∀ n, ((c n : ℤ) : ℂ) = (qExpansion 1 (E : ℍ → ℂ)).coeff n := fun n =>
    ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Γ1 hsum n
  exact ModularCurve.isIntegralQExp_iff.mpr hcoef

theorem slash_of_neg_mem {L : ℕ} {w : ℤ} (F : ModularForm (Γ1 L) w) {g : SL(2, ℤ)}
    (hg : -g ∈ CongruenceSubgroup.Gamma1 L) : (⇑F : ℍ → ℂ) ∣[w] g = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
  have h1 : (⇑F : ℍ → ℂ) ∣[w] (-g) = ⇑F := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hg)
  have hneg : (⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
    funext τ
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]
    have hτ : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    have hd : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -1 := by
      rw [ModularGroup.denom_apply]
      simp [Matrix.SpecialLinearGroup.coe_neg]
    rw [hτ, hd, mul_comm]
    congr 1
    rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
  calc (⇑F : ℍ → ℂ) ∣[w] g = (⇑F : ℍ → ℂ) ∣[w] ((-1 : SL(2, ℤ)) * (-g)) := by rw [neg_one_mul, neg_neg]
    _ = ((⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ))) ∣[w] (-g) := SlashAction.slash_mul _ _ _ _
    _ = (((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ)) ∣[w] (-g) := by rw [hneg]
    _ = ((-1 : ℂ) ^ w) • ((⇑F : ℍ → ℂ) ∣[w] (-g)) := by rw [ModularForm.SL_smul_slash]
    _ = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by rw [h1]

theorem slash_eq_sign_smul (E : ModularForm (Γ1 3) 1) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 3) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] g = ε • (⇑E : ℍ → ℂ) := by
  have h10 : ((g 1 0 : ℤ) : ZMod 3) = 0 := CongruenceSubgroup.Gamma0_mem.mp hg
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have hxd : ((g 0 0 : ℤ) : ZMod 3) * ((g 1 1 : ℤ) : ZMod 3) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 3) hdet
    push_cast at this
    rw [h10, mul_zero, sub_zero] at this
    exact this
  have hd3 : ((g 1 1 : ℤ) : ZMod 3) = 1 ∨ ((g 1 1 : ℤ) : ZMod 3) = -1 := by
    have hne : ((g 1 1 : ℤ) : ZMod 3) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hxd; exact zero_ne_one hxd
    revert hne; generalize ((g 1 1 : ℤ) : ZMod 3) = e; decide +revert
  rcases hd3 with hd3 | hd3
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hmem : g ∈ CongruenceSubgroup.Gamma1 3 := by
      rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, hd3, h10⟩
      rw [hd3, mul_one] at hxd; exact hxd
    rw [ModularForm.SL_slash, one_smul]
    exact SlashInvariantFormClass.slash_action_eq E _ (Subgroup.mem_map_of_mem _ hmem)
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hmem : -g ∈ CongruenceSubgroup.Gamma1 3 := by
      rw [CongruenceSubgroup.Gamma1_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h10, neg_zero]
      refine ⟨?_, by rw [hd3, neg_neg], trivial⟩
      rw [hd3, mul_neg, mul_one] at hxd
      exact hxd
    rw [slash_of_neg_mem E hmem, zpow_one]

theorem exists_corr (N : ℕ) (hN : ¬ 3 ∣ N) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 N ∧ (3 : ℤ) ∣ (δ * γ) 1 0 ∧
      (N : ℤ) ∣ (δ * γ) 1 1 - γ 1 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this

  obtain ⟨s, hs⟩ : ∃ s : ℤ, ¬ (3 : ℤ) ∣ γ 0 0 + s * γ 1 0 := by
    by_cases ha : (3 : ℤ) ∣ γ 0 0
    · refine ⟨1, fun h => ?_⟩
      have hc : (3 : ℤ) ∣ γ 1 0 := by
        have := dvd_sub h ha; simpa using this
      have : (3 : ℤ) ∣ 1 := by
        rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      omega
    · exact ⟨0, by simpa using ha⟩
  set x : ℤ := γ 0 0 + s * γ 1 0 with hx
  set t : ℤ := -(γ 1 0 * N * x) with ht
  let δ : SL(2, ℤ) := ⟨!![1, s; (N : ℤ) * t, (N : ℤ) * t * s + 1], by
    rw [Matrix.det_fin_two_of]; ring⟩
  have hδ00 : δ 0 0 = 1 := rfl
  have hδ01 : δ 0 1 = s := rfl
  have hδ10 : δ 1 0 = (N : ℤ) * t := rfl
  have hδ11 : δ 1 1 = (N : ℤ) * t * s + 1 := rfl
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem, hδ00, hδ11, hδ10]
    push_cast
    simp
  ·
    have h10 : (δ * γ) 1 0 = (N : ℤ) * t * γ 0 0 + ((N : ℤ) * t * s + 1) * γ 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hδ10, hδ11]
    have hNx : ¬ (3 : ℤ) ∣ (N : ℤ) * x := by
      intro h
      rcases (Int.prime_three.dvd_mul).mp h with h | h
      · exact hN (by exact_mod_cast h)
      · exact hs h
    have hsq : (3 : ℤ) ∣ 1 - ((N : ℤ) * x) ^ 2 := by
      have h3 : ((N : ℤ) * x) % 3 = 1 ∨ ((N : ℤ) * x) % 3 = 2 := by omega
      rw [Int.dvd_iff_emod_eq_zero]
      rcases h3 with h3 | h3
      · have : (1 - ((N : ℤ) * x) ^ 2) % 3 = (1 - (((N : ℤ) * x) % 3) ^ 2 % 3) % 3 := by
          simp [Int.sub_emod, pow_two, Int.mul_emod]
        rw [this, h3]; norm_num
      · have : (1 - ((N : ℤ) * x) ^ 2) % 3 = (1 - (((N : ℤ) * x) % 3) ^ 2 % 3) % 3 := by
          simp [Int.sub_emod, pow_two, Int.mul_emod]
        rw [this, h3]; norm_num
    rw [h10]
    have : (N : ℤ) * t * γ 0 0 + ((N : ℤ) * t * s + 1) * γ 1 0 = γ 1 0 * (1 - ((N : ℤ) * x) ^ 2) := by
      rw [ht, hx]; ring
    rw [this]
    exact dvd_mul_of_dvd_right hsq _
  · have h11 : (δ * γ) 1 1 = (N : ℤ) * t * γ 0 1 + ((N : ℤ) * t * s + 1) * γ 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hδ10, hδ11]
    rw [h11]
    exact ⟨t * γ 0 1 + t * s * γ 1 1, by ring⟩

end AUXODDSMALL

open AUXODDSMALL UpperHalfPlane in
open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : M ≤ 2) (hMp : 3 ≤ M * p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
  classical
  by_cases hp3 : p = 3
  ·
    subst hp3
    have h3γ : (3 : ℤ) ∣ γ 1 1 := by exact_mod_cast hγp
    exact ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three
      M hM γ hγ h3γ

  set K := IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) with hKdef
  have hpp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hpp.ne_zero
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp0⟩
  haveI : NeZero (3 * M) := ⟨Nat.mul_ne_zero three_ne_zero (NeZero.ne M)⟩
  have hM1 : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h3M : ¬ 3 ∣ M := by
    intro h; have := Nat.le_of_dvd hM1 h; omega
  have hp3M : ¬ p ∣ 3 * M := by
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h)
    · exact hpM h
  have h3N : ¬ 3 ∣ M * p := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact h3M h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h).symm

  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm ℚ (M * p) hMp
  have hw0 : (⇑w.form : ℍ → ℂ) ≠ 0 := by
    intro h0
    apply w.intSeriesC_ne_zero
    have hq : qExpansion 1 (⇑w.form : ℍ → ℂ) = 0 := by
      rw [h0, UpperHalfPlane.qExpansion_zero]
    have hser : w.series = 0 := by
      have hint : (w.series).map (Int.castRingHom ℂ) = 0 := by rw [w.isIntegralQExp, hq]
      exact (PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective) (by rw [hint, map_zero])
    simp [ModularCurve.intSeriesC, hser]
  refine ⟨1, w.form, w.series, odd_one, w.isIntegralQExp, hw0, ?_⟩

  obtain ⟨E, hE⟩ := exists_E1
  obtain ⟨δ, hδ, hδ3, hδN⟩ := exists_corr (M * p) h3N γ
  set γ' : SL(2, ℤ) := δ * γ with hγ'def
  have hγ'M : γ' ∈ CongruenceSubgroup.Gamma0 M := by
    have hδ0 : δ ∈ CongruenceSubgroup.Gamma0 (M * p) := CongruenceSubgroup.Gamma1_in_Gamma0 _ hδ
    have hδ0M : δ ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem] at hδ0 ⊢
      have := congrArg (ZMod.castHom (Nat.dvd_mul_right M p) (ZMod M)) hδ0
      rwa [map_intCast, map_zero] at this
    exact mul_mem hδ0M hγ
  have hγ'3M : γ' ∈ CongruenceSubgroup.Gamma0 (3 * M) := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hM' : (M : ℤ) ∣ γ' 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ'M)
    have h3' : (3 : ℤ) ∣ γ' 1 0 := hδ3
    have hcop : IsCoprime (3 : ℤ) (M : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 3 M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3M
      exact_mod_cast this
    push_cast
    exact hcop.mul_dvd h3' hM'
  have hγ'3 : γ' ∈ CongruenceSubgroup.Gamma0 3 := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hδ3
  have hγ'p : (p : ℤ) ∣ γ' 1 1 := by
    have h1 : ((M * p : ℕ) : ℤ) ∣ γ' 1 1 - γ 1 1 := hδN
    have h2 : (p : ℤ) ∣ γ' 1 1 - γ 1 1 := dvd_trans ⟨(M : ℤ), by push_cast; ring⟩ h1
    simpa using dvd_add h2 hγp

  have hhγ : (⇑w.form : ℍ → ℂ) ∣[(1 : ℤ)] γ' = (⇑w.form : ℍ → ℂ) ∣[(1 : ℤ)] γ := by
    rw [hγ'def, SlashAction.slash_mul]
    congr 1
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq w.form _ (Subgroup.mem_map_of_mem _ hδ)

  obtain ⟨ε, hε, hEγ⟩ := slash_eq_sign_smul E hγ'3
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num

  have hle1 : Γ1 (3 * M * p) ≤ Γ1 (M * p) := Γ1_le_of_dvd (Dvd.intro_left 3 (by ring))
  have hle3 : Γ1 (3 * M * p) ≤ Γ1 3 := Γ1_le_of_dvd (Dvd.intro (M * p) (by ring))
  set h3 : ModularForm (Γ1 (3 * M * p)) 1 := ModularCurve.restrictForm hle1 w.form with hh3
  set E3 : ModularForm (Γ1 (3 * M * p)) 1 := ModularCurve.restrictForm hle3 E with hE3
  set F : ModularForm (Γ1 (3 * M * p)) (1 + 1) := h3.mul E3 with hF
  have hFint : ModularCurve.IsIntegralQExp F (w.series * EisensteinWeightOne.e1Chi3) :=
    isIntegralQExp_mul (f := h3) (h := E3) w.isIntegralQExp hE
  have heven : Even ((1 : ℤ) + 1) := ⟨1, rfl⟩
  have hA := ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even p (3 * M) hp3M
    heven F hFint γ' hγ'3M hγ'p

  obtain ⟨FF, hFF⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p (3 * M) hp3M F γ' hγ'3M hγ'p
  obtain ⟨Fh, hFh⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p (3 * M) hp3M h3 γ' hγ'3M hγ'p
  obtain ⟨FE, hFE⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p (3 * M) hp3M E3 γ' hγ'3M hγ'p

  have hFFmul : (⇑FF : ℍ → ℂ) = ⇑(Fh.mul FE) := by
    rw [hFF, hF, ModularForm.coe_mul h3 E3, ModularForm.coe_mul Fh FE, hFh, hFE, ModularForm.mul_slash_SL2]
    rfl
  have hA' : ∀ n : ℕ, (qExpansion 1 (⇑(Fh.mul FE) : ℍ → ℂ)).coeff n ∈ K := by
    intro n
    have := hA n
    rwa [← hFF, hFFmul] at this

  have hFEfun : (⇑FE : ℍ → ℂ) = ε • (fun τ : ℍ => E (ModularForm.heckeDiagMatrix p • τ)) := by
    rw [hFE]
    ext τ
    rw [hE3, ModularCurve.coe_restrictForm, hEγ, Pi.smul_apply, Pi.smul_apply]
  have hdilfun : (fun τ : ℍ => E (ModularForm.heckeDiagMatrix p • τ)) = ε • (⇑FE : ℍ → ℂ) := by
    rw [hFEfun, smul_smul, hε2, one_smul]
  have hanFE : AnalyticAt ℂ (cuspFunction 1 (⇑FE : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero FE one_pos one_mem_strictPeriods_Γ1
  have hqFE : qExpansion 1 (⇑FE : ℍ → ℂ) = ε • qExpansion 1 (fun τ : ℍ => E (ModularForm.heckeDiagMatrix p • τ)) := by
    rw [hdilfun, UpperHalfPlane.qExpansion_smul hanFE, smul_smul, hε2, one_smul]
  have hεK : ε ∈ K := by
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  have hEcoeff : ∀ m : ℕ, (qExpansion 1 (⇑E : ℍ → ℂ)).coeff m ∈ K := by
    intro m
    rw [← hE.coeff m]
    exact intCast_mem K _
  have hB : ∀ n : ℕ, (qExpansion 1 (⇑FE : ℍ → ℂ)).coeff n ∈ K := by
    intro n
    rw [hqFE, PowerSeries.coeff_smul, smul_eq_mul]
    refine mul_mem hεK ?_
    have hdil := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul E (one_mem_strictPeriods_Γ1 (N := 3)) hp0 n
    simp only [ModularFormClass.qCoeff] at hdil
    rw [hdil]
    split_ifs
    · exact hEcoeff _
    · exact zero_mem _

  have hB0 : qExpansion 1 (⇑FE : ℍ → ℂ) ≠ 0 := by
    intro h0
    have hc := congrArg (fun s : PowerSeries ℂ => s.coeff 0) h0
    simp only [map_zero] at hc
    rw [hqFE, PowerSeries.coeff_smul, smul_eq_mul] at hc
    have hdil := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul E (one_mem_strictPeriods_Γ1 (N := 3)) hp0 0
    simp only [ModularFormClass.qCoeff, dvd_zero, ↓reduceIte, Nat.zero_div] at hdil
    rw [hdil, ← hE.coeff 0] at hc
    have h1 : (PowerSeries.coeff 0 EisensteinWeightOne.e1Chi3 : ℤ) = 1 := by
      simp [EisensteinWeightOne.e1Chi3]
    rw [h1] at hc
    push_cast at hc
    rw [mul_one] at hc
    rcases hε with rfl | rfl <;> norm_num at hc

  have hmul : qExpansion 1 (⇑Fh : ℍ → ℂ) * qExpansion 1 (⇑FE : ℍ → ℂ) = qExpansion 1 (⇑(Fh.mul FE) : ℍ → ℂ) :=
    (ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ1 Fh FE).symm
  have hX := coeff_mem_of_mul_eq (S := K.toSubfield) (fun n => hB n) hB0 (fun n => hA' n) hmul
  intro n
  have hfun : (fun τ : ℍ => ((⇑w.form : ℍ → ℂ) ∣[(1 : ℤ)] γ) (ModularForm.heckeDiagMatrix p • τ)) = ⇑Fh := by
    rw [hFh, hh3, ModularCurve.coe_restrictForm, hhγ]
  rw [hfun]
  exact hX n

end S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two
end P2MW
export P2MW.S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two (solution)
