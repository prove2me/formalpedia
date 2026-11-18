-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:26:49.945707+00:00
-- url     : https://prove2.me/submissions/aeb78315-c4eb-455f-b9a3-410d9f9367fb

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics
import Theorems.Thm_GreedyColoringLCA969_LowerBound_finite_amplification
import Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_2

open Filter Asymptotics
namespace GreedyColoringLCA969.LowerBound

theorem eventually_exponential_dominates (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ 8*a*x < (2 : ℝ) ^ (C*x/log2 x) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < C * (Real.log 2)^2 / 4 := by positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).def hc
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (8*a)))
  filter_upwards [hsmall,hlog,eventually_ge_atTop (2 : ℝ)] with x hx hxa hx2
  have hxp : 0 < x := by linarith
  have hlxp : 0 < Real.log x := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)), id_eq, abs_of_pos hxp] at hx
  have hprod : Real.log (8*a*x) * Real.log x < C * (Real.log 2)^2 * x := by
    rw [Real.log_mul (by positivity : 8*a ≠ 0) hxp.ne']
    have h1 := mul_le_mul_of_nonneg_right hxa hlxp.le
    nlinarith
  have hexp : Real.log (8*a*x) < Real.log 2 * (C*x/log2 x) := by
    apply (lt_div_iff₀ hlxp).mpr at hprod
    have heq : Real.log 2 * (C*x/log2 x) = C * (Real.log 2)^2*x/Real.log x := by
      unfold log2
      field_simp
      <;> ring
    rw [heq]
    exact hprod
  refine ⟨hx2,?_⟩
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := Real.exp_lt_exp.mpr hexp
  simpa only [Real.exp_log (by positivity : 0 < 8*a*x)] using hh

theorem degree_parameters (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∃ D K : ℕ, 1 ≤ D ∧
      6 * (2 : ℝ) ^ ((c/2)*x/log2 x) / δ ≤ ((D-1 : ℕ) : ℝ) ∧
      (K : ℝ) ≤ c*x/log2 x ∧
      2*x*D < (2 : ℝ) ^ ((K-1 : ℕ) : ℝ) := by
  let C := c/2
  let a := 6/δ + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 2 < a := by
    dsimp [a]
    have hh : 0 < 6/δ := by positivity
    linarith
  filter_upwards [eventually_exponential_dominates C a hC (by linarith)] with x hx
  obtain ⟨hx2,hqbig⟩ := hx
  let t := C*x/log2 x
  let q := (2 : ℝ)^t
  have hxp : 0 < x := by linarith
  have hL : 0 < log2 x := div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  have ht : 0 < t := by dsimp [t]; positivity
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : 1 ≤ q := Real.one_le_rpow (by norm_num) ht.le
  have ht1 : 1 < t := by
    by_contra hn
    have hh : q ≤ 2 := by simpa [q] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_of_not_gt hn)
    change 8*a*x < q at hqbig
    nlinarith
  let D := ⌈6*q/δ⌉₊ + 1
  let K := ⌊c*x/log2 x⌋₊
  have hK : 2 ≤ K := by
    apply Nat.le_floor
    have heq : c*x/log2 x = 2*t := by dsimp [t,C]; ring
    rw [heq]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hbudget : 6*q/δ ≤ ((D-1 : ℕ) : ℝ) := by
    simpa only [D,Nat.add_sub_cancel] using Nat.le_ceil (6*q/δ)
  have hDupper : (D : ℝ) ≤ a*q := by
    have hceil : (⌈6*q/δ⌉₊ : ℝ) < 6*q/δ+1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 6*q/δ+2 ≤ a*q := by
      have heq : a*q = 6*q/δ+2*q := by dsimp [a]; ring
      rw [heq]
      linarith
    dsimp [D]
    push_cast
    linarith
  have hKlo : (K : ℝ) ≤ c*x/log2 x := Nat.floor_le (by positivity)
  have hKhi : c*x/log2 x < (K : ℝ)+1 := Nat.lt_floor_add_one _
  have hKsub : ((K-1 : ℕ) : ℝ) = (K : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hpow : q^2/4 ≤ (2 : ℝ)^((K-1 : ℕ):ℝ) := by
    have hex : 2*t-2 ≤ ((K-1 : ℕ):ℝ) := by
      rw [hKsub]
      have heq : c*x/log2 x = 2*t := by dsimp [t,C]; ring
      rw [heq] at hKhi
      linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hex
    convert hh using 1
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    rw [show 2*t = t*2 by ring,Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [q]
  refine ⟨D,K,hD,hbudget,hKlo,?_⟩
  have h1 := mul_le_mul_of_nonneg_left hDupper (by positivity : (0 : ℝ) ≤ 2*x)
  have h2 := mul_lt_mul_of_pos_right hqbig hq
  change 8*a*x < q at hqbig
  change 8*a*x*q < q*q at h2
  nlinarith

end GreedyColoringLCA969.LowerBound


open scoped ENNReal Classical
open MeasureTheory Filter
open GreedyColoringLCA969.LowerBound

theorem solution (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ Δ0 : ℕ, 2 ≤ Δ0 ∧
      ∀ Δ : ℕ, Δ0 ≤ Δ → ∀ A : Algorithm .standard,
        UniformlyEfficient A Δ ((2 : ℝ) ^ (C * Δ / log2 (Δ : ℝ))) ε →
          ∃ (n : ℕ) (R : Representation n),
            MaxDegreeAtMost R.graph (Δ : ℝ) ∧
            successProbability A R ≤ ENNReal.ofReal δ := by
  classical
  by_cases hδ1 : δ ≤ 1
  · obtain ⟨c,C',hc,hC',hgraphs⟩ := lemma_3_2 (ε/4) (by positivity)
    obtain ⟨a,ha⟩ := eventually_atTop.mp (degree_parameters c δ hc hδ)
    obtain ⟨Δ0,hΔ0⟩ := exists_nat_gt (max (max a C') 2)
    have hΔ02 : 2 ≤ Δ0 := by
      have hh := (le_max_right (max a C') 2).trans_lt hΔ0
      exact_mod_cast hh.le
    refine ⟨c/2,by positivity,Δ0,hΔ02,?_⟩
    intro Δ hΔ A hA
    have hcast : (Δ0 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    have hΔ2 : 2 ≤ Δ := hΔ02.trans hΔ
    have hΔC : C' < (Δ : ℝ) := ((le_max_right a C').trans (le_max_left _ _)).trans_lt hΔ0 |>.trans_le hcast
    have hΔa : a ≤ (Δ : ℝ) := ((le_max_left a C').trans (le_max_left _ _)).trans (hΔ0.le.trans hcast)
    obtain ⟨D,K,hD,hbudget,hK,hlarge⟩ := ha Δ hΔa
    let g : ℝ := max C' ((2*Δ*D+1 : ℕ) : ℝ) + 1
    have hgC : C' < g := by dsimp [g]; linarith [le_max_left C' ((2*Δ*D+1 : ℕ) : ℝ)]
    obtain ⟨n,G,hn,hdegree,hgirth,hhigh⟩ := hgraphs Δ g hΔC hgC
    have hgirth' : GirthAtLeast G (2*Δ*D+1 : ℕ) := by
      intro v p hp
      exact (show ((2*Δ*D+1 : ℕ) : ℝ) ≤ g by dsimp [g]; linarith [le_max_right C' ((2*Δ*D+1 : ℕ) : ℝ)]).trans (hgirth v p hp)
    have hlarge' : 2*Δ*D < 2^(K-1) := by
      rw [Real.rpow_natCast] at hlarge
      exact_mod_cast hlarge
    have hhigh' : ∀ colors : Fin n → ℕ+, IsProper G colors →
        (1-ε/4)*(n:ℝ) ≤ (Nat.card {v : Fin n // (K:ℝ) ≤ ((colors v).val : ℝ)} : ℝ) := by
      intro colors hcolors
      apply (hhigh colors hcolors).trans
      apply Nat.cast_le.mpr
      apply Nat.card_le_card_of_injective
        (fun v : {v : Fin n // c*Δ/log2 (Δ:ℝ) ≤ ((colors v).val:ℝ)} =>
          (⟨v.val,hK.trans v.prop⟩ : {v : Fin n // (K:ℝ) ≤ ((colors v).val:ℝ)}))
      intro u v huv
      exact Subtype.ext (congrArg (fun z : {v : Fin n // (K:ℝ) ≤ ((colors v).val:ℝ)} => z.val) huv)
    exact finite_amplification G hn Δ D K (by omega) hD hdegree hgirth' hlarge' ε δ _ hε hδ hδ1
      (Real.rpow_pos_of_pos (by norm_num) _) hbudget hhigh' A hA
  · have hδge : 1 ≤ δ := (lt_of_not_ge hδ1).le
    let R : Representation 0 := ⟨⊥,⟨fun _ => [],fun v => Fin.elim0 v⟩⟩
    refine ⟨1,by norm_num,2,le_rfl,?_⟩
    intro Δ hΔ A hA
    refine ⟨0,R,?_,?_⟩
    · intro v
      exact Fin.elim0 v
    · exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hδge)
