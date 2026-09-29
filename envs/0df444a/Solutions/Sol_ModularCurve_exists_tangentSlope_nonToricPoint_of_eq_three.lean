-- Prove2me | solution 1 for ModularCurve.exists_tangentSlope_nonToricPoint_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/12126a29-0149-5750-9b91-c142758555ed

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_TateCurve_TorsionParametrization
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Theorems.Thm_TateCurve_pointX_qExpansion
import Theorems.Thm_TateCurve_pointY_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GLT1

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun ModularCurve"

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem nnnorm_coe_unit_of_pow_eq_one (c : Kˣ) {p : ℕ} (hp : p ≠ 0) (hc : c ^ p = 1) :
    ‖(c : K)‖₊ = 1 := by
  have hcp : ((c : K)) ^ p = 1 := by
    have := congrArg (Units.val) hc
    simpa using this
  have h1 : ‖(c : K)‖₊ ^ p = 1 := by
    rw [← nnnorm_pow, hcp, nnnorm_one]
  rcases lt_trichotomy ‖(c : K)‖₊ 1 with hlt | heq | hgt
  · exact absurd h1 (by simpa using (pow_lt_one₀ zero_le hlt hp).ne)
  · exact heq
  · exact absurd h1 (by simpa using (one_lt_pow₀ hgt hp).ne')

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem lattice_mul_slotVal_ne_one (c : Kˣ) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1)
    {p j : ℕ} (hc : c ^ p = 1) (h1j : 1 ≤ j) (hjp : j < p) (n : ℤ) :
    (t ^ p) ^ n * ((c : K) * t ^ j) ≠ 1 := by
  intro h
  have hp0 : p ≠ 0 := by omega
  have hcn : ‖(c : K)‖₊ = 1 := nnnorm_coe_unit_of_pow_eq_one c hp0 hc
  have ht0n : ‖t‖₊ ≠ 0 := by simpa [nnnorm_eq_zero] using ht0

  have hval : ‖(t ^ p) ^ n * ((c : K) * t ^ j)‖₊ = ‖t‖₊ ^ ((p : ℤ) * n + (j : ℤ)) := by
    rw [nnnorm_mul, nnnorm_mul, hcn, one_mul, nnnorm_zpow, nnnorm_pow, nnnorm_pow,
      ← zpow_natCast ‖t‖₊ p, ← zpow_mul, ← zpow_natCast ‖t‖₊ j, ← zpow_add₀ ht0n]
  have h1 : ‖t‖₊ ^ ((p : ℤ) * n + (j : ℤ)) = 1 := by
    rw [← hval, h, nnnorm_one]
  set k : ℤ := (p : ℤ) * n + (j : ℤ) with hk
  have hk0 : k ≠ 0 := by
    intro hk0
    have hbridge : (p : ℤ) * -n = -((p : ℤ) * n) := by ring
    have hpj : (p : ℤ) ∣ (j : ℤ) := ⟨-n, by omega⟩
    have hpj' : (p : ℕ) ∣ j := Int.natCast_dvd_natCast.mp hpj
    have := Nat.le_of_dvd (by omega) hpj'
    omega
  have htpos : 0 < ‖t‖₊ := pos_iff_ne_zero.mpr ht0n
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  ·
    have hm : (0 : ℤ) < -k := by omega
    have hpow : ‖t‖₊ ^ (-k) < 1 := by
      have hnat : ‖t‖₊ ^ (-k) = ‖t‖₊ ^ ((-k).toNat) := by
        rw [← zpow_natCast ‖t‖₊ ((-k).toNat), Int.toNat_of_nonneg hm.le]
      rw [hnat]
      exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)
    have hgt : (1 : ℝ≥0) < ‖t‖₊ ^ k := by
      rw [show k = -(-k) by ring, zpow_neg]
      exact (one_lt_inv₀ (zpow_pos htpos _)).mpr hpow
    exact absurd h1 hgt.ne'
  · exact hk0 hzero
  ·
    have hnat : ‖t‖₊ ^ k = ‖t‖₊ ^ (k.toNat) := by
      rw [← zpow_natCast ‖t‖₊ (k.toNat), Int.toNat_of_nonneg hpos.le]
    rw [hnat] at h1
    exact absurd h1 (pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)).ne

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem hasSum_xfun {w : K} (hw : ‖w‖ < 1) :
    HasSum (fun d : ℕ => (d : K) * w ^ d) (xfun w) := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := K) (r := w) hw
  simpa [xfun] using h

theorem hasSum_yfun {w : K} (hw : ‖w‖ < 1) :
    HasSum (fun d : ℕ => ((d.choose 2 : ℕ) : K) * w ^ d) (yfun w) := by
  have hwne : w ≠ 1 := by rintro rfl; simp at hw
  have hw1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwne)

  have hf : Summable fun k : ℕ => ‖(k : K) * w ^ k‖ := by
    refine summable_norm_mul_geometric_of_norm_lt_one (k := 1) (r := w) hw
      (u := fun n => n) ?_
    refine Asymptotics.isBigO_of_le _ (fun n => ?_)
    simp [pow_one]
  have hg : Summable fun l : ℕ => ‖w ^ l‖ := summable_norm_geometric_of_norm_lt_one hw

  have hx := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := K) (r := w) hw
  have hgeo := hasSum_geometric_of_norm_lt_one hw

  have hinner : ∀ n : ℕ,
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, ((kl.1 : K) * w ^ kl.1) * w ^ kl.2)
        = (((n + 1).choose 2 : ℕ) : K) * w ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        ((k : K) * w ^ k) * w ^ (n - k) = (k : K) * w ^ n := by
      intro k hk
      rw [mul_assoc, ← pow_add]
      congr 2
      have := Finset.mem_range.mp hk
      omega
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    have hgauss : (∑ k ∈ Finset.range (n + 1), (k : K)) = (((n + 1).choose 2 : ℕ) : K) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [Finset.sum_range_id, Nat.choose_two_right, Nat.add_sub_cancel]
    exact hgauss

  have hanti := summable_sum_mul_antidiagonal_of_summable_norm' hf hx.summable hg hgeo.summable
  have hn_summ : Summable fun n : ℕ => (((n + 1).choose 2 : ℕ) : K) * w ^ n :=
    hanti.congr hinner
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hn : HasSum (fun n : ℕ => (((n + 1).choose 2 : ℕ) : K) * w ^ n)
      ((w / (1 - w) ^ 2) * (1 - w)⁻¹) := by
    refine (Summable.hasSum_iff hn_summ).mpr ?_
    rw [← tsum_congr hinner, ← hcauchy, hx.tsum_eq, hgeo.tsum_eq]

  have hshift : HasSum (fun n : ℕ => (((n + 1).choose 2 : ℕ) : K) * w ^ (n + 1))
      (w * ((w / (1 - w) ^ 2) * (1 - w)⁻¹)) := by
    have h := hn.mul_left w
    have heq : (fun n : ℕ => w * ((((n + 1).choose 2 : ℕ) : K) * w ^ n))
        = fun n : ℕ => (((n + 1).choose 2 : ℕ) : K) * w ^ (n + 1) := by
      funext n; ring
    rwa [heq] at h
  have hfull := (hasSum_nat_add_iff (f := fun d : ℕ => ((d.choose 2 : ℕ) : K) * w ^ d) 1).mp
    hshift
  have hval : w * ((w / (1 - w) ^ 2) * (1 - w)⁻¹)
      + ∑ i ∈ Finset.range 1, ((i.choose 2 : ℕ) : K) * w ^ i = yfun w := by
    have h0 : ((Nat.choose 0 2 : ℕ) : K) = 0 := by norm_num [Nat.choose]
    rw [Finset.sum_range_one, pow_zero, h0, zero_mul, add_zero, yfun]
    field_simp
    try ring
  rwa [hval] at hfull

def fiberFinset (g : ℕ × ℕ → ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun x => g x = n)

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem hasSum_of_fiber_sum {fam : ℕ × ℕ → K} {g : ℕ × ℕ → ℕ} {S : K}
    (hbound : ∀ x : ℕ × ℕ, fam x ≠ 0 → x.1 ≤ g x ∧ x.2 ≤ g x)
    (hsum : HasSum fam S)
    (c : ℕ → K) (hc : ∀ n, c n = ∑ x ∈ fiberFinset g n, fam x) :
    HasSum c S := by
  classical

  have hσ : HasSum (fun y : Σ n : ℕ, {x : ℕ × ℕ // g x = n} => fam y.2.1) S := by
    have := (Equiv.sigmaFiberEquiv g).hasSum_iff (f := fam) (a := S)
    exact this.mpr hsum

  refine hσ.sigma (fun n => ?_)
  classical
  have hz : ∀ z : {x : ℕ × ℕ // g x = n},
      z ∉ (fiberFinset g n).subtype (fun x => g x = n) → fam z.1 = 0 := by
    intro z hzmem
    by_contra h0
    apply hzmem
    rw [Finset.mem_subtype]
    have hb := hbound z.1 h0
    rw [z.2] at hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, z.2⟩
  have hval : c n = ∑ z ∈ (fiberFinset g n).subtype (fun x => g x = n), fam z.1 := by
    rw [hc n]
    exact (Finset.sum_subtype_of_mem fam (fun x hx => (Finset.mem_filter.mp hx).2)).symm
  rw [hval]
  exact hasSum_sum_of_ne_finset_zero hz

def armFam (A : ℕ → ℕ → K) (gfun : ℕ → ℕ → ℕ) (t : K) : ℕ × ℕ → K :=
  fun x => (if x.2 ∈ x.1.divisors then A x.1 x.2 else 0) * t ^ gfun x.1 x.2

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem summable_norm_armFam {A : ℕ → ℕ → K} (hA : ∀ M e, e ∈ M.divisors → ‖A M e‖ ≤ 1)
    {gfun : ℕ → ℕ → ℕ} (hgM : ∀ M e, e ∈ M.divisors → M ≤ gfun M e)
    {t : K} (ht : ‖t‖ < 1) :
    Summable fun x : ℕ × ℕ => ‖armFam A gfun t x‖ := by
  have ht0 : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t

  have hterm : ∀ x : ℕ × ℕ, ‖armFam A gfun t x‖
      ≤ (if x.2 ∈ x.1.divisors then ‖t‖ ^ x.1 else 0) := by
    rintro ⟨M, e⟩
    by_cases hdvd : e ∈ M.divisors
    · simp only [armFam, if_pos hdvd]
      calc ‖A M e * t ^ gfun M e‖ = ‖A M e‖ * ‖t‖ ^ gfun M e := by
            rw [norm_mul, norm_pow]
        _ ≤ 1 * ‖t‖ ^ gfun M e :=
            mul_le_mul_of_nonneg_right (hA M e hdvd) (by positivity)
        _ = ‖t‖ ^ gfun M e := one_mul _
        _ ≤ ‖t‖ ^ M := pow_le_pow_of_le_one ht0 ht.le (hgM M e hdvd)
    · simp only [armFam]
      rw [if_neg hdvd, if_neg hdvd]
      simp

  have hmaj : Summable fun x : ℕ × ℕ => (if x.2 ∈ x.1.divisors then ‖t‖ ^ x.1 else 0) := by
    rw [summable_prod_of_nonneg (fun x => by positivity)]
    constructor
    · intro M
      refine summable_of_ne_finset_zero (s := M.divisors) (fun e he => if_neg he)
    ·
      have hrow : ∀ M : ℕ, (∑' e : ℕ, (if e ∈ M.divisors then ‖t‖ ^ M else 0))
          ≤ ((M + 1 : ℕ) : ℝ) * ‖t‖ ^ M := by
        intro M
        rw [tsum_eq_sum (s := M.divisors) (fun e he => if_neg he)]
        calc (∑ e ∈ M.divisors, if e ∈ M.divisors then ‖t‖ ^ M else 0)
            = ∑ e ∈ M.divisors, ‖t‖ ^ M :=
              Finset.sum_congr rfl (fun e he => if_pos he)
          _ = (M.divisors.card : ℝ) * ‖t‖ ^ M := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((M + 1 : ℕ) : ℝ) * ‖t‖ ^ M := by
              have hsub' : M.divisors ⊆ Finset.range (M + 1) := fun e he =>
                Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le he))
              have hcard : M.divisors.card ≤ M + 1 := by
                simpa [Finset.card_range] using Finset.card_le_card hsub'
              have hcast : (M.divisors.card : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right hcast (by positivity)
      have hgeom : Summable fun M : ℕ => ((M + 1 : ℕ) : ℝ) * ‖t‖ ^ M := by
        have hnorm : Summable fun M : ℕ => ‖(((M + 1 : ℕ) : ℝ)) * (‖t‖ : ℝ) ^ M‖ := by
          refine summable_norm_mul_geometric_of_norm_lt_one (k := 1)
            (r := (‖t‖ : ℝ)) (by simpa using ht) (u := fun M => M + 1) ?_
          refine Asymptotics.IsBigO.of_bound 2 ?_
          filter_upwards [Filter.eventually_ge_atTop 1] with M hM
          simp only [Real.norm_natCast, pow_one]
          have h1M : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          push_cast
          linarith
        exact hnorm.of_norm
      refine Summable.of_nonneg_of_le (fun M => tsum_nonneg (fun e => by positivity))
        (fun M => hrow M) hgeom
  exact Summable.of_nonneg_of_le (fun x => norm_nonneg _) hterm hmaj

omit [IsUltrametricDist K] in

theorem arm_hasSum_triple {A : ℕ → ℕ → K} (hA : ∀ M e, e ∈ M.divisors → ‖A M e‖ ≤ 1)
    {gfun : ℕ → ℕ → ℕ} (hgM : ∀ M e, e ∈ M.divisors → M ≤ gfun M e)
    (hge : ∀ M e, e ∈ M.divisors → e ≤ gfun M e)
    {t : K} (ht : ‖t‖ < 1) :
    HasSum (armFam A gfun t) (∑' x : ℕ × ℕ, armFam A gfun t x) ∧
    HasSum (fun n : ℕ => ∑ x ∈ fiberFinset (fun x => gfun x.1 x.2) n, armFam A gfun t x)
      (∑' x : ℕ × ℕ, armFam A gfun t x) ∧
    HasSum (fun M : ℕ => ∑ e ∈ M.divisors, A M e * t ^ gfun M e)
      (∑' x : ℕ × ℕ, armFam A gfun t x) := by
  have hsumm : Summable (armFam A gfun t) := (summable_norm_armFam hA hgM ht).of_norm
  have h1 : HasSum (armFam A gfun t) (∑' x : ℕ × ℕ, armFam A gfun t x) := hsumm.hasSum
  refine ⟨h1, ?_, ?_⟩
  · refine hasSum_of_fiber_sum (fun x hx => ?_) h1 _ (fun n => rfl)
    have hdvd : x.2 ∈ x.1.divisors := by
      by_contra hne
      exact hx (by simp only [armFam]; rw [if_neg hne, zero_mul])
    exact ⟨hgM x.1 x.2 hdvd, hge x.1 x.2 hdvd⟩
  · refine HasSum.prod_fiberwise h1 (fun M => ?_)
    have hz : ∀ e ∉ M.divisors, armFam A gfun t (M, e) = 0 := fun e he => by
      simp only [armFam]; rw [if_neg he, zero_mul]
    have hval : (∑ e ∈ M.divisors, A M e * t ^ gfun M e)
        = ∑ e ∈ M.divisors, armFam A gfun t (M, e) :=
      (Finset.sum_congr rfl (fun e he => by simp only [armFam]; rw [if_pos he])).symm
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hz

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem fiber_sum_eq {A : ℕ → ℕ → K} {gfun : ℕ → ℕ → ℕ}
    (_hgM : ∀ M e, e ∈ M.divisors → M ≤ gfun M e) (t : K) (n : ℕ) :
    ∑ x ∈ fiberFinset (fun x => gfun x.1 x.2) n, armFam A gfun t x
      = (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
          (if gfun M e = n then A M e else 0)) * t ^ n := by
  classical

  have hstep1 : ∑ x ∈ fiberFinset (fun x => gfun x.1 x.2) n, armFam A gfun t x
      = ∑ x ∈ fiberFinset (fun x => gfun x.1 x.2) n,
          (if x.2 ∈ x.1.divisors then A x.1 x.2 else 0) * t ^ n := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hgx : gfun x.1 x.2 = n := (Finset.mem_filter.mp hx).2
    simp [armFam, hgx]
  rw [hstep1, ← Finset.sum_mul]
  congr 1

  rw [fiberFinset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  have hMn : M ≤ n := by
    have := Finset.mem_range.mp hM
    omega
  have hsub : M.divisors ⊆ Finset.range (n + 1) := fun e he => by
    have := Nat.divisor_le he
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun e _ hedvd => by rw [if_neg hedvd, ite_self])]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [if_pos he]

section Ties

variable {p : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in

theorem j_lt_p (hp3 : 3 ≤ p) {j : ℕ} (hjp : j ≤ p / 2) : j < p := by omega

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem norm_slotVal_lt_one (c : Kˣ) (hnc : ‖(c : K)‖₊ = 1) {t : K} (ht : ‖t‖₊ < 1)
    {j : ℕ} (h1j : 1 ≤ j) : ‖(c : K) * t ^ j‖ < 1 := by
  have h : ‖(c : K) * t ^ j‖₊ < 1 := by
    rw [nnnorm_mul, hnc, one_mul, nnnorm_pow]
    calc ‖t‖₊ ^ j ≤ ‖t‖₊ ^ 1 :=
          pow_le_pow_of_le_one (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht.le h1j
      _ = ‖t‖₊ := pow_one _
      _ < 1 := ht
  exact_mod_cast h

omit [IsUltrametricDist K] [CompleteSpace K] [Fact (Nat.Prime p)] in

theorem inv_pow_eq_one (c : Kˣ) (hc : c ^ p = 1) : c⁻¹ ^ p = 1 := by
  rw [inv_pow, hc, inv_one]

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem hasSum_xfun_arm (c : Kˣ) (hnc : ‖(c : K)‖₊ = 1) {t : K} (ht : ‖t‖₊ < 1)
    {j : ℕ} (h1j : 1 ≤ j) :
    HasSum (fun n : ℕ => (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n)
      (xfun ((c : K) * t ^ j)) := by
  have hj0 : 0 < j := by omega
  have hbase := hasSum_xfun (w := (c : K) * t ^ j) (norm_slotVal_lt_one c hnc ht h1j)
  have hinj : Function.Injective (fun d : ℕ => j * d) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hj0 hab
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => j * d) →
      (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n = 0 := by
    intro n hn
    rw [if_neg, zero_mul]
    rintro ⟨d, hd⟩
    exact hn ⟨d, hd.symm⟩
  refine (hinj.hasSum_iff hzero).mp ?_
  have hcong : ((fun n : ℕ =>
        (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n)
          ∘ fun d : ℕ => j * d)
      = fun d : ℕ => (d : K) * ((c : K) * t ^ j) ^ d := by
    funext d
    simp only [Function.comp]
    rw [if_pos (dvd_mul_right j d), Nat.mul_div_cancel_left d hj0, mul_pow, pow_mul]
    ring
  rw [hcong]
  exact hbase

theorem hasSum_yfun_arm (c : Kˣ) (hnc : ‖(c : K)‖₊ = 1) {t : K} (ht : ‖t‖₊ < 1)
    {j : ℕ} (h1j : 1 ≤ j) :
    HasSum (fun n : ℕ =>
        (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n)
      (yfun ((c : K) * t ^ j)) := by
  have hj0 : 0 < j := by omega
  have hbase := hasSum_yfun (w := (c : K) * t ^ j) (norm_slotVal_lt_one c hnc ht h1j)
  have hinj : Function.Injective (fun d : ℕ => j * d) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hj0 hab
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => j * d) →
      (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n = 0 := by
    intro n hn
    rw [if_neg, zero_mul]
    rintro ⟨d, hd⟩
    exact hn ⟨d, hd.symm⟩
  refine (hinj.hasSum_iff hzero).mp ?_
  have hcong : ((fun n : ℕ =>
        (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n)
          ∘ fun d : ℕ => j * d)
      = fun d : ℕ => ((d.choose 2 : ℕ) : K) * ((c : K) * t ^ j) ^ d := by
    funext d
    simp only [Function.comp]
    rw [if_pos (dvd_mul_right j d), Nat.mul_div_cancel_left d hj0, mul_pow, pow_mul]
    ring
  rw [hcong]
  exact hbase

end Ties

theorem hasSum_coeff_slotSubst_tateUnivX_pointX
    (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (c : Kˣ) (hc : c ^ p = 1)
    {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) {j : ℕ} (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst K p c j tateUnivX) * t ^ n)
      (pointX (t ^ p) ((c : K) * t ^ j)) := by
  classical
  have hp0 : p ≠ 0 := by omega
  have hjltp : j < p := j_lt_p hp3 hjp
  have hnc : ‖(c : K)‖₊ = 1 := nnnorm_coe_unit_of_pow_eq_one c hp0 hc
  have hnc' : ‖((c⁻¹ : Kˣ) : K)‖₊ = 1 :=
    nnnorm_coe_unit_of_pow_eq_one c⁻¹ hp0 (inv_pow_eq_one c hc)
  have htR : ‖t‖ < 1 := by exact_mod_cast ht
  have ht0n : ‖t‖₊ ≠ 0 := by simpa [nnnorm_eq_zero] using ht0
  set u : K := (c : K) * t ^ j with hudef

  set A₁ : ℕ → ℕ → K := fun _ e => (e : K) * (c : K) ^ e with hA₁def
  set A₂ : ℕ → ℕ → K := fun _ e => (e : K) * ((c⁻¹ : Kˣ) : K) ^ e with hA₂def
  set A₃ : ℕ → ℕ → K := fun _ e => -(2 * (e : K)) with hA₃def
  set g₁ : ℕ → ℕ → ℕ := fun M e => p * M + j * e with hg₁def
  set g₂ : ℕ → ℕ → ℕ := fun M e => p * M - j * e with hg₂def
  set g₃ : ℕ → ℕ → ℕ := fun M _ => p * M with hg₃def

  have hsupp : ∀ M e : ℕ, e ∈ M.divisors →
      1 ≤ e ∧ e ≤ M ∧ j * e ≤ p * M ∧ j * e + M ≤ p * M := by
    intro M e he
    obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (by
      rintro rfl; exact hM0 (zero_dvd_iff.mp hdvd))
    have heM : e ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd
    have h1 : j * e ≤ j * M := Nat.mul_le_mul_left j heM
    have h2 : (j + 1) * M ≤ p * M := Nat.mul_le_mul_right M (by omega)
    have h3 : (j + 1) * M = j * M + M := by ring
    refine ⟨he1, heM, ?_, ?_⟩ <;> omega

  have hnatle : ∀ e : ℕ, ‖(e : K)‖ ≤ 1 := fun e => IsUltrametricDist.norm_natCast_le_one K e
  have hcoe1 : ‖(c : K)‖ = 1 := by rw [← coe_nnnorm, hnc, NNReal.coe_one]
  have hcoe1' : ‖((c⁻¹ : Kˣ) : K)‖ = 1 := by rw [← coe_nnnorm, hnc', NNReal.coe_one]
  have hA₁b : ∀ M e, e ∈ M.divisors → ‖A₁ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₁def]
    rw [norm_mul, norm_pow, hcoe1, one_pow, mul_one]
    exact hnatle e
  have hA₂b : ∀ M e, e ∈ M.divisors → ‖A₂ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₂def]
    rw [norm_mul, norm_pow, hcoe1', one_pow, mul_one]
    exact hnatle e
  have hA₃b : ∀ M e, e ∈ M.divisors → ‖A₃ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₃def]
    rw [norm_neg]
    calc ‖2 * (e : K)‖ = ‖((2 * e : ℕ) : K)‖ := by push_cast; ring_nf
      _ ≤ 1 := hnatle _

  have hMle : ∀ M : ℕ, M ≤ p * M := fun M => Nat.le_mul_of_pos_left M (by omega)
  have hg₁M : ∀ M e, e ∈ M.divisors → M ≤ g₁ M e := by
    intro M e he; have := hMle M; simp only [hg₁def]; omega
  have hg₁e : ∀ M e, e ∈ M.divisors → e ≤ g₁ M e := by
    intro M e he
    have he' := (hsupp M e he).2.1
    have := hMle M
    simp only [hg₁def]; omega
  have hg₂M : ∀ M e, e ∈ M.divisors → M ≤ g₂ M e := by
    intro M e he
    have h := (hsupp M e he).2.2.2
    simp only [hg₂def]; omega
  have hg₂e : ∀ M e, e ∈ M.divisors → e ≤ g₂ M e := by
    intro M e he
    obtain ⟨-, heM, -, h⟩ := hsupp M e he
    simp only [hg₂def]; omega
  have hg₃M : ∀ M e, e ∈ M.divisors → M ≤ g₃ M e := by
    intro M e he; have := hMle M; simp only [hg₃def]; omega
  have hg₃e : ∀ M e, e ∈ M.divisors → e ≤ g₃ M e := by
    intro M e he
    have := (hsupp M e he).2.1; have := hMle M
    simp only [hg₃def]; omega

  obtain ⟨h1g, h1f, h1r⟩ := arm_hasSum_triple hA₁b hg₁M hg₁e htR
  obtain ⟨h2g, h2f, h2r⟩ := arm_hasSum_triple hA₂b hg₂M hg₂e htR
  obtain ⟨h3g, h3f, h3r⟩ := arm_hasSum_triple hA₃b hg₃M hg₃e htR

  have hdecomp : ∀ n : ℕ, PowerSeries.coeff n (slotSubst K p c j tateUnivX) * t ^ n
      = ((if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n
          + ((∑ x ∈ fiberFinset (fun x => g₁ x.1 x.2) n, armFam A₁ g₁ t x)
            + (∑ x ∈ fiberFinset (fun x => g₂ x.1 x.2) n, armFam A₂ g₂ t x)
            + (∑ x ∈ fiberFinset (fun x => g₃ x.1 x.2) n, armFam A₃ g₃ t x))) := by
    intro n
    rw [ModularCurve.coeff_slotSubst_tateUnivX p c j (by omega) hjltp n]
    rw [fiber_sum_eq hg₁M t n, fiber_sum_eq hg₂M t n, fiber_sum_eq hg₃M t n]
    have hS : (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) *
          (((if n = p * M + j * e then (c : K) ^ e else 0)
            + if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)
            - if n = p * M then 2 else 0))
        = ((∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₁ M e = n then A₁ M e else 0)
          + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₂ M e = n then A₂ M e else 0)
          + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₃ M e = n then A₃ M e else 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨he1, heM, hje, hjeM⟩ := hsupp M e he
      have h1iff : (n = p * M + j * e) ↔ (g₁ M e = n) := by
        simp only [hg₁def]; omega
      have h2iff : (n + j * e = p * M) ↔ (g₂ M e = n) := by
        simp only [hg₂def]; omega
      have h3iff : (n = p * M) ↔ (g₃ M e = n) := by
        simp only [hg₃def]; omega
      rw [if_congr h1iff rfl rfl, if_congr h2iff rfl rfl, if_congr h3iff rfl rfl]
      simp only [hA₁def, hA₂def, hA₃def]
      split_ifs <;> ring
    rw [hS]
    ring

  have hxarm := hasSum_xfun_arm c hnc ht h1j
  have hsum0 : HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst K p c j tateUnivX) * t ^ n)
      (xfun u + ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x)) := by
    rw [funext hdecomp]
    exact hxarm.add ((h1f.add h2f).add h3f)

  have hrow : HasSum (fun M : ℕ => xCoeff u M * (t ^ p) ^ M)
      ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x) := by
    have hcomb := (h1r.add h2r).add h3r
    have hfe : (fun M : ℕ => ((∑ e ∈ M.divisors, A₁ M e * t ^ g₁ M e)
          + ∑ e ∈ M.divisors, A₂ M e * t ^ g₂ M e)
          + ∑ e ∈ M.divisors, A₃ M e * t ^ g₃ M e)
        = fun M : ℕ => xCoeff u M * (t ^ p) ^ M := by
      funext M
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, xCoeff, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨he1, heM, hje, hjeM⟩ := hsupp M e he
      simp only [hA₁def, hA₂def, hA₃def, hg₁def, hg₂def, hg₃def, xDivTerm, hudef]
      have hx1 : (c : K) ^ e * t ^ (p * M + j * e) = ((c : K) * t ^ j) ^ e * (t ^ p) ^ M := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring
      have hx2 : ((c⁻¹ : Kˣ) : K) ^ e * t ^ (p * M - j * e)
          = (((c : K) * t ^ j)⁻¹) ^ e * (t ^ p) ^ M := by
        have h1 : (((c : K) * t ^ j)⁻¹) ^ e = ((c⁻¹ : Kˣ) : K) ^ e * (t ^ (j * e))⁻¹ := by
          rw [mul_inv, mul_pow, ← Units.val_inv_eq_inv_val, inv_pow, ← pow_mul]
        rw [h1, pow_sub₀ t ht0 hje, ← pow_mul]
        ring
      have hx3 : t ^ (p * M) = (t ^ p) ^ M := by rw [← pow_mul]
      calc (e : K) * (c : K) ^ e * t ^ (p * M + j * e)
            + (e : K) * ((c⁻¹ : Kˣ) : K) ^ e * t ^ (p * M - j * e)
            + -(2 * (e : K)) * t ^ (p * M)
          = (e : K) * ((c : K) ^ e * t ^ (p * M + j * e))
            + (e : K) * (((c⁻¹ : Kˣ) : K) ^ e * t ^ (p * M - j * e))
            + -(2 * (e : K)) * t ^ (p * M) := by ring
        _ = (e : K) * (((c : K) * t ^ j) ^ e * (t ^ p) ^ M)
            + (e : K) * ((((c : K) * t ^ j)⁻¹) ^ e * (t ^ p) ^ M)
            + -(2 * (e : K)) * (t ^ p) ^ M := by rw [hx1, hx2, hx3]
        _ = (e : K) * (((c : K) * t ^ j) ^ e + (((c : K) * t ^ j)⁻¹) ^ e - 2) * (t ^ p) ^ M := by
            ring
    rwa [hfe] at hcomb

  have hq0 : t ^ p ≠ 0 := pow_ne_zero p ht0
  have hq1 : ‖t ^ p‖₊ < 1 := by
    rw [nnnorm_pow]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht hp0
  have hu0 : u ≠ 0 := mul_ne_zero (Units.ne_zero c) (pow_ne_zero j ht0)
  have hu1 : ∀ n : ℤ, (t ^ p) ^ n * u ≠ 1 :=
    lattice_mul_slotVal_ne_one c ht0 ht hc h1j hjltp
  have hqu : ‖t ^ p * u‖₊ < 1 := by
    rw [hudef, nnnorm_mul, nnnorm_mul, hnc, nnnorm_pow, nnnorm_pow, one_mul, ← pow_add]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)
  have hqu' : ‖t ^ p * u⁻¹‖₊ < 1 := by
    rw [hudef, mul_inv, nnnorm_mul, nnnorm_mul, nnnorm_inv, nnnorm_inv, hnc, inv_one, one_mul,
      nnnorm_pow, nnnorm_pow]
    have hps : ‖t‖₊ ^ p * (‖t‖₊ ^ j)⁻¹ = ‖t‖₊ ^ (p - j) := by
      rw [pow_sub₀ ‖t‖₊ ht0n hjltp.le]
    rw [hps]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)
  have hqexp := TateCurve.pointX_qExpansion hq0 hq1 hu0 hu1 hqu hqu'

  have hx0 : xCoeff u 0 = (0 : K) := by
    simp [xCoeff, Nat.divisors_zero]
  have hshift : HasSum (fun N : ℕ => xCoeff u (N + 1) * (t ^ p) ^ (N + 1))
      ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x) := by
    refine (hasSum_nat_add_iff (f := fun M : ℕ => xCoeff u M * (t ^ p) ^ M) 1).mpr ?_
    simpa [Finset.sum_range_one, hx0] using hrow
  have hfinal : xfun u + ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x)
      + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x) + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x)
      = pointX (t ^ p) u := by
    rw [hqexp, hshift.tsum_eq]
  rwa [hfinal] at hsum0

theorem hasSum_coeff_slotSubst_tateUnivY_pointY
    (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (c : Kˣ) (hc : c ^ p = 1)
    {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) {j : ℕ} (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst K p c j tateUnivY) * t ^ n)
      (pointY (t ^ p) ((c : K) * t ^ j)) := by
  classical
  have hp0 : p ≠ 0 := by omega
  have hjltp : j < p := j_lt_p hp3 hjp
  have hnc : ‖(c : K)‖₊ = 1 := nnnorm_coe_unit_of_pow_eq_one c hp0 hc
  have hnc' : ‖((c⁻¹ : Kˣ) : K)‖₊ = 1 :=
    nnnorm_coe_unit_of_pow_eq_one c⁻¹ hp0 (inv_pow_eq_one c hc)
  have htR : ‖t‖ < 1 := by exact_mod_cast ht
  have ht0n : ‖t‖₊ ≠ 0 := by simpa [nnnorm_eq_zero] using ht0
  set u : K := (c : K) * t ^ j with hudef
  set A₁ : ℕ → ℕ → K := fun _ e => ((e.choose 2 : ℕ) : K) * (c : K) ^ e with hA₁def
  set A₂ : ℕ → ℕ → K :=
    fun _ e => -((((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e) with hA₂def
  set A₃ : ℕ → ℕ → K := fun _ e => (e : K) with hA₃def
  set g₁ : ℕ → ℕ → ℕ := fun M e => p * M + j * e with hg₁def
  set g₂ : ℕ → ℕ → ℕ := fun M e => p * M - j * e with hg₂def
  set g₃ : ℕ → ℕ → ℕ := fun M _ => p * M with hg₃def
  have hsupp : ∀ M e : ℕ, e ∈ M.divisors →
      1 ≤ e ∧ e ≤ M ∧ j * e ≤ p * M ∧ j * e + M ≤ p * M := by
    intro M e he
    obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (by
      rintro rfl; exact hM0 (zero_dvd_iff.mp hdvd))
    have heM : e ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd
    have h1 : j * e ≤ j * M := Nat.mul_le_mul_left j heM
    have h2 : (j + 1) * M ≤ p * M := Nat.mul_le_mul_right M (by omega)
    have h3 : (j + 1) * M = j * M + M := by ring
    refine ⟨he1, heM, ?_, ?_⟩ <;> omega
  have hnatle : ∀ e : ℕ, ‖(e : K)‖ ≤ 1 := fun e => IsUltrametricDist.norm_natCast_le_one K e
  have hcoe1 : ‖(c : K)‖ = 1 := by rw [← coe_nnnorm, hnc, NNReal.coe_one]
  have hcoe1' : ‖((c⁻¹ : Kˣ) : K)‖ = 1 := by rw [← coe_nnnorm, hnc', NNReal.coe_one]
  have hA₁b : ∀ M e, e ∈ M.divisors → ‖A₁ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₁def]
    rw [norm_mul, norm_pow, hcoe1, one_pow, mul_one]
    exact hnatle _
  have hA₂b : ∀ M e, e ∈ M.divisors → ‖A₂ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₂def]
    rw [norm_neg, norm_mul, norm_pow, hcoe1', one_pow, mul_one]
    exact hnatle _
  have hA₃b : ∀ M e, e ∈ M.divisors → ‖A₃ M e‖ ≤ 1 := by
    intro M e _
    simp only [hA₃def]
    exact hnatle _
  have hMle : ∀ M : ℕ, M ≤ p * M := fun M => Nat.le_mul_of_pos_left M (by omega)
  have hg₁M : ∀ M e, e ∈ M.divisors → M ≤ g₁ M e := by
    intro M e he; have := hMle M; simp only [hg₁def]; omega
  have hg₁e : ∀ M e, e ∈ M.divisors → e ≤ g₁ M e := by
    intro M e he
    have he' := (hsupp M e he).2.1
    have := hMle M
    simp only [hg₁def]; omega
  have hg₂M : ∀ M e, e ∈ M.divisors → M ≤ g₂ M e := by
    intro M e he
    have h := (hsupp M e he).2.2.2
    simp only [hg₂def]; omega
  have hg₂e : ∀ M e, e ∈ M.divisors → e ≤ g₂ M e := by
    intro M e he
    obtain ⟨-, heM, -, h⟩ := hsupp M e he
    simp only [hg₂def]; omega
  have hg₃M : ∀ M e, e ∈ M.divisors → M ≤ g₃ M e := by
    intro M e he; have := hMle M; simp only [hg₃def]; omega
  have hg₃e : ∀ M e, e ∈ M.divisors → e ≤ g₃ M e := by
    intro M e he
    have := (hsupp M e he).2.1; have := hMle M
    simp only [hg₃def]; omega
  obtain ⟨h1g, h1f, h1r⟩ := arm_hasSum_triple hA₁b hg₁M hg₁e htR
  obtain ⟨h2g, h2f, h2r⟩ := arm_hasSum_triple hA₂b hg₂M hg₂e htR
  obtain ⟨h3g, h3f, h3r⟩ := arm_hasSum_triple hA₃b hg₃M hg₃e htR
  have hdecomp : ∀ n : ℕ, PowerSeries.coeff n (slotSubst K p c j tateUnivY) * t ^ n
      = ((if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) * t ^ n
          + ((∑ x ∈ fiberFinset (fun x => g₁ x.1 x.2) n, armFam A₁ g₁ t x)
            + (∑ x ∈ fiberFinset (fun x => g₂ x.1 x.2) n, armFam A₂ g₂ t x)
            + (∑ x ∈ fiberFinset (fun x => g₃ x.1 x.2) n, armFam A₃ g₃ t x))) := by
    intro n
    rw [ModularCurve.coeff_slotSubst_tateUnivY p c j (by omega) hjltp n]
    rw [fiber_sum_eq hg₁M t n, fiber_sum_eq hg₂M t n, fiber_sum_eq hg₃M t n]
    have hS : (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
          ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
            - (if n + j * e = p * M then
                (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0)
            + (if n = p * M then (e : K) else 0)))
        = ((∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₁ M e = n then A₁ M e else 0)
          + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₂ M e = n then A₂ M e else 0)
          + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, if g₃ M e = n then A₃ M e else 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨he1, heM, hje, hjeM⟩ := hsupp M e he
      have h1iff : (n = p * M + j * e) ↔ (g₁ M e = n) := by
        simp only [hg₁def]; omega
      have h2iff : (n + j * e = p * M) ↔ (g₂ M e = n) := by
        simp only [hg₂def]; omega
      have h3iff : (n = p * M) ↔ (g₃ M e = n) := by
        simp only [hg₃def]; omega
      rw [if_congr h1iff rfl rfl, if_congr h2iff rfl rfl, if_congr h3iff rfl rfl]
      simp only [hA₁def, hA₂def, hA₃def]
      split_ifs <;> ring
    rw [hS]
    ring
  have hyarm := hasSum_yfun_arm c hnc ht h1j
  have hsum0 : HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst K p c j tateUnivY) * t ^ n)
      (yfun u + ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x)) := by
    rw [funext hdecomp]
    exact hyarm.add ((h1f.add h2f).add h3f)
  have hrow : HasSum (fun M : ℕ => yCoeff u M * (t ^ p) ^ M)
      ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x) := by
    have hcomb := (h1r.add h2r).add h3r
    have hfe : (fun M : ℕ => ((∑ e ∈ M.divisors, A₁ M e * t ^ g₁ M e)
          + ∑ e ∈ M.divisors, A₂ M e * t ^ g₂ M e)
          + ∑ e ∈ M.divisors, A₃ M e * t ^ g₃ M e)
        = fun M : ℕ => yCoeff u M * (t ^ p) ^ M := by
      funext M
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, yCoeff, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨he1, heM, hje, hjeM⟩ := hsupp M e he
      simp only [hA₁def, hA₂def, hA₃def, hg₁def, hg₂def, hg₃def, yDivTerm, hudef]
      have hx1 : (c : K) ^ e * t ^ (p * M + j * e) = ((c : K) * t ^ j) ^ e * (t ^ p) ^ M := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring
      have hx2 : ((c⁻¹ : Kˣ) : K) ^ e * t ^ (p * M - j * e)
          = (((c : K) * t ^ j)⁻¹) ^ e * (t ^ p) ^ M := by
        have h1 : (((c : K) * t ^ j)⁻¹) ^ e = ((c⁻¹ : Kˣ) : K) ^ e * (t ^ (j * e))⁻¹ := by
          rw [mul_inv, mul_pow, ← Units.val_inv_eq_inv_val, inv_pow, ← pow_mul]
        rw [h1, pow_sub₀ t ht0 hje, ← pow_mul]
        ring
      have hx3 : t ^ (p * M) = (t ^ p) ^ M := by rw [← pow_mul]
      have hch : (((e + 1).choose 2 : ℕ) : K) = ((e.choose 2 : ℕ) : K) + (e : K) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        push_cast
        ring
      calc ((e.choose 2 : ℕ) : K) * (c : K) ^ e * t ^ (p * M + j * e)
            + -((((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e) * t ^ (p * M - j * e)
            + (e : K) * t ^ (p * M)
          = ((e.choose 2 : ℕ) : K) * ((c : K) ^ e * t ^ (p * M + j * e))
            - (((e + 1).choose 2 : ℕ) : K) * (((c⁻¹ : Kˣ) : K) ^ e * t ^ (p * M - j * e))
            + (e : K) * t ^ (p * M) := by ring
        _ = ((e.choose 2 : ℕ) : K) * (((c : K) * t ^ j) ^ e * (t ^ p) ^ M)
            - (((e + 1).choose 2 : ℕ) : K) * ((((c : K) * t ^ j)⁻¹) ^ e * (t ^ p) ^ M)
            + (e : K) * (t ^ p) ^ M := by rw [hx1, hx2, hx3]
        _ = (((e.choose 2 : ℕ) : K) * (((c : K) * t ^ j) ^ e - (((c : K) * t ^ j)⁻¹) ^ e)
            - (e : K) * (((c : K) * t ^ j)⁻¹) ^ e + (e : K)) * (t ^ p) ^ M := by
            rw [hch]
            ring
    rwa [hfe] at hcomb
  have hq0 : t ^ p ≠ 0 := pow_ne_zero p ht0
  have hq1 : ‖t ^ p‖₊ < 1 := by
    rw [nnnorm_pow]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht hp0
  have hu0 : u ≠ 0 := mul_ne_zero (Units.ne_zero c) (pow_ne_zero j ht0)
  have hu1 : ∀ n : ℤ, (t ^ p) ^ n * u ≠ 1 :=
    lattice_mul_slotVal_ne_one c ht0 ht hc h1j hjltp
  have hqu : ‖t ^ p * u‖₊ < 1 := by
    rw [hudef, nnnorm_mul, nnnorm_mul, hnc, nnnorm_pow, nnnorm_pow, one_mul, ← pow_add]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)
  have hqu' : ‖t ^ p * u⁻¹‖₊ < 1 := by
    rw [hudef, mul_inv, nnnorm_mul, nnnorm_mul, nnnorm_inv, nnnorm_inv, hnc, inv_one, one_mul,
      nnnorm_pow, nnnorm_pow]
    have hps : ‖t‖₊ ^ p * (‖t‖₊ ^ j)⁻¹ = ‖t‖₊ ^ (p - j) := by
      rw [pow_sub₀ ‖t‖₊ ht0n hjltp.le]
    rw [hps]
    exact pow_lt_one₀ (zero_le : (0 : ℝ≥0) ≤ ‖t‖₊) ht (by omega)
  have hqexp := TateCurve.pointY_qExpansion hq0 hq1 hu0 hu1 hqu hqu'
  have hy0 : yCoeff u 0 = (0 : K) := by
    simp [yCoeff, Nat.divisors_zero]
  have hshift : HasSum (fun N : ℕ => yCoeff u (N + 1) * (t ^ p) ^ (N + 1))
      ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x) + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x)
        + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x) := by
    refine (hasSum_nat_add_iff (f := fun M : ℕ => yCoeff u M * (t ^ p) ^ M) 1).mpr ?_
    simpa [Finset.sum_range_one, hy0] using hrow
  have hfinal : yfun u + ((∑' x : ℕ × ℕ, armFam A₁ g₁ t x)
      + (∑' x : ℕ × ℕ, armFam A₂ g₂ t x) + ∑' x : ℕ × ℕ, armFam A₃ g₃ t x)
      = pointY (t ^ p) u := by
    rw [hqexp, hshift.tsum_eq]
  rwa [hfinal] at hsum0

end GLT1

end

noncomputable section

open ModularCurve

namespace SlotSeriesTransport

theorem exists_slope_of_cleared {A : Type*} [CommRing A] {d n a₁ a₂ x₁ x₂ x₃ : A}
    (hd : IsUnit d) (hG : n ^ 2 + a₁ * n * d - (a₂ + x₁ + x₂ + x₃) * d ^ 2 = 0) :
    ∃ ℓ : A, ℓ * d = n ∧ ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₂ = x₃ := by
  obtain ⟨u, rfl⟩ := hd
  refine ⟨n * ↑u⁻¹, by rw [mul_assoc, Units.inv_mul, mul_one], ?_⟩
  have key : (n * ↑u⁻¹) ^ 2 + a₁ * (n * ↑u⁻¹) - a₂ - x₁ - x₂ - x₃
      = (n ^ 2 + a₁ * n * ↑u - (a₂ + x₁ + x₂ + x₃) * ↑u ^ 2) * ↑u⁻¹ ^ 2 := by
    have h1 : (↑u : A) * ↑u⁻¹ = 1 := Units.mul_inv u
    linear_combination ((a₂ + x₁ + x₂ + x₃) * (1 + (↑u : A) * ↑u⁻¹) - a₁ * n * ↑u⁻¹) * h1
  rw [← sub_eq_zero, key, hG, zero_mul]

section Naturality

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

private theorem map_ite_zero (P : Prop) [Decidable P] (x : R) :
    φ (if P then x else 0) = if P then φ x else 0 := by
  split_ifs <;> simp

theorem map_slotSubst_tateUnivX (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    PowerSeries.map φ (slotSubst R p c j tateUnivX)
      = slotSubst S p (Units.map (φ : R →* S) c) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivX p c j hj hjp n,
    coeff_slotSubst_tateUnivX p _ j hj hjp n, Units.coe_map_inv, Units.coe_map]
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast, map_ofNat,
    map_ite_zero, MonoidHom.coe_coe]

theorem map_slotSubst_tateUnivY (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    PowerSeries.map φ (slotSubst R p c j tateUnivY)
      = slotSubst S p (Units.map (φ : R →* S) c) j tateUnivY := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivY p c j hj hjp n,
    coeff_slotSubst_tateUnivY p _ j hj hjp n, Units.coe_map_inv, Units.coe_map]
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_natCast,
    map_ite_zero, MonoidHom.coe_coe]

def a4Series (R : Type*) [CommRing R] (p : ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => if p ∣ n then ((PowerSeries.coeff (n / p) tateA4 : ℤ) : R) else 0

theorem coeff_a4Series (R : Type*) [CommRing R] (p n : ℕ) :
    PowerSeries.coeff n (a4Series R p)
      = if p ∣ n then ((PowerSeries.coeff (n / p) tateA4 : ℤ) : R) else 0 := by
  rw [a4Series, PowerSeries.coeff_mk]

theorem map_a4Series (p : ℕ) : PowerSeries.map φ (a4Series R p) = a4Series S p := by
  ext n
  rw [PowerSeries.coeff_map, coeff_a4Series, coeff_a4Series, map_ite_zero, map_intCast]

def tangentSeries (R : Type*) [CommRing R] (p : ℕ) (ξ : Rˣ) (b k m : ℕ) : PowerSeries R :=
  (3 * slotSubst R p (ξ ^ (b * k)) k tateUnivX ^ 2 + a4Series R p
      - slotSubst R p (ξ ^ (b * k)) k tateUnivY) ^ 2
    + (3 * slotSubst R p (ξ ^ (b * k)) k tateUnivX ^ 2 + a4Series R p
        - slotSubst R p (ξ ^ (b * k)) k tateUnivY)
      * (2 * slotSubst R p (ξ ^ (b * k)) k tateUnivY + slotSubst R p (ξ ^ (b * k)) k tateUnivX)
    - (2 * slotSubst R p (ξ ^ (b * k)) k tateUnivX + slotSubst R p (ξ ^ (b * m)) m tateUnivX)
      * (2 * slotSubst R p (ξ ^ (b * k)) k tateUnivY
          + slotSubst R p (ξ ^ (b * k)) k tateUnivX) ^ 2

theorem map_tangentSeries (p : ℕ) (ξ : Rˣ) (b k m : ℕ)
    (h1k : 1 ≤ k) (hkp : k < p) (h1m : 1 ≤ m) (hmp : m < p) :
    PowerSeries.map φ (tangentSeries R p ξ b k m)
      = tangentSeries S p (Units.map (φ : R →* S) ξ) b k m := by
  simp only [tangentSeries, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_slotSubst_tateUnivX φ p _ k h1k hkp, map_slotSubst_tateUnivX φ p _ m h1m hmp,
    map_slotSubst_tateUnivY φ p _ k h1k hkp, map_a4Series φ p]

end Naturality

section Faces

variable (K : Type*) [CommRing K] (p : ℕ) [NeZero p]

theorem tateBase_a₁ : (tateBase K p).a₁ = 1 := by simp [tateBase, tateLaurent, tatePowerSeries]
theorem tateBase_a₂ : (tateBase K p).a₂ = 0 := by simp [tateBase, tateLaurent, tatePowerSeries]
theorem tateBase_a₃ : (tateBase K p).a₃ = 0 := by simp [tateBase, tateLaurent, tatePowerSeries]

theorem qExpand_ofPowerSeries (f : PowerSeries K) :
    qExpand K p (HahnSeries.ofPowerSeries ℤ K f)
      = HahnSeries.ofPowerSeries ℤ K
          (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) f else 0) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hk
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    by_cases hk' : k' < 0
    · rw [if_pos hk', if_pos (mul_neg_of_pos_of_neg hp0 hk')]
    · rw [if_neg hk', if_neg (by nlinarith), PowerSeries.coeff_mk]
      have hnat : ((p : ℤ) * k').natAbs = p * k'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [hnat, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne p))]
  · rw [qExpand_coeff_of_not_dvd (R := K) p _ hk, PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · rw [PowerSeries.coeff_mk, if_neg]
      intro hdvd
      apply hk
      have hk0 : 0 ≤ k := le_of_not_gt hneg
      rw [← Int.natAbs_of_nonneg hk0]
      exact Int.natCast_dvd_natCast.mpr hdvd

theorem tateBase_a₄ : (tateBase K p).a₄ = HahnSeries.ofPowerSeries ℤ K (a4Series K p) := by
  have h : (tateBase K p).a₄ = qExpand K p (laurentOfInt K tateA4) := by
    simp [tateBase, tateLaurent, tatePowerSeries]
  rw [h, laurentOfInt_apply, qExpand_ofPowerSeries]
  congr 1

end Faces

section Evaluation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

def IsBdd (φ : PowerSeries K) : Prop := ∀ n, ‖PowerSeries.coeff n φ‖ ≤ 1

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem IsBdd.neg {φ : PowerSeries K} (h : IsBdd φ) : IsBdd (-φ) := fun n => by
  rw [map_neg, norm_neg]; exact h n

omit [CompleteSpace K] in
theorem IsBdd.add {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) : IsBdd (φ + ψ) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ n) (hψ n))

omit [CompleteSpace K] in
theorem IsBdd.sub {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) : IsBdd (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

omit [CompleteSpace K] in
theorem IsBdd.mul {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) : IsBdd (φ * ψ) := fun n => by
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun kl _ => ?_
  calc ‖PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ‖
      ≤ ‖PowerSeries.coeff kl.1 φ‖ * ‖PowerSeries.coeff kl.2 ψ‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (hφ _) (hψ _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

omit [CompleteSpace K] in
theorem IsBdd.pow {φ : PowerSeries K} (hφ : IsBdd φ) (n : ℕ) : IsBdd (φ ^ n) := by
  induction n with
  | zero =>
    intro k
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih => rw [pow_succ]; exact ih.mul hφ

omit [CompleteSpace K] in
theorem IsBdd.natCast (n : ℕ) : IsBdd (n : PowerSeries K) := fun k => by
  rw [← map_natCast (PowerSeries.C (R := K)) n, PowerSeries.coeff_C]
  split_ifs
  · exact IsUltrametricDist.norm_natCast_le_one K n
  · simp

omit [CompleteSpace K] in
theorem IsBdd.ofNat (n : ℕ) [n.AtLeastTwo] : IsBdd (ofNat(n) : PowerSeries K) := by
  rw [← Nat.cast_ofNat]; exact IsBdd.natCast n

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem IsBdd.summable_norm {φ : PowerSeries K} (hφ : IsBdd φ) {t : K} (ht : ‖t‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n φ * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg t) ht)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg t) n) (hφ n)

omit [IsUltrametricDist K] in
theorem IsBdd.summable {φ : PowerSeries K} (hφ : IsBdd φ) {t : K} (ht : ‖t‖ < 1) :
    Summable fun n => PowerSeries.coeff n φ * t ^ n :=
  (hφ.summable_norm ht).of_norm

def ev (φ : PowerSeries K) (t : K) : K := ∑' n, PowerSeries.coeff n φ * t ^ n

omit [IsUltrametricDist K] in
theorem ev_add {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) {t : K} (ht : ‖t‖ < 1) :
    ev (φ + ψ) t = ev φ t + ev ψ t := by
  rw [ev, ev, ev, ← (hφ.summable ht).tsum_add (hψ.summable ht)]
  exact tsum_congr fun n => by rw [map_add, add_mul]

omit [IsUltrametricDist K] in
theorem ev_sub {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) {t : K} (ht : ‖t‖ < 1) :
    ev (φ - ψ) t = ev φ t - ev ψ t := by
  rw [ev, ev, ev, ← (hφ.summable ht).tsum_sub (hψ.summable ht)]
  exact tsum_congr fun n => by rw [map_sub, sub_mul]

omit [IsUltrametricDist K] in
theorem ev_mul {φ ψ : PowerSeries K} (hφ : IsBdd φ) (hψ : IsBdd ψ) {t : K} (ht : ‖t‖ < 1) :
    ev (φ * ψ) t = ev φ t * ev ψ t := by
  rw [ev, ev, ev, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hφ.summable_norm ht)
    (hψ.summable_norm ht)]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

omit [IsUltrametricDist K] in
theorem ev_pow_two {φ : PowerSeries K} (hφ : IsBdd φ) {t : K} (ht : ‖t‖ < 1) :
    ev (φ ^ 2) t = ev φ t ^ 2 := by
  rw [pow_two, pow_two, ev_mul hφ hφ ht]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ev_C (r : K) (t : K) : ev (PowerSeries.C r) t = r := by
  rw [ev, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [PowerSeries.coeff_C, if_neg hn, zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ev_natCast (n : ℕ) (t : K) : ev (n : PowerSeries K) t = n := by
  rw [← map_natCast (PowerSeries.C (R := K)) n, ev_C]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ev_ofNat (n : ℕ) [n.AtLeastTwo] (t : K) : ev (ofNat(n) : PowerSeries K) t = ofNat(n) := by
  rw [← Nat.cast_ofNat, ev_natCast, Nat.cast_ofNat]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem hasSum_iff_ev_eq {φ : PowerSeries K} {t a : K} (hs : Summable fun n => PowerSeries.coeff n φ * t ^ n) :
    HasSum (fun n => PowerSeries.coeff n φ * t ^ n) a ↔ ev φ t = a :=
  ⟨fun h => h.tsum_eq, fun h => h ▸ hs.hasSum⟩

theorem eq_zero_of_forall_ev_eq_zero {φ : PowerSeries K} (hφ : IsBdd φ)
    (h : ∀ t : K, t ≠ 0 → ‖t‖ < 1 → ev φ t = 0) : φ = 0 := by
  obtain ⟨q₀, hq₀0, hq₀1⟩ := NormedField.exists_norm_lt_one K
  have hmain := TateCurve.coeff_eq_of_forall_tsum_eq (a := fun n => PowerSeries.coeff n φ)
    (b := fun _ => 0) (q₀ := q₀) (norm_pos_iff.mp hq₀0) hq₀1
    (fun q _ hq => hφ.summable (lt_of_le_of_lt hq hq₀1))
    (fun q _ _ => by simp)
    (fun q hq hqle => by
      have := h q hq (lt_of_le_of_lt hqle hq₀1)
      rw [ev] at this
      rw [this]
      simp)
  ext n
  rw [map_zero]; exact hmain n

end Evaluation

section Bounded

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
theorem norm_units_pow_le {c : Kˣ} (hc : ‖(c : K)‖ ≤ 1) (e : ℕ) : ‖(c : K) ^ e‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc

theorem isBdd_slotSubst_tateUnivX (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hc : ‖(c : K)‖ ≤ 1) (hc' : ‖((c⁻¹ : Kˣ) : K)‖ ≤ 1) :
    IsBdd (slotSubst K p c j tateUnivX) := by
  intro n
  rw [coeff_slotSubst_tateUnivX p c j hj hjp n]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · split_ifs
    · exact (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
        (norm_nonneg _) (norm_units_pow_le hc _))
    · simp
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun M _ => ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
    refine (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
      (norm_nonneg _) ?_)
    have h2 : ‖(if n = p * M then (2 : K) else 0)‖ ≤ 1 := by
      split_ifs
      · exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
      · simp
    have hA : ‖(if n = p * M + j * e then (c : K) ^ e else 0)‖ ≤ 1 := by
      split_ifs
      · exact norm_units_pow_le hc e
      · simp
    have hB : ‖(if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)‖ ≤ 1 := by
      split_ifs
      · exact norm_units_pow_le hc' e
      · simp
    exact (norm_sub_le_max' _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA hB)) h2)

theorem isBdd_slotSubst_tateUnivY (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hc : ‖(c : K)‖ ≤ 1) (hc' : ‖((c⁻¹ : Kˣ) : K)‖ ≤ 1) :
    IsBdd (slotSubst K p c j tateUnivY) := by
  intro n
  rw [coeff_slotSubst_tateUnivY p c j hj hjp n]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · split_ifs
    · exact (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
        (norm_nonneg _) (norm_units_pow_le hc _))
    · simp
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun M _ => ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
    have hA : ‖(if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)‖ ≤ 1 := by
      split_ifs
      · exact (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
          (norm_nonneg _) (norm_units_pow_le hc e))
      · simp
    have hB : ‖(if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e
        else 0)‖ ≤ 1 := by
      split_ifs
      · exact (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
          (norm_nonneg _) (norm_units_pow_le hc' e))
      · simp
    have hC : ‖(if n = p * M then (e : K) else 0)‖ ≤ 1 := by
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one K e
      · simp
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_sub_le_max' _ _).trans (max_le hA hB)) hC)

theorem isBdd_a4Series (p : ℕ) : IsBdd (a4Series K p) := fun n => by
  rw [coeff_a4Series]
  split_ifs
  · exact IsUltrametricDist.norm_intCast_le_one K _
  · simp

end Bounded

section Universal

open Polynomial

variable (p : ℕ) [Fact p.Prime]

def cycPoly : ℤ[X] := X ^ p - C 1

theorem cycPoly_monic : (cycPoly p).Monic :=
  Polynomial.monic_X_pow_sub_C (1 : ℤ) (Fact.out : p.Prime).ne_zero

omit [Fact p.Prime] in
theorem natDegree_cycPoly : (cycPoly p).natDegree = p := by
  rw [cycPoly, Polynomial.natDegree_X_pow_sub_C]

theorem cycPoly_ne_one : cycPoly p ≠ 1 := by
  intro h
  have h1 := congrArg Polynomial.natDegree h
  rw [natDegree_cycPoly, Polynomial.natDegree_one] at h1
  exact (Fact.out : p.Prime).ne_zero h1

abbrev UnivRing : Type := AdjoinRoot (cycPoly p)

omit [Fact p.Prime] in
theorem root_pow_eq_one : (AdjoinRoot.root (cycPoly p)) ^ p = 1 := by
  have h := AdjoinRoot.eval₂_root (cycPoly p)
  rw [cycPoly, eval₂_sub, eval₂_X_pow, eval₂_C, map_one, sub_eq_zero] at h
  exact h

def rootUnit : (UnivRing p)ˣ where
  val := AdjoinRoot.root (cycPoly p)
  inv := AdjoinRoot.root (cycPoly p) ^ (p - 1)
  val_inv := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, root_pow_eq_one]
  inv_val := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, root_pow_eq_one]

@[scoped simp] theorem val_rootUnit : (rootUnit p : UnivRing p) = AdjoinRoot.root (cycPoly p) := rfl

variable {p}

def liftAt {S : Type*} [CommRing S] (ζ : Sˣ) (hζ : ζ ^ p = 1) : UnivRing p →+* S :=
  AdjoinRoot.lift (Int.castRingHom S) (ζ : S) (by
    rw [cycPoly, eval₂_sub, eval₂_X_pow, eval₂_C, map_one, ← Units.val_pow_eq_pow_val, hζ,
      Units.val_one, sub_self])

omit [Fact p.Prime] in
theorem liftAt_root {S : Type*} [CommRing S] (ζ : Sˣ) (hζ : ζ ^ p = 1) :
    liftAt ζ hζ (AdjoinRoot.root (cycPoly p)) = ζ := by
  rw [liftAt, AdjoinRoot.lift_root]

theorem map_liftAt_rootUnit {S : Type*} [CommRing S] (ζ : Sˣ) (hζ : ζ ^ p = 1) :
    Units.map (liftAt ζ hζ : UnivRing p →* S) (rootUnit p) = ζ := by
  ext
  rw [Units.coe_map, MonoidHom.coe_coe, val_rootUnit, liftAt_root]

theorem eq_zero_of_forall_liftAt_pow {F : Type*} [Field F] [CharZero F] (ζu : Fˣ)
    (hζ : IsPrimitiveRoot (ζu : F) p) (hζp : ∀ c : ℕ, (ζu ^ c) ^ p = 1) (g : UnivRing p)
    (h : ∀ c : ℕ, c < p → liftAt (ζu ^ c) (hζp c) g = 0) : g = 0 := by
  set P : ℤ[X] := AdjoinRoot.modByMonicHom (cycPoly_monic p) g with hP
  have hg : AdjoinRoot.mk (cycPoly p) P = g := AdjoinRoot.mk_leftInverse (cycPoly_monic p) g
  have hdeg : P.natDegree < p := by
    obtain ⟨g₀, rfl⟩ := AdjoinRoot.mk_surjective g
    rw [hP, AdjoinRoot.modByMonicHom_mk]
    have := Polynomial.natDegree_modByMonic_lt g₀ (cycPoly_monic p) (cycPoly_ne_one p)
    rwa [natDegree_cycPoly] at this
  have hQ : P.map (Int.castRingHom F) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (ι := Fin p)
      (f := fun c => ((ζu : F)) ^ (c : ℕ)) ?_ ?_ ?_
    · intro c d hcd
      exact Fin.ext (hζ.pow_inj c.isLt d.isLt hcd)
    · intro c
      have h1 := h c c.isLt
      rw [← hg, liftAt, AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map] at h1
      simpa [Units.val_pow_eq_pow_val] using h1
    · rw [Fintype.card_fin]
      exact (Polynomial.natDegree_map_le).trans_lt hdeg
  have hP0 : P = 0 :=
    Polynomial.map_injective (Int.castRingHom F) Int.cast_injective (by rw [hQ, Polynomial.map_zero])
  rw [← hg, hP0, map_zero]

theorem powerSeries_eq_zero_of_forall_liftAt_pow {F : Type*} [Field F] [CharZero F] (ζu : Fˣ)
    (hζ : IsPrimitiveRoot (ζu : F) p) (hζp : ∀ c : ℕ, (ζu ^ c) ^ p = 1)
    (Φ : PowerSeries (UnivRing p))
    (h : ∀ c : ℕ, c < p → PowerSeries.map (liftAt (ζu ^ c) (hζp c)) Φ = 0) : Φ = 0 := by
  ext n
  rw [map_zero]
  refine eq_zero_of_forall_liftAt_pow ζu hζ hζp _ fun c hc => ?_
  have := congrArg (PowerSeries.coeff n) (h c hc)
  rwa [PowerSeries.coeff_map, map_zero] at this

omit [Fact p.Prime] in
theorem tangentSeries_pow (R : Type*) [CommRing R] (ζ : Rˣ) (c b k m : ℕ) :
    tangentSeries R p (ζ ^ c) b k m = tangentSeries R p ζ (c * b) k m := by
  simp only [tangentSeries, ← pow_mul, mul_assoc]

theorem tangentSeries_eq_zero_of_field {F : Type*} [Field F] [CharZero F] (ζu : Fˣ)
    (hζ : IsPrimitiveRoot (ζu : F) p) (k m : ℕ)
    (h1k : 1 ≤ k) (hkp : k < p) (h1m : 1 ≤ m) (hmp : m < p)
    (hF : ∀ b : ℕ, tangentSeries F p ζu b k m = 0)
    (K : Type*) [CommRing K] (ζ : Kˣ) (hζK : ζ ^ p = 1) (b : ℕ) :
    tangentSeries K p ζ b k m = 0 := by
  have hζp : ∀ c : ℕ, (ζu ^ c) ^ p = 1 := fun c => by
    rw [← pow_mul, mul_comm, pow_mul]
    have : ζu ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
    rw [this, one_pow]
  have huniv : tangentSeries (UnivRing p) p (rootUnit p) b k m = 0 := by
    refine powerSeries_eq_zero_of_forall_liftAt_pow ζu hζ hζp _ fun c hc => ?_
    rw [map_tangentSeries _ p _ b k m h1k hkp h1m hmp, map_liftAt_rootUnit, tangentSeries_pow]
    exact hF _
  have := congrArg (PowerSeries.map (liftAt ζ hζK)) huniv
  rwa [map_tangentSeries _ p _ b k m h1k hkp h1m hmp, map_liftAt_rootUnit, map_zero] at this

end Universal

section Vanishing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_coe_units_eq_one_of_pow_eq_one (c : Kˣ) {p : ℕ} (hp : p ≠ 0) (hc : c ^ p = 1) :
    ‖(c : K)‖ = 1 := by
  have h1 : ‖(c : K)‖ ^ p = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp).mp h1

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_coe_units_pow_le_one (c : Kˣ) {p : ℕ} (hp : p ≠ 0) (hc : c ^ p = 1) (e : ℕ) :
    ‖((c ^ e : Kˣ) : K)‖ ≤ 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow, norm_coe_units_eq_one_of_pow_eq_one c hp hc, one_pow]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_coe_units_pow_inv_le_one (c : Kˣ) {p : ℕ} (hp : p ≠ 0) (hc : c ^ p = 1) (e : ℕ) :
    ‖(((c ^ e)⁻¹ : Kˣ) : K)‖ ≤ 1 := by
  rw [Units.val_inv_eq_inv_val, norm_inv, Units.val_pow_eq_pow_val, norm_pow,
    norm_coe_units_eq_one_of_pow_eq_one c hp hc, one_pow, inv_one]

omit [CompleteSpace K] in
theorem isBdd_slotX (p : ℕ) [Fact p.Prime] (ζu : Kˣ) (hζu : ζu ^ p = 1) (e k : ℕ)
    (h1k : 1 ≤ k) (hkp : k < p) : IsBdd (slotSubst K p (ζu ^ e) k tateUnivX) :=
  isBdd_slotSubst_tateUnivX p _ k h1k hkp
    (norm_coe_units_pow_le_one ζu (Fact.out : p.Prime).ne_zero hζu _)
    (norm_coe_units_pow_inv_le_one ζu (Fact.out : p.Prime).ne_zero hζu _)

omit [CompleteSpace K] in
theorem isBdd_slotY (p : ℕ) [Fact p.Prime] (ζu : Kˣ) (hζu : ζu ^ p = 1) (e k : ℕ)
    (h1k : 1 ≤ k) (hkp : k < p) : IsBdd (slotSubst K p (ζu ^ e) k tateUnivY) :=
  isBdd_slotSubst_tateUnivY p _ k h1k hkp
    (norm_coe_units_pow_le_one ζu (Fact.out : p.Prime).ne_zero hζu _)
    (norm_coe_units_pow_inv_le_one ζu (Fact.out : p.Prime).ne_zero hζu _)

theorem tangentSeries_eq_zero_of_ties (p : ℕ) [Fact p.Prime] (ζu : Kˣ) (hζu : ζu ^ p = 1)
    (b k m : ℕ) (h1k : 1 ≤ k) (hkp : k < p) (h1m : 1 ≤ m) (hmp : m < p)
    (xk xm yk a4 : K → K)
    (hXk : ∀ t : K, t ≠ 0 → ‖t‖ < 1 → HasSum
      (fun n : ℕ => PowerSeries.coeff n (slotSubst K p (ζu ^ (b * k)) k tateUnivX) * t ^ n) (xk t))
    (hXm : ∀ t : K, t ≠ 0 → ‖t‖ < 1 → HasSum
      (fun n : ℕ => PowerSeries.coeff n (slotSubst K p (ζu ^ (b * m)) m tateUnivX) * t ^ n) (xm t))
    (hYk : ∀ t : K, t ≠ 0 → ‖t‖ < 1 → HasSum
      (fun n : ℕ => PowerSeries.coeff n (slotSubst K p (ζu ^ (b * k)) k tateUnivY) * t ^ n) (yk t))
    (hA4 : ∀ t : K, t ≠ 0 → ‖t‖ < 1 →
      HasSum (fun n : ℕ => PowerSeries.coeff n (a4Series K p) * t ^ n) (a4 t))
    (hG : ∀ t : K, t ≠ 0 → ‖t‖ < 1 →
      (3 * xk t ^ 2 + a4 t - yk t) ^ 2
        + (3 * xk t ^ 2 + a4 t - yk t) * (2 * yk t + xk t)
        - (2 * xk t + xm t) * (2 * yk t + xk t) ^ 2 = 0) :
    tangentSeries K p ζu b k m = 0 := by
  set Xk := slotSubst K p (ζu ^ (b * k)) k tateUnivX with hXk'
  set Xm := slotSubst K p (ζu ^ (b * m)) m tateUnivX with hXm'
  set Yk := slotSubst K p (ζu ^ (b * k)) k tateUnivY with hYk'
  have bXk : IsBdd Xk := isBdd_slotX p ζu hζu _ k h1k hkp
  have bXm : IsBdd Xm := isBdd_slotX p ζu hζu _ m h1m hmp
  have bYk : IsBdd Yk := isBdd_slotY p ζu hζu _ k h1k hkp
  have bA4 : IsBdd (a4Series K p) := isBdd_a4Series p
  have b3 : IsBdd (3 : PowerSeries K) := IsBdd.ofNat 3
  have b2 : IsBdd (2 : PowerSeries K) := IsBdd.ofNat 2
  have bN : IsBdd (3 * Xk ^ 2 + a4Series K p - Yk) := ((b3.mul (bXk.pow 2)).add bA4).sub bYk
  have bD : IsBdd (2 * Yk + Xk) := (b2.mul bYk).add bXk
  have bC : IsBdd (2 * Xk + Xm) := (b2.mul bXk).add bXm
  refine eq_zero_of_forall_ev_eq_zero
    (((bN.pow 2).add (bN.mul bD)).sub (bC.mul (bD.pow 2))) fun t ht0 ht => ?_
  have eXk : ev Xk t = xk t := (hXk t ht0 ht).tsum_eq
  have eXm : ev Xm t = xm t := (hXm t ht0 ht).tsum_eq
  have eYk : ev Yk t = yk t := (hYk t ht0 ht).tsum_eq
  have eA4 : ev (a4Series K p) t = a4 t := (hA4 t ht0 ht).tsum_eq
  show ev (tangentSeries K p ζu b k m) t = 0
  rw [tangentSeries, ← hXk', ← hXm', ← hYk',
    ev_sub ((bN.pow 2).add (bN.mul bD)) (bC.mul (bD.pow 2)) ht,
    ev_add (bN.pow 2) (bN.mul bD) ht, ev_pow_two bN ht, ev_mul bN bD ht, ev_mul bC (bD.pow 2) ht,
    ev_pow_two bD ht, ev_sub ((b3.mul (bXk.pow 2)).add bA4) bYk ht,
    ev_add (b3.mul (bXk.pow 2)) bA4 ht, ev_mul b3 (bXk.pow 2) ht, ev_pow_two bXk ht,
    ev_add (b2.mul bYk) bXk ht, ev_mul b2 bYk ht, ev_add (b2.mul bXk) bXm ht, ev_mul b2 bXk ht,
    ev_ofNat, ev_ofNat, eXk, eXm, eYk, eA4]
  exact hG t ht0 ht

end Vanishing

section KGrain

variable (K : Type*) [CommRing K] (p : ℕ) [NeZero p]

theorem tangent_identity_of_tangentSeries_eq_zero (ζ : Kˣ) (b k m : ℕ)
    (h : tangentSeries K p ζ b k m = 0) :
    (3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2 + 2 * (tateBase K p).a₂
        * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₄
        - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2) ^ 2
      + (tateBase K p).a₁ * (3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2
          + 2 * (tateBase K p).a₂ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₄
          - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2)
        * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)
      - ((tateBase K p).a₂ + (nonToricPoint K p (ζ ^ (b * k)) k).1
          + (nonToricPoint K p (ζ ^ (b * k)) k).1 + (nonToricPoint K p (ζ ^ (b * m)) m).1)
        * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) ^ 2
      = 0 := by
  have := congrArg (HahnSeries.ofPowerSeries ℤ K) h
  rw [tangentSeries, map_zero] at this
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at this
  simp only [nonToricPoint_fst, nonToricPoint_snd, tateBase_a₁, tateBase_a₂, tateBase_a₃,
    tateBase_a₄, one_mul, mul_zero, zero_mul, zero_add, add_zero]
  rw [← this]
  ring

end KGrain

section TieA4

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.GLT1"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

def a4Fam (Q : K) (x : ℕ × ℕ) : K :=
  if x.1 = 0 ∨ x.2 = 0 then 0 else -(((5 * x.1 ^ 3 : ℕ) : K) * Q ^ (x.1 * x.2))

omit [CompleteSpace K] in
theorem norm_a4Fam_le {Q : K} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1) (x : ℕ × ℕ) :
    ‖a4Fam Q x‖ ≤ ‖Q‖⁻¹ * (‖Q‖ ^ x.1 * ‖Q‖ ^ x.2) := by
  have hQpos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  unfold a4Fam
  split_ifs with h
  · rw [norm_zero]; positivity
  · push Not at h
    obtain ⟨h1, h2⟩ := h
    have hv : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.mpr h1
    have hu : 1 ≤ x.2 := Nat.one_le_iff_ne_zero.mpr h2
    rw [norm_neg, norm_mul, norm_pow]
    have hc : ‖((5 * x.1 ^ 3 : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
    have hexp : x.1 + x.2 ≤ x.1 * x.2 + 1 := by nlinarith
    calc ‖((5 * x.1 ^ 3 : ℕ) : K)‖ * ‖Q‖ ^ (x.1 * x.2)
        ≤ 1 * ‖Q‖ ^ (x.1 * x.2) := by gcongr
      _ = ‖Q‖ ^ (x.1 * x.2) := one_mul _
      _ ≤ ‖Q‖ ^ (x.1 + x.2 - 1) :=
          pow_le_pow_of_le_one hQpos.le hQ1.le (by omega)
      _ = ‖Q‖⁻¹ * (‖Q‖ ^ x.1 * ‖Q‖ ^ x.2) := by
          rw [← pow_add, mul_comm, ← div_eq_mul_inv, eq_div_iff hQpos.ne', ← pow_succ,
            Nat.sub_add_cancel (by omega)]

theorem summable_a4Fam {Q : K} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1) : Summable (a4Fam Q) := by
  refine Summable.of_norm_bounded ?_ (norm_a4Fam_le hQ0 hQ1)
  refine Summable.mul_left _ ?_
  exact Summable.mul_of_nonneg (summable_geometric_of_lt_one (norm_nonneg _) hQ1)
    (summable_geometric_of_lt_one (norm_nonneg _) hQ1) (fun _ => by positivity)
    (fun _ => by positivity)

omit [CompleteSpace K] in

theorem hasSum_a4Fam_row {Q : K} (hQ1 : ‖Q‖ < 1) (v : ℕ) :
    HasSum (fun u : ℕ => a4Fam Q (v, u)) (-(term (fun n => 5 * n ^ 3) Q v)) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have h0 : term (fun n => 5 * n ^ 3) Q 0 = 0 := term_zero _ _
    have hf : (fun u : ℕ => a4Fam Q (0, u)) = fun _ => 0 := by
      funext u; simp [a4Fam]
    rw [h0, neg_zero, hf]
    exact hasSum_zero
  · have hQv : ‖Q ^ v‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hQ1 hv.ne'
    have hgeo := hasSum_geometric_of_norm_lt_one hQv

    have h1 : HasSum (fun u : ℕ => -(((5 * v ^ 3 : ℕ) : K)) * Q ^ v * (Q ^ v) ^ u)
        (-(((5 * v ^ 3 : ℕ) : K)) * Q ^ v * (1 - Q ^ v)⁻¹) := hgeo.mul_left _
    have h2 : HasSum (fun u : ℕ => a4Fam Q (v, u + 1))
        (-(term (fun n => 5 * n ^ 3) Q v) - ∑ i ∈ Finset.range 1, a4Fam Q (v, i)) := by
      have hz : ∑ i ∈ Finset.range 1, a4Fam Q (v, i) = 0 := by simp [a4Fam]
      rw [hz, sub_zero]
      have hval : -(term (fun n => 5 * n ^ 3) Q v)
          = -(((5 * v ^ 3 : ℕ) : K)) * Q ^ v * (1 - Q ^ v)⁻¹ := by
        rw [term, div_eq_mul_inv]; ring
      rw [hval]
      refine h1.congr_fun fun u => ?_
      have hv0 : v ≠ 0 := hv.ne'
      simp only [a4Fam, hv0, Nat.succ_ne_zero, or_self, if_false]
      rw [pow_mul, pow_succ]; ring
    exact (hasSum_nat_add_iff' 1).mp h2

theorem hasSum_neg_term_a₄ {Q : K} (hQ1 : ‖Q‖₊ < 1) :
    HasSum (fun v : ℕ => -(term (fun n => 5 * n ^ 3) Q v)) (a₄ Q) := by
  rw [a₄, coeffSum]
  exact (summable_term _ hQ1).hasSum.neg

theorem hasSum_a4Fam {Q : K} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1) : HasSum (a4Fam Q) (a₄ Q) := by
  obtain ⟨S, hS⟩ := summable_a4Fam hQ0 hQ1
  have hrows := hS.prod_fiberwise (fun v => hasSum_a4Fam_row hQ1 v)
  have hQ1' : ‖Q‖₊ < 1 := by exact_mod_cast hQ1
  have hSa : S = a₄ Q := hrows.unique (hasSum_neg_term_a₄ hQ1')
  rwa [hSa] at hS

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem fiber_sum_a4Fam (Q : K) (N : ℕ) :
    ((PowerSeries.coeff N tateA4 : ℤ) : K) * Q ^ N
      = ∑ x ∈ fiberFinset (fun x : ℕ × ℕ => x.1 * x.2) N, a4Fam Q x := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [coeff_zero_tateA4, Int.cast_zero, zero_mul]
    have hf : fiberFinset (fun x : ℕ × ℕ => x.1 * x.2) 0 = {(0, 0)} := by
      ext ⟨u, v⟩
      simp only [fiberFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        zero_add, Nat.lt_one_iff, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl⟩
    rw [hf, Finset.sum_singleton]
    simp [a4Fam]
  · have hfib : fiberFinset (fun x : ℕ × ℕ => x.1 * x.2) N = N.divisorsAntidiagonal := by
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hN.ne' le_rfl]
      ext ⟨u, v⟩
      simp only [fiberFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨-, huv⟩
        have hu : 0 < u := Nat.pos_of_ne_zero fun h => by subst h; simp at huv; omega
        have hv : 0 < v := Nat.pos_of_ne_zero fun h => by subst h; simp at huv; omega
        refine ⟨⟨⟨hu, ?_⟩, ⟨hv, ?_⟩⟩, huv⟩
        · rw [← huv]; exact Nat.le_mul_of_pos_right u hv
        · rw [← huv]; exact Nat.le_mul_of_pos_left v hu
      · rintro ⟨⟨⟨hu, huN⟩, ⟨hv, hvN⟩⟩, huv⟩
        exact ⟨⟨by omega, by omega⟩, huv⟩
    rw [hfib, Nat.sum_divisorsAntidiagonal (fun u v => a4Fam Q (u, v)), coeff_tateA4,
      Int.cast_neg, Int.cast_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hq0 : N / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hN hdvd) (Nat.pos_of_ne_zero hd0))
    simp only [a4Fam, hd0, hq0, or_self, if_false, Nat.mul_div_cancel' hdvd]
    push_cast
    ring

theorem hasSum_coeff_tateA4_a₄ {Q : K} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ < 1) :
    HasSum (fun N : ℕ => ((PowerSeries.coeff N tateA4 : ℤ) : K) * Q ^ N) (a₄ Q) := by
  refine hasSum_of_fiber_sum (fam := a4Fam Q) (g := fun x : ℕ × ℕ => x.1 * x.2) ?_
    (hasSum_a4Fam hQ0 hQ1) _ (fiber_sum_a4Fam Q)
  intro x hx
  unfold a4Fam at hx
  split_ifs at hx with h
  · exact absurd rfl hx
  · push Not at h
    exact ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h.2),
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h.1)⟩

theorem hasSum_coeff_a4Series_a₄ (p : ℕ) [Fact p.Prime] {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (a4Series K p) * t ^ n) (a₄ (t ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have ht' : ‖t‖ < 1 := by exact_mod_cast ht
  have hQ0 : t ^ p ≠ 0 := pow_ne_zero _ ht0
  have hQ1 : ‖t ^ p‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) ht' hp
  have hmain := hasSum_coeff_tateA4_a₄ hQ0 hQ1
  have hinj : Function.Injective (fun N : ℕ => p * N) := fun a b h => Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero hp) h
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    rw [a4Series, PowerSeries.coeff_mk, if_neg, zero_mul]
    rintro ⟨N, rfl⟩
    exact hn ⟨N, rfl⟩
  · refine hmain.congr_fun fun N => ?_
    simp only [Function.comp_apply, a4Series, PowerSeries.coeff_mk]
    rw [if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), pow_mul]

end TieA4

section Main

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun"

theorem exists_slope_of_cleared₂ {A : Type*} [CommRing A] {d n a₁ a₂ x₁ x₃ : A}
    (hd : IsUnit d) (hG : n ^ 2 + a₁ * n * d - (a₂ + x₁ + x₁ + x₃) * d ^ 2 = 0) :
    ∃ ℓ : A, ℓ * d = n ∧ ℓ ^ 2 + a₁ * ℓ - a₂ - 2 * x₁ = x₃ := by
  obtain ⟨ℓ, h1, h2⟩ := exists_slope_of_cleared hd hG
  exact ⟨ℓ, h1, by rw [← h2]; ring⟩

theorem units_pow_pow_eq_one {M : Type*} [CommMonoid M] {ζu : M} {p : ℕ} (h : ζu ^ p = 1)
    (e : ℕ) : (ζu ^ e) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [CharZero F]

theorem tangent_of_pointTies (p : ℕ) [Fact p.Prime] (ζu : Fˣ) (hζ : IsPrimitiveRoot (ζu : F) p)
    (hX : ∀ (c : Fˣ), c ^ p = 1 → ∀ {t : F}, t ≠ 0 → ‖t‖₊ < 1 → ∀ {j : ℕ}, 1 ≤ j → j ≤ p / 2 →
      HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst F p c j tateUnivX) * t ^ n)
        (pointX (t ^ p) ((c : F) * t ^ j)))
    (hY : ∀ (c : Fˣ), c ^ p = 1 → ∀ {t : F}, t ≠ 0 → ‖t‖₊ < 1 → ∀ {j : ℕ}, 1 ≤ j → j ≤ p / 2 →
      HasSum (fun n : ℕ => PowerSeries.coeff n (slotSubst F p c j tateUnivY) * t ^ n)
        (pointY (t ^ p) ((c : F) * t ^ j)))
    (k m : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) (h1m : 1 ≤ m) (hmp : m ≤ p / 2)
    (hG : ∀ b : ℕ, ∀ t : F, t ≠ 0 → ‖t‖₊ < 1 →
      (3 * pointX (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k) ^ 2 + a₄ (t ^ p)
          - pointY (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k)) ^ 2
        + (3 * pointX (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k) ^ 2 + a₄ (t ^ p)
            - pointY (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k))
          * (2 * pointY (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k)
            + pointX (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k))
        - (2 * pointX (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k)
            + pointX (t ^ p) (((ζu ^ (b * m) : Fˣ) : F) * t ^ m))
          * (2 * pointY (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k)
            + pointX (t ^ p) (((ζu ^ (b * k) : Fˣ) : F) * t ^ k)) ^ 2 = 0)
    (K : Type*) [CommRing K] [NeZero p] (ζ : Kˣ) (hζK : ζ ^ p = 1) (b : ℕ)
    (hunit : IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
        + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)) :
    IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
        + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) ∧
    ∃ ℓ : LaurentSeries K,
      ℓ * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)
        = 3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2
          + 2 * (tateBase K p).a₂ * (nonToricPoint K p (ζ ^ (b * k)) k).1
          + (tateBase K p).a₄ - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2 ∧
      ℓ ^ 2 + (tateBase K p).a₁ * ℓ - (tateBase K p).a₂
          - 2 * (nonToricPoint K p (ζ ^ (b * k)) k).1
        = (nonToricPoint K p (ζ ^ (b * m)) m).1 := by
  have hζu : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  have hp2 : p / 2 < p := Nat.div_lt_self (Fact.out : p.Prime).pos one_lt_two
  have hlt : ∀ {t : F}, ‖t‖ < 1 → ‖t‖₊ < 1 := fun ht => by exact_mod_cast ht
  have hF : ∀ b' : ℕ, tangentSeries F p ζu b' k m = 0 := fun b' =>
    tangentSeries_eq_zero_of_ties p ζu hζu b' k m h1k (hkp.trans_lt hp2) h1m (hmp.trans_lt hp2)
      (fun t => pointX (t ^ p) (((ζu ^ (b' * k) : Fˣ) : F) * t ^ k))
      (fun t => pointX (t ^ p) (((ζu ^ (b' * m) : Fˣ) : F) * t ^ m))
      (fun t => pointY (t ^ p) (((ζu ^ (b' * k) : Fˣ) : F) * t ^ k))
      (fun t => a₄ (t ^ p))
      (fun t ht0 ht => hX _ (units_pow_pow_eq_one hζu _) ht0 (hlt ht) h1k hkp)
      (fun t ht0 ht => hX _ (units_pow_pow_eq_one hζu _) ht0 (hlt ht) h1m hmp)
      (fun t ht0 ht => hY _ (units_pow_pow_eq_one hζu _) ht0 (hlt ht) h1k hkp)
      (fun t ht0 ht => hasSum_coeff_a4Series_a₄ p ht0 (hlt ht))
      (fun t ht0 ht => hG b' t ht0 (hlt ht))
  have hK : tangentSeries K p ζ b k m = 0 :=
    tangentSeries_eq_zero_of_field ζu hζ k m h1k (hkp.trans_lt hp2) h1m (hmp.trans_lt hp2) hF K ζ
      hζK b
  exact ⟨hunit, exists_slope_of_cleared₂ hunit
    (tangent_identity_of_tangentSeries_eq_zero K p ζ b k m hK)⟩

end Main

end SlotSeriesTransport
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport"

noncomputable section

namespace SlotSeriesTransport

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun WeierstrassCurve.Affine"

open scoped NNReal

section PointSum

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K] [IsAlgClosed K]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] in
theorem nnnorm_tpow_lt_one {t : K} (ht : ‖t‖₊ < 1) {p : ℕ} (hp : p ≠ 0) : ‖t ^ p‖₊ < 1 := by
  rw [nnnorm_pow]; exact pow_lt_one₀ (by positivity) ht hp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] in
theorem slotParam_ne_zero (ζu : Kˣ) {t : K} (ht0 : t ≠ 0) (e k : ℕ) :
    (ζu : K) ^ e * t ^ k ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ ζu.ne_zero) (pow_ne_zero _ ht0)

omit [IsAlgClosed K] in

theorem slotParam_offLattice (p : ℕ) [Fact p.Prime] (ζu : Kˣ) (hζ : IsPrimitiveRoot (ζu : K) p)
    {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) (e k : ℕ) (h1k : 1 ≤ k) (hkp : k < p) :
    OffLattice (t ^ p) ((ζu : K) ^ e * t ^ k) := by
  have hp : p.Prime := Fact.out
  have h := tateParam_offLattice (ζ := (ζu : K)) (t := t) (q := t ^ p) (pow_ne_zero _ ht0)
    (nnnorm_tpow_lt_one ht hp.ne_zero) hζ rfl (Nat.mod_lt e hp.pos) hkp (fun h => by omega)
  rwa [← zeta_pow_mod hζ.pow_eq_one] at h

omit [IsAlgClosed K] in

theorem slot_nonsingular (p : ℕ) [Fact p.Prime] (ζu : Kˣ) (hζ : IsPrimitiveRoot (ζu : K) p)
    {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) (e k : ℕ) (h1k : 1 ≤ k) (hkp : k < p) :
    (curve (t ^ p)).toAffine.Nonsingular (pointX (t ^ p) ((ζu : K) ^ e * t ^ k))
      (pointY (t ^ p) ((ζu : K) ^ e * t ^ k)) :=
  nonsingular_point (pow_ne_zero _ ht0) (nnnorm_tpow_lt_one ht (Fact.out : p.Prime).ne_zero)
    (slotParam_ne_zero ζu ht0 e k) (slotParam_offLattice p ζu hζ ht0 ht e k h1k hkp)

theorem slot_add_self_eq_neg_three (p : ℕ) [Fact p.Prime] (hp3 : p = 3) (ζu : Kˣ)
    (hζ : IsPrimitiveRoot (ζu : K) p) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) (e : ℕ)
    (h : (curve (t ^ p)).toAffine.Nonsingular (pointX (t ^ p) ((ζu : K) ^ e * t ^ 1))
      (pointY (t ^ p) ((ζu : K) ^ e * t ^ 1))) :
    (Point.some _ _ h : (curve (t ^ p)).toAffine.Point) + Point.some _ _ h
      = -Point.some _ _ h := by
  have hp : p.Prime := Fact.out
  have h3 : p • (Point.some _ _ h : (curve (t ^ p)).toAffine.Point) = 0 :=
    nsmul_prime_eq_zero_unconditional (pow_ne_zero _ ht0) (nnnorm_tpow_lt_one ht hp.ne_zero)
      (slotParam_ne_zero ζu ht0 e 1) (slotParam_offLattice p ζu hζ ht0 ht e 1 le_rfl (by omega))
      (tateParam_pow hζ.pow_eq_one rfl e 1) hp (hp.odd_of_ne_two (by omega)) h
  have h3' : (2 + 1 : ℕ) • (Point.some _ _ h : (curve (t ^ p)).toAffine.Point) = 0 := by
    rw [show (2 + 1 : ℕ) = p by omega]; exact h3
  rw [add_nsmul, one_nsmul, two_nsmul] at h3'
  exact eq_neg_of_add_eq_zero_left h3'

theorem pointY_slot_ne_negY_three (p : ℕ) [Fact p.Prime] (hp3 : p = 3) (ζu : Kˣ)
    (hζ : IsPrimitiveRoot (ζu : K) p) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖₊ < 1) (e : ℕ) :
    pointY (t ^ p) ((ζu : K) ^ e * t ^ 1)
      ≠ (curve (t ^ p)).toAffine.negY (pointX (t ^ p) ((ζu : K) ^ e * t ^ 1))
          (pointY (t ^ p) ((ζu : K) ^ e * t ^ 1)) := by
  have h_k := slot_nonsingular p ζu hζ ht0 ht e 1 le_rfl (by omega)
  intro hy
  have hpt : (Point.some _ _ h_k : (curve (t ^ p)).toAffine.Point) = -Point.some _ _ h_k := by
    rw [Point.neg_some]; simp only [Point.some.injEq]; exact ⟨trivial, hy⟩
  have hsum := slot_add_self_eq_neg_three p hp3 ζu hζ ht0 ht e h_k
  have hzero : (Point.some _ _ h_k : (curve (t ^ p)).toAffine.Point) + Point.some _ _ h_k = 0 := by
    nth_rewrite 2 [hpt]
    exact add_neg_cancel _
  rw [hzero] at hsum
  exact Point.some_ne_zero _ (neg_eq_zero.mp hsum.symm)

end PointSum
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport"

end SlotSeriesTransport
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport"

namespace TateSlotChord

open ModularCurve

variable (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime]

scoped instance instNeZeroPrime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem tateBase_a₁ : (tateBase K p).a₁ = 1 := by
  show ((tateLaurent K).map (qExpand K p)).a₁ = 1
  rw [WeierstrassCurve.map_a₁]
  show (qExpand K p) (tateLaurent K).a₁ = 1
  rw [show (tateLaurent K).a₁ = 1 from by
    simp [tateLaurent, WeierstrassCurve.map_a₁, tatePowerSeries]]
  exact map_one _

theorem tateBase_a₂ : (tateBase K p).a₂ = 0 := by
  show ((tateLaurent K).map (qExpand K p)).a₂ = 0
  rw [WeierstrassCurve.map_a₂]
  rw [show (tateLaurent K).a₂ = 0 from by
    simp [tateLaurent, WeierstrassCurve.map_a₂, tatePowerSeries]]
  exact map_zero _

theorem tateBase_a₃ : (tateBase K p).a₃ = 0 := by
  show ((tateLaurent K).map (qExpand K p)).a₃ = 0
  rw [WeierstrassCurve.map_a₃]
  rw [show (tateLaurent K).a₃ = 0 from by
    simp [tateLaurent, WeierstrassCurve.map_a₃, tatePowerSeries]]
  exact map_zero _

variable (hp3 : 3 ≤ p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)

theorem isUnit_ofPowerSeries_of_coeff {R : Type*} [CommRing R] (f : PowerSeries R) (N : ℕ)
    (hlow : ∀ n < N, PowerSeries.coeff n f = 0) (hN : IsUnit (PowerSeries.coeff N f)) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ R) f) := by

  set g : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + N) f with hg
  have hg0 : PowerSeries.coeff 0 g = PowerSeries.coeff N f := by
    simp only [hg, PowerSeries.coeff_mk, zero_add]
  have hgU : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0] using hN
  have hfac : f = PowerSeries.X ^ N * g := by
    ext n
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · simp only [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
    · exact hlow n (Nat.lt_of_not_le h)
  rw [hfac, map_mul, map_pow]
  refine IsUnit.mul (IsUnit.pow N ?_) (hgU.map _)
  rw [HahnSeries.ofPowerSeries_X]
  exact ⟨⟨HahnSeries.single (1 : ℤ) (1 : R), HahnSeries.single (-1 : ℤ) (1 : R),
    by rw [HahnSeries.single_mul_single]; simp,
    by rw [HahnSeries.single_mul_single]; simp⟩, rfl⟩

include hp3 in

theorem slotSubstX_coeff_low (c : Kˣ) (j : ℕ) (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    (∀ n < j, PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K) := by
  have hjp' : j < p := lt_of_le_of_lt hjp
    (Nat.div_lt_self ((Fact.out : p.Prime).pos) one_lt_two)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2j : 2 * j < p := by rcases hodd with ⟨w, hw⟩; omega

  have tails (n : ℕ) (hn : n ≤ j) :
      (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : K) * (((if n = p * M + j * e then (c : K) ^ e else 0)
          + if n + j * e = p * M then (↑c⁻¹ : K) ^ e else 0)
          - if n = p * M then 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp at he
    have heM : e ≤ M := Nat.le_of_dvd hM1 (Nat.mem_divisors.mp he).1
    have hMn : M ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
    have h1 : ¬ n = p * M + j * e := by nlinarith [hM1, hjp']
    have h3 : ¬ n = p * M := by nlinarith [hM1, hjp']
    have h2 : ¬ n + j * e = p * M := by
      intro heq
      have : n ≥ (p - j) * M := by nlinarith [heM]
      have : p - j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hM1) this
      omega
    simp [h1, h2, h3]
  constructor
  · intro n hn
    rw [coeff_slotSubst_tateUnivX p c j h1j hjp' n, tails n hn.le, add_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact if_neg fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.mpr hn)
  · rw [coeff_slotSubst_tateUnivX p c j h1j hjp' j, tails j le_rfl, add_zero,
      if_pos (dvd_refl j), Nat.div_self h1j, Nat.cast_one, one_mul, pow_one]

include hp3 in

theorem slotSubst_tangentDenom_coeff_low (c : Kˣ) (j : ℕ) (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    (∀ n < j, PowerSeries.coeff n
      (2 * slotSubst K p c j tateUnivY + slotSubst K p c j tateUnivX) = 0) ∧
    PowerSeries.coeff j
      (2 * slotSubst K p c j tateUnivY + slotSubst K p c j tateUnivX) = (c : K) := by
  have hjp' : j < p := lt_of_le_of_lt hjp
    (Nat.div_lt_self ((Fact.out : p.Prime).pos) one_lt_two)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2j : 2 * j < p := by rcases hodd with ⟨w, hw⟩; omega

  have tailsY (n : ℕ) (hn : n ≤ j) :
      (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
          - if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * (↑c⁻¹ : K) ^ e else 0)
          + if n = p * M then ((e : ℕ) : K) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp at he
    have heM : e ≤ M := Nat.le_of_dvd hM1 (Nat.mem_divisors.mp he).1
    have hMn : M ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
    have h1 : ¬ n = p * M + j * e := by nlinarith [hM1, hjp']
    have h3 : ¬ n = p * M := by nlinarith [hM1, hjp']
    have h2 : ¬ n + j * e = p * M := by
      intro heq; have : n ≥ (p - j) * M := by nlinarith [heM]
      have : p - j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hM1) this; omega
    simp [h1, h2, h3]

  have hYlow (n : ℕ) (hn : n ≤ j) :
      PowerSeries.coeff n (slotSubst K p c j tateUnivY) = 0 := by
    rw [coeff_slotSubst_tateUnivY p c j h1j hjp' n, tailsY n hn, add_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [Nat.div_self h1j]
    · exact if_neg fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.mpr hlt)
  have hX := slotSubstX_coeff_low K p hp3 c j h1j hjp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [two_mul, map_add, map_add, hYlow n hn.le, hX.1 n hn, add_zero, add_zero]
  · rw [two_mul, map_add, map_add, hYlow j le_rfl, hX.2, add_zero, zero_add]

include hp3 in

theorem isUnit_tangentDenom_nonToricPoint (k : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) :
    IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
      + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) := by
  rw [tateBase_a₁, tateBase_a₃, one_mul, add_zero, nonToricPoint_fst, nonToricPoint_snd,
    ← map_ofNat (HahnSeries.ofPowerSeries ℤ K) 2, ← map_mul, ← map_add]
  refine isUnit_ofPowerSeries_of_coeff _ k ?_ ?_
  · exact (slotSubst_tangentDenom_coeff_low K p hp3 (ζ ^ (b * k)) k h1k hkp).1
  · rw [(slotSubst_tangentDenom_coeff_low K p hp3 (ζ ^ (b * k)) k h1k hkp).2]
    exact Units.isUnit _

def tangentG {R : Type*} [CommRing R] (a₁ a₂ num den xk xm : R) : R :=
  num ^ 2 + a₁ * num * den - (a₂ + xk + xk + xm) * den ^ 2

theorem tangentG_eq_zero_iff_addX_eq {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (xk yk xm : F) (hy : yk ≠ WeierstrassCurve.Affine.negY W xk yk) :
    tangentG W.a₁ W.a₂
        (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk)
        (yk - WeierstrassCurve.Affine.negY W xk yk) xk xm = 0 ↔
      WeierstrassCurve.Affine.addX W xk xk (WeierstrassCurve.Affine.slope W xk xk yk yk)
        = xm := by
  have hd : yk - WeierstrassCurve.Affine.negY W xk yk ≠ 0 := sub_ne_zero.mpr hy
  have key : tangentG W.a₁ W.a₂
        (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk)
        (yk - WeierstrassCurve.Affine.negY W xk yk) xk xm
      = (yk - WeierstrassCurve.Affine.negY W xk yk) ^ 2
        * (WeierstrassCurve.Affine.addX W xk xk
              (WeierstrassCurve.Affine.slope W xk xk yk yk) - xm) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, WeierstrassCurve.Affine.addX, tangentG]
    field_simp
    ring
  rw [key, mul_eq_zero, or_iff_right (pow_ne_zero 2 hd), sub_eq_zero]

end TateSlotChord
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.TateSlotChord"

namespace SlotSeriesBridge

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun ModularCurve WeierstrassCurve WeierstrassCurve.Affine"
open scoped NNReal

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [CharZero F] [IsAlgClosed F] [DecidableEq F]

theorem tangentG_analytic_three (p : ℕ) [Fact p.Prime] (hp3 : p = 3)
    (ζu : Fˣ) (hζ : IsPrimitiveRoot (ζu : F) p) :
    ∀ b : ℕ, ∀ t : F, t ≠ 0 → ‖t‖₊ < 1 →
      (3 * pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1) ^ 2 + a₄ (t ^ p)
          - pointY (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1)) ^ 2
        + (3 * pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1) ^ 2 + a₄ (t ^ p)
            - pointY (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1))
          * (2 * pointY (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1)
            + pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1))
        - (2 * pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1)
            + pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1))
          * (2 * pointY (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1)
            + pointX (t ^ p) (((ζu ^ (b * 1) : Fˣ) : F) * t ^ 1)) ^ 2 = 0 := by
  intro b t ht0 ht1
  simp only [Units.val_pow_eq_pow_val]
  have h_k := SlotSeriesTransport.slot_nonsingular p ζu hζ ht0 ht1 (b * 1) 1 le_rfl (by omega)
  have hadd := SlotSeriesTransport.slot_add_self_eq_neg_three p hp3 ζu hζ ht0 ht1 (b * 1) h_k
  have hyneq := SlotSeriesTransport.pointY_slot_ne_negY_three p hp3 ζu hζ ht0 ht1 (b * 1)
  rw [Point.add_of_Y_ne (h₁ := h_k) (h₂ := h_k) hyneq, Point.neg_some] at hadd
  have haddX : (curve (t ^ p)).toAffine.addX
        (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
        (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
        ((curve (t ^ p)).toAffine.slope
          (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
          (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
          (pointY (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
          (pointY (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1)))
      = pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1) := by
    injection hadd
  have hG := (TateSlotChord.tangentG_eq_zero_iff_addX_eq (curve (t ^ p))
      (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
      (pointY (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1))
      (pointX (t ^ p) ((ζu : F) ^ (b * 1) * t ^ 1)) hyneq).mpr haddX
  simp only [TateSlotChord.tangentG, curve_a₁, curve_a₂, curve_a₃, curve_a₄,
    WeierstrassCurve.Affine.negY] at hG
  linear_combination hG

end SlotSeriesBridge
p2m_reactivate "P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.SlotSeriesTransport P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three.TateSlotChord"

p2m_open "TateCurve~hasSum_xfun~hasSum_yfun" in open ModularCurve  in
open scoped PadicComplex in

theorem solution
    (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (hp3 : p = 3)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) (k : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) :
    IsUnit (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
        + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃) ∧
    ∃ ℓ : LaurentSeries K,
      ℓ * (2 * (nonToricPoint K p (ζ ^ (b * k)) k).2
          + (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).1 + (tateBase K p).a₃)
        = 3 * (nonToricPoint K p (ζ ^ (b * k)) k).1 ^ 2
          + 2 * (tateBase K p).a₂ * (nonToricPoint K p (ζ ^ (b * k)) k).1
          + (tateBase K p).a₄ - (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * k)) k).2 ∧
      ℓ ^ 2 + (tateBase K p).a₁ * ℓ - (tateBase K p).a₂
          - 2 * (nonToricPoint K p (ζ ^ (b * k)) k).1
        = (nonToricPoint K p (ζ ^ (b * k)) k).1 := by
  haveI : Fact p.Prime := ⟨by rw [hp3]; exact Nat.prime_three⟩
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp3' : 3 ≤ p := hp3.ge
  obtain rfl : k = 1 := by omega
  haveI : NeZero ((p : ℕ) : ℂ_[2]) := ⟨Nat.cast_ne_zero.mpr hp0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[2] p
  set ζu : ℂ_[2]ˣ := (hζ₀.isUnit hp0).unit with hζu_def
  have hζu : IsPrimitiveRoot (ζu : ℂ_[2]) p := by rwa [hζu_def, IsUnit.unit_spec]
  exact SlotSeriesTransport.tangent_of_pointTies (F := ℂ_[2]) p ζu hζu
    (GLT1.hasSum_coeff_slotSubst_tateUnivX_pointX p hp3')
    (GLT1.hasSum_coeff_slotSubst_tateUnivY_pointY p hp3')
    1 1 h1k hkp h1k hkp
    (SlotSeriesBridge.tangentG_analytic_three p hp3 ζu hζu)
    K ζ hζ b
    (TateSlotChord.isUnit_tangentDenom_nonToricPoint K p hp3' ζ b 1 h1k hkp)

end S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three
end P2MW
export P2MW.S_ModularCurve_exists_tangentSlope_nonToricPoint_of_eq_three (solution)
