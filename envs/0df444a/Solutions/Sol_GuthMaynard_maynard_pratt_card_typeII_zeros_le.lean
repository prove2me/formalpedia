-- Prove2me | solution 1 for GuthMaynard.maynard_pratt_card_typeII_zeros_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:24:09.059213+00:00
-- url     : https://prove2.me/submissions/a10a6526-94fc-4524-a1c2-71a6c76ea17f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_GuthMaynard_maynard_pratt_twisted_fourth_moment

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
/-!
# Maynard–Pratt Lemma 24 (arXiv:2206.11729v2, Appendix C, pp. 37–38): blueprint

`R_II(σ,T) ≪ T^{2(1-σ)} (log T)^{O(1)}`, reduced to the twisted fourth moment
`GuthMaynard.maynard_pratt_twisted_fourth_moment` (MP's display on p. 38) and the local zero count
`Zeta23.RvM.zeta_local_zero_count`.

Route (MP's, with one change): for a Type II zero `ρ = β + iγ`,
`1/3 ≤ (1/2π) T^{(1/2-β)/2} ∫ |Γ(1/2-β+iu)| |F(γ+u)| du` with `F(t) = M(1/2+it) ζ(1/2+it)`.
MP truncate at `|u| ≤ (log T)^2` using exponential decay of `Γ`; here the tail `|u| > T/4` is
cut using polynomial decay of `Γ` (order 6), and the weight `|Γ(1/2-β+iu)| ≤ K log T/(1+u²)` is
kept inside a weighted Hölder (Jensen) inequality, so no `(log T)^2`-truncation is needed. Summing
over zeros, the weights `∑_ρ m_ρ/(1+(t-γ)²) ≪ log T` replace MP's `(log T)^3`-separated set.

Every lemma marked `sorry` is a prover target; the assembly `l24_dev` is sorry-free modulo them.
-/
/-! ## Definitions -/
/-- The mollifier `M(s) = ∑_{m ≤ 2T^{1/100}} μ(m) m^{-s}` of MP (19). -/
noncomputable def Mf (T : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- `F(t) = M(1/2+it) ζ(1/2+it)`. -/
noncomputable def F (T t : ℝ) : ℂ :=
  Mf T (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)

/-- The Type II line integral of MP (19), as in the published statement. -/
noncomputable def J (T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
    (T : ℂ) ^ ((((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I) / 2) *
      Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I) *
      Mf T (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)) *
      riemannZeta (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I))

/-- The weighted fourth moment around the ordinate of `ρ`. -/
noncomputable def Q (T : ℝ) (ρ : ℂ) : ℝ :=
  ∫ t in T / 2..3 * T, ‖F T t‖ ^ 4 * (1 + (t - ρ.im) ^ 2)⁻¹

/-- Zeros in a set `S`, counted with multiplicity, in `ℕ∞`. -/
noncomputable def zc (S : Set ℂ) : ℕ∞ := ∑' s : S, analyticOrderAt riemannZeta (s : ℂ)

/-- The Type II zeros of the statement. -/
def S2 (σ T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧ 1 / 3 ≤ ‖J T ρ‖}

/-- The multiplicity as a real number. -/
noncomputable def mult (ρ : ℂ) : ℝ := ((analyticOrderAt riemannZeta ρ).toNat : ℝ)

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-! ## Counting primitives -/
lemma pa_enat_summable {β : Type*} (f : β → ℕ∞) : Summable f :=
  ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩

lemma pa_not_analytic_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hc : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have h2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1)
      (𝓝 ((1 - 1) * riemannZeta 1)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique riemannZeta_residue_one h2
  simp at this

lemma pa_order_ne_top (ρ : ℂ) : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  by_cases h : ρ = 1
  · subst h; rw [analyticOrderAt_of_not_analyticAt pa_not_analytic_one]; exact ENat.zero_ne_top
  · exact Zeta23.analyticOrderAt_riemannZeta_ne_top h

lemma pa_order_eq (ρ : ℂ) : ((analyticOrderAt riemannZeta ρ : ℕ∞) : ℝ≥0∞) =
    ENNReal.ofReal ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (pa_order_ne_top ρ)
  rw [← hn]; simp

lemma pa_zc_eq (S : Set ℂ) : (zc S : ℝ≥0∞) =
    ∑' s : S, ENNReal.ofReal ((analyticOrderAt riemannZeta (s : ℂ)).toNat : ℝ) := by
  unfold zc
  rw [show ((∑' s : S, analyticOrderAt riemannZeta (s : ℂ) : ℕ∞) : ℝ≥0∞) =
      ENat.toENNRealRingHom (∑' s : S, analyticOrderAt riemannZeta (s : ℂ)) from rfl,
    (pa_enat_summable _).map_tsum ENat.toENNRealRingHom ENat.continuous_toENNReal]
  exact tsum_congr fun s => pa_order_eq s

/-- A count bounded on every finite subset (with multiplicities `toNat`) is bounded.
(`analyticOrderAt riemannZeta ρ ≠ ⊤` for every `ρ`: `0` at the pole, finite elsewhere since `ζ`
is not locally zero on the connected set `{1}ᶜ`.) -/
theorem count_le_of_finset_bound (S : Set ℂ) (K : ℝ)
    (h : ∀ F : Finset ℂ, (↑F : Set ℂ) ⊆ S → (∑ ρ ∈ F, mult ρ) ≤ K) :
    (zc S : ℝ≥0∞) ≤ ENNReal.ofReal K := by
  rw [pa_zc_eq, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun u => ?_
  have hsub : (↑(u.map (Function.Embedding.subtype _)) : Set ℂ) ⊆ S := by
    intro x hx
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have := h _ hsub
  rw [Finset.sum_map] at this
  simp only [mult] at this
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal this

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
/-! ## Counting primitives (as in the Ingham development, `IngPartC.lean`) -/
alias count_le_of_finset_bound := GuthMaynard.CitedZeros.L24.PartA.count_le_of_finset_bound

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
lemma pa_zerosIn_finite (a b : ℝ) : (Zeta23.zerosIn a b).Finite :=
  Zeta23.zetaSeam.finite_window a b

lemma pa_Ncount_eq (a b : ℝ) : (Zeta23.Ncount a b : ℝ) =
    ∑ ρ ∈ (pa_zerosIn_finite a b).toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (pa_zerosIn_finite a b)]
  push_cast; rfl

lemma pa_window_sum_le (F : Finset ℂ) (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re) (a b : ℝ) :
    ∑ ρ ∈ F.filter (fun ρ => a < ρ.im ∧ ρ.im ≤ b), ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
      Zeta23.Ncount a b := by
  rw [pa_Ncount_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ.1
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨h1, h2, ?_⟩, hρ.2.1, hρ.2.2⟩
    by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h1
  · intros; positivity

lemma pa_ceil_sub_one {x : ℝ} (hx : 0 < x) :
    (((⌈x⌉₊ - 1 : ℕ) : ℝ) < x) ∧ x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  rw [Nat.cast_sub h1]
  push_cast
  constructor
  · linarith [Nat.ceil_lt_add_one hx.le]
  · linarith [Nat.le_ceil x]

lemma pa_log_shift {x : ℝ} (hx : 3 ≤ x) : Real.log (x + 1) ≤ 2 * Real.log x := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by linarith)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith

/-- Local zero count with multiplicity, from `Zeta23.RvM.zeta_local_zero_count`. -/
theorem local_count_finset : ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Finset ℂ,
    (∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re) → ∀ t H : ℝ, 0 ≤ H →
      ∑ ρ ∈ F.filter (fun ρ => |ρ.im - t| ≤ H), mult ρ ≤
        A * (H + 1) * Real.log (|t| + H + 3) := by
  simp only [mult]
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨4 * A₀, by linarith, fun F hF t H hH => ?_⟩
  set G := F.filter (fun ρ => |ρ.im - t| ≤ H) with hG
  set a := t - H - 1 with ha
  set K := ⌊2 * H⌋₊ + 2 with hK
  set k : ℂ → ℕ := fun ρ => ⌈ρ.im - a⌉₊ - 1 with hk
  have hmaps : ∀ ρ ∈ G, k ρ ∈ Finset.range K := by
    intro ρ hρ
    rw [hG, Finset.mem_filter] at hρ
    have h1 := (abs_le.1 hρ.2)
    rw [Finset.mem_range]
    have hc : ⌈ρ.im - a⌉₊ ≤ ⌈2 * H⌉₊ + 1 := by
      rw [Nat.ceil_le]; push_cast
      linarith [Nat.le_ceil (2 * H)]
    have := Nat.ceil_le_floor_add_one (2 * H)
    simp only [hk]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlog3 : 0 ≤ Real.log (|t| + H + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hfib : ∀ j ∈ Finset.range K, ∑ ρ ∈ G.filter (fun ρ => k ρ = j),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ 2 * A₀ * Real.log (|t| + H + 3) := by
    intro j hj
    have hsub : G.filter (fun ρ => k ρ = j) ⊆
        F.filter (fun ρ => a + j < ρ.im ∧ ρ.im ≤ a + j + 1) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ ⊢
      obtain ⟨hρG, hkj⟩ := hρ
      rw [hG, Finset.mem_filter] at hρG
      have h1 := (abs_le.1 hρG.2)
      have hx : 0 < ρ.im - a := by rw [ha]; linarith
      obtain ⟨c1, c2⟩ := pa_ceil_sub_one hx
      have : ((⌈ρ.im - a⌉₊ - 1 : ℕ) : ℝ) = j := by rw [← hkj]
      refine ⟨hρG.1, by linarith, by linarith⟩
    have hjK : (j : ℝ) + 1 ≤ ⌊2 * H⌋₊ + 2 := by
      have := Finset.mem_range.1 hj
      have : j + 1 ≤ ⌊2 * H⌋₊ + 2 := by omega
      exact_mod_cast this
    have hfl := Nat.floor_le (show 0 ≤ 2 * H by linarith)
    have habs : |a + j| ≤ |t| + H + 1 := by
      rw [abs_le]
      have := neg_abs_le t
      have := le_abs_self t
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      constructor <;> rw [ha] <;> linarith
    calc ∑ ρ ∈ G.filter (fun ρ => k ρ = j), ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
        ≤ ∑ ρ ∈ F.filter (fun ρ => a + j < ρ.im ∧ ρ.im ≤ a + j + 1),
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ Zeta23.Ncount (a + j) (a + j + 1) := pa_window_sum_le F hF _ _
      _ ≤ A₀ * Real.log (|a + j| + 3) := hA (a + j)
      _ ≤ A₀ * (2 * Real.log (|t| + H + 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          refine le_trans (Real.log_le_log (by positivity) (?_ : |a + j| + 3 ≤ (|t| + H + 3) + 1))
            (pa_log_shift (by linarith [abs_nonneg t]))
          linarith
      _ = 2 * A₀ * Real.log (|t| + H + 3) := by ring
  calc ∑ j ∈ Finset.range K, ∑ ρ ∈ G.filter (fun ρ => k ρ = j),
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
      ≤ ∑ j ∈ Finset.range K, 2 * A₀ * Real.log (|t| + H + 3) := Finset.sum_le_sum hfib
    _ = (K : ℝ) * (2 * A₀ * Real.log (|t| + H + 3)) := by simp
    _ ≤ (2 * (H + 1)) * (2 * A₀ * Real.log (|t| + H + 3)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hK]; push_cast
        linarith [Nat.floor_le (show 0 ≤ 2 * H by linarith)]
    _ = 4 * A₀ * (H + 1) * Real.log (|t| + H + 3) := by ring

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-! ## The steps -/
/-- Nontrivial zeros (ordinate `≠ 0`) lie in `0 < Re < 1` (as `MP23.zero_re_pos_lt_one`). -/
theorem zero_re_pos_lt_one {ρ : ℂ} (h : riemannZeta ρ = 0) (hi : ρ.im ≠ 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hre
    push Not at hre
    set s : ℂ := 1 - ρ with hs
    have hsre : 1 ≤ s.re := by simp [hs]; linarith
    have hsim : s.im ≠ 0 := by simp [hs]; exact hi
    have hn : ∀ n : ℕ, s ≠ -n := by
      intro n hn; apply hsim; rw [hn]; simp
    have h1 : s ≠ 1 := by intro h1; apply hsim; rw [h1]; simp
    have hfe := riemannZeta_one_sub hn h1
    rw [hs, sub_sub_cancel, ← hs] at hfe
    rw [h] at hfe
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
    have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hn
    have hc : Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      apply hsim
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hs' : s = 2 * (k : ℂ) + 1 := by
        apply mul_left_cancel₀ hpi
        linear_combination 2 * hk
      rw [hs']; simp
    have hp : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      push Not
      intro h0
      exfalso
      have : (2 * (Real.pi : ℂ)) ≠ 0 := by
        exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact this h0
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp) hG) hc) hz) hfe.symm
  · by_contra hre
    push Not at hre
    exact riemannZeta_ne_zero_of_one_le_re hre h

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
/-! ## The steps -/
alias zero_re_pos_lt_one := GuthMaynard.CitedZeros.L24.PartA.zero_re_pos_lt_one

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-- All zeros with ordinate in `[T, 2T]`: `≪ T log T` (`local_count_finset` with `t = 3T/2`,
`H = T/2`, and `zero_re_pos_lt_one`). -/
theorem trivial_count : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ G : Finset ℂ,
    (∀ ρ ∈ G, riemannZeta ρ = 0 ∧ ρ.im ∈ Set.Icc T (2 * T)) →
      ∑ ρ ∈ G, mult ρ ≤ C * T * Real.log T := by
  obtain ⟨A, hA, hloc⟩ := local_count_finset
  refine ⟨2 * A, 3, by linarith, fun T hT G hG => ?_⟩
  have hG' : ∀ ρ ∈ G, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ =>
    ⟨(hG ρ hρ).1, (zero_re_pos_lt_one (hG ρ hρ).1
      (by have := (hG ρ hρ).2.1; intro h0; linarith)).1⟩
  have h := hloc G hG' (3 * T / 2) (T / 2) (by linarith)
  rw [Finset.filter_true_of_mem (fun ρ hρ => by
    have := (hG ρ hρ).2
    rw [abs_le]; constructor <;> linarith [this.1, this.2])] at h
  rw [abs_of_nonneg (by linarith)] at h
  have hlog : Real.log (3 * T / 2 + T / 2 + 3) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hl0 : 0 ≤ Real.log (3 * T / 2 + T / 2 + 3) := Real.log_nonneg (by linarith)
  calc ∑ ρ ∈ G, mult ρ ≤ A * (T / 2 + 1) * Real.log (3 * T / 2 + T / 2 + 3) := h
    _ ≤ A * T * (2 * Real.log T) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA) hlog hl0 (by positivity)
    _ = 2 * A * T * Real.log T := by ring

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
alias trivial_count := GuthMaynard.CitedZeros.L24.PartA.trivial_count

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartD
open GuthMaynard.CitedZeros.L24
/-! ### Γ in vertical strips (adapted from `MP23.lean`) -/
lemma norm_Gamma_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, Real.Gamma x ≤ C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx => ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Complex.Gamma (z + n) = Complex.Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := real_Gamma_compact_bound (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Complex.Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Complex.Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

/-- Polynomial decay of `Γ` in vertical strips. -/
lemma gamma_decay (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → (1 + |z.im|) ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Complex.Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Complex.Gamma z‖ ≤ C₀ :=
      (norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza, hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

/-! ### Growth of ζ (adapted from `MP23.lean`) -/
/-- Terms of the continuation `(w-1) ζ(w) = -1 + ∑ eT w n`. -/
noncomputable def eT (w : ℂ) (n : ℕ) : ℂ :=
  (w - 1) * ((n : ℂ) + 1) ^ (-w) - ((n : ℂ) + 1) ^ (1 - w) + ((n : ℂ) + 2) ^ (1 - w)

lemma cpow_diff_bound (w : ℂ) (hw : 0 < w.re) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : y ∈ Icc x (x + 1)) :
    ‖(y : ℂ) ^ (-w) - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) * (y - x) := by
  have hderiv : ∀ t ∈ Icc x (x + 1), HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-w))
      ((-w) * (t : ℂ) ^ (-w - 1)) (Icc x (x + 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_ofReal_cpow_const ht0 (by
      intro h; apply (ne_of_gt hw); have := congrArg Complex.re h; simpa using this)).hasDerivWithinAt
  have hb : ∀ t ∈ Ico x (x + 1), ‖(-w) * (t : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * x ^ (-w.re - 1) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)) (norm_nonneg _)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb y hy

lemma eT_bound (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx : 0 < x := by positivity
  rcases eq_or_ne w 1 with rfl | hw1
  · simp [eT]
  have hw1' : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  set φ : ℝ → ℂ := fun y => (w - 1) * (y : ℂ) * (x : ℂ) ^ (-w) + (y : ℂ) ^ (1 - w) with hφ
  have hderiv : ∀ t ∈ Icc x (x + 1), HasDerivWithinAt φ
      ((w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w)) (Icc x (x + 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 := hasDerivAt_ofReal_cpow_const ht0 hw1'
    rw [show 1 - w - 1 = -w by ring] at h1
    have h2 : HasDerivAt (fun y : ℝ => (w - 1) * (y : ℂ) * (x : ℂ) ^ (-w)) ((w - 1) * (x : ℂ) ^ (-w)) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (w - 1)).mul_const ((x : ℂ) ^ (-w))
      simpa using this
    exact (h2.add h1).hasDerivWithinAt
  have hb : ∀ t ∈ Ico x (x + 1),
      ‖(w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w)‖ ≤ ‖w - 1‖ * (‖w‖ * x ^ (-w.re - 1)) := by
    intro t ht
    have e : (w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w) =
        -((w - 1) * ((t : ℂ) ^ (-w) - (x : ℂ) ^ (-w))) := by ring
    rw [e, norm_neg, norm_mul]
    gcongr
    calc ‖(t : ℂ) ^ (-w) - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) * (t - x) :=
          cpow_diff_bound w hw x hx t (Ico_subset_Icc_self ht)
      _ ≤ ‖w‖ * x ^ (-w.re - 1) * 1 := by
          gcongr
          linarith [ht.2]
      _ = _ := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb (x + 1) ⟨by linarith, le_rfl⟩
  have he : φ (x + 1) - φ x = eT w n := by
    simp only [hφ, eT, hxdef]
    push_cast
    rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
    have hx0 : ((n : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    have : ((n : ℂ) + 1) ^ (1 - w) = ((n : ℂ) + 1) * ((n : ℂ) + 1) ^ (-w) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    rw [this]
    ring
  rw [he] at hmvt
  calc ‖eT w n‖ ≤ ‖w - 1‖ * (‖w‖ * x ^ (-w.re - 1)) * (x + 1 - x) := hmvt
    _ = _ := by ring

lemma summable_rpow_shift {p : ℝ} (hp : 1 < p) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
  have := (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  refine this.congr (fun n => ?_)
  have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos h0, Real.rpow_neg h0.le, one_div]

lemma eT_bound' (w : ℂ) (hw : 1 / 4 < w.re) (n : ℕ) :
    ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)) := by
  refine (eT_bound w (by linarith) n).trans ?_
  gcongr
  · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact this
  · linarith

lemma eT_differentiable (n : ℕ) : Differentiable ℂ (fun w => eT w n) := by
  intro w
  have h1 : ((n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  have h2 : ((n : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  unfold eT
  have d1 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl h1)
  have d2 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h1)
  have d3 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 2) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h2)
  exact (((differentiableAt_id.sub_const 1).mul d1).sub d2).add d3

/-- The continuation sum. -/
noncomputable def Gz (w : ℂ) : ℂ := ∑' n : ℕ, eT w n

/-- The domain `1/4 < Re w`, `|w| < R`. -/
def UR (R : ℝ) : Set ℂ := {w : ℂ | 1 / 4 < w.re} ∩ Metric.ball 0 R

lemma UR_open (R : ℝ) : IsOpen (UR R) :=
  (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball

lemma Gz_diff (R : ℝ) : DifferentiableOn ℂ Gz (UR R) := by
  have hs := (summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left ((R + 1) * R)
  refine differentiableOn_tsum_of_summable_norm hs (fun n => (eT_differentiable n).differentiableOn)
    (UR_open R) (fun n w hw => ?_)
  have hwR : ‖w‖ < R := by simpa using hw.2
  refine (eT_bound' w hw.1 n).trans ?_
  have h1 : ‖w - 1‖ ≤ R + 1 := (norm_sub_le _ _).trans (by simp; linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 hwR.le (norm_nonneg _) (by linarith [norm_nonneg w]))
    (by positivity)

lemma Gz_eq (w : ℂ) (hw : 1 < w.re) : Gz w = (w - 1) * riemannZeta w - 1 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcast : ∀ n : ℕ, ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := fun n => by push_cast; ring
  -- summability of `(n+1)^{-w}`
  have hs1 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (-w)) := by
    apply Summable.of_norm
    refine (summable_rpow_shift (p := w.re) hw).congr (fun n => ?_)
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
    simp
  have hsG : Summable (fun n : ℕ => eT w n) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
    · exact (summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left _
    · intro n; exact eT_bound' w (by linarith) n
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (1 - w) with hf
  have hs2 : Summable (fun n : ℕ => f (n + 1) - f n) := by
    have := hsG.sub (hs1.mul_left (w - 1))
    refine this.congr (fun n => ?_)
    simp only [eT, hf]; push_cast; ring_nf
  have hlim : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun n : ℕ => ‖f n‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (1 - w.re) := by
      funext n
      simp only [hf]
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
      simp
    rw [e]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := w.re - 1) (by linarith)).comp h1
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, neg_sub]
  have htel : ∑' n : ℕ, (f (n + 1) - f n) = -1 := by
    have hp := hs2.hasSum.tendsto_sum_nat
    have hq : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (f (i + 1) - f i)) atTop (𝓝 (0 - f 0)) := by
      have : (fun N : ℕ => ∑ i ∈ Finset.range N, (f (i + 1) - f i)) = fun N => f N - f 0 := by
        funext N; exact Finset.sum_range_sub f N
      rw [this]; exact hlim.sub_const _
    have := tendsto_nhds_unique hp hq
    rw [this]; simp [hf]
  have hz : riemannZeta w = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-w) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    congr 1; funext n; rw [Complex.cpow_neg, one_div]
  have hsplit : (fun n : ℕ => eT w n) = fun n : ℕ => (w - 1) * ((n : ℂ) + 1) ^ (-w) + (f (n + 1) - f n) := by
    funext n; simp only [eT, hf]; push_cast; ring_nf
  unfold Gz
  rw [hsplit, (hs1.mul_left (w - 1)).tsum_add hs2, tsum_mul_left, htel, hz]
  ring

lemma zeta1_eq (R : ℝ) (hR : 2 < R) : ∀ w ∈ UR R, riemannZeta₁ w = 1 + Gz w := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ (UR R) :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (UR_open R)
  have hB : AnalyticOnNhd ℂ (fun w => 1 + Gz w) (UR R) :=
    ((differentiableOn_const _).add (Gz_diff R)).analyticOnNhd (UR_open R)
  have hconv : Convex ℝ (UR R) := (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have h2 : (2 : ℂ) ∈ UR R := ⟨by norm_num, by simp; linarith⟩
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] fun w => 1 + Gz w := by
    have hU : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with w hw
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    rw [Gz_eq w hw, riemannZeta_eq_inv_sub_mul hw1]
    field_simp
    ring
  intro w hw
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB hconv.isPreconnected h2 hev hw

/-- Polynomial growth of `ζ` for `Re w ≥ 1/2`. -/
lemma zeta_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → 2 ≤ |w.im| →
    ‖riemannZeta w‖ ≤ C * (1 + ‖w‖) := by
  have hS := summable_rpow_shift (p := 3 / 2) (by norm_num)
  set S := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨1 + S, by positivity, fun w hw him => ?_⟩
  have hw1 : w ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
  have hwm : 2 ≤ ‖w - 1‖ := by
    refine him.trans ?_
    have := Complex.abs_im_le_norm (w - 1)
    simpa using this
  have hmem : w ∈ UR (‖w‖ + 3) := ⟨show (1 / 4 : ℝ) < w.re by linarith, by simp⟩
  have heq := zeta1_eq (‖w‖ + 3) (by linarith [norm_nonneg w]) w hmem
  have hbnd : ∀ n : ℕ, ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro n
    refine (eT_bound w (by linarith) n).trans ?_
    gcongr
    · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      exact this
    · linarith
  have hG : ‖Gz w‖ ≤ ‖w - 1‖ * ‖w‖ * S := by
    unfold Gz
    rw [hSdef, ← tsum_mul_left]
    exact tsum_of_norm_bounded (hS.mul_left _).hasSum hbnd
  rw [riemannZeta_eq_inv_sub_mul hw1, heq, norm_mul, norm_inv]
  have hpos : 0 < ‖w - 1‖ := by linarith
  rw [inv_mul_le_iff₀ hpos]
  calc ‖1 + Gz w‖ ≤ 1 + ‖w - 1‖ * ‖w‖ * S := (norm_add_le _ _).trans (by simp [hG])
    _ ≤ ‖w - 1‖ * ((1 + S) * (1 + ‖w‖)) := by
      nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) hS0]

lemma Mf_bound (T : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : ‖Mf T w‖ ≤ (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) := by
  unfold Mf
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [norm_mul]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := m)
      rw [show ((ArithmeticFunction.moebius m : ℤ) : ℂ) = (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
        by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast this
    have h2 : ‖(m : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by simp; linarith)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma floorM_le (T : ℝ) (hT : 1 ≤ T) : (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤ 2 * T := by
  refine (Nat.floor_le (by positivity)).trans ?_
  have : T ^ (1 / 100 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  rw [Real.rpow_one] at this
  linarith

/-! ### Bounds on the critical line -/
lemma zeta_line_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨C, hC, h⟩ := zeta_growth
  have hcont : Continuous (fun t : ℝ => ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖) := by
    refine continuous_norm.comp ?_
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      (by fun_prop : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * I))).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).bddAbove_image hcont.continuousOn
  refine ⟨2 * C + |M|, by positivity, fun t => ?_⟩
  by_cases ht : 2 ≤ |t|
  · have hw := h (1 / 2 + (t : ℂ) * I) (by simp) (by simpa using ht)
    have hn : ‖(1 / 2 + (t : ℂ) * I)‖ ≤ 1 / 2 + |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp
    calc _ ≤ C * (1 + ‖(1 / 2 + (t : ℂ) * I)‖) := hw
      _ ≤ C * (1 + (1 / 2 + |t|)) := by gcongr
      _ ≤ (2 * C + |M|) * (1 + |t|) := by nlinarith [abs_nonneg M, abs_nonneg t]
  · push Not at ht
    have hmem : t ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := hM (mem_image_of_mem _ hmem)
    calc _ ≤ M := this
      _ ≤ |M| := le_abs_self M
      _ ≤ (2 * C + |M|) * (1 + |t|) := by nlinarith [abs_nonneg M, abs_nonneg t]

lemma F_bound (Cz : ℝ)
    (hz : ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ Cz * (1 + |t|))
    {T : ℝ} (hT : 1 ≤ T) (t : ℝ) : ‖F T t‖ ≤ 2 * T * (Cz * (1 + |t|)) := by
  unfold F
  rw [norm_mul]
  have h1 : ‖Mf T (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * T :=
    (Mf_bound T (by simp)).trans (floorM_le T hT)
  exact mul_le_mul h1 (hz t) (norm_nonneg _) (by positivity)

lemma F_cont (T : ℝ) : Continuous (fun t : ℝ => F T t) := by
  have hl : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * I)) := by fun_prop
  have hM : Continuous (fun s : ℂ => Mf T s) := by
    unfold Mf
    refine continuous_finsetSum _ (fun m hm => ?_)
    have hm0 : (m : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      exact_mod_cast (by omega : m ≠ 0)
    exact continuous_const.mul (continuous_neg.const_cpow (Or.inl hm0))
  have hZ : Continuous (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      hl.continuousAt
  exact (hM.comp hl).mul hZ

/-- `Γ(s) = Γ(s+1)/s` on the line `Re s = c ∈ [-1/2, 0)`. -/
lemma gamma_line (C₅ : ℝ)
    (hC : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 → (1 + |z.im|) ^ 5 * ‖Complex.Gamma z‖ ≤ C₅)
    {c : ℝ} (hc1 : -1 / 2 ≤ c) (hc2 : c < 0) (u : ℝ) :
    ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * I)‖ * ‖((c : ℂ) + (u : ℂ) * I)‖ * (1 + |u|) ^ 5
      ≤ C₅ := by
  set s : ℂ := (c : ℂ) + (u : ℂ) * I with hs
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have h1 := hC (s + 1) (by simp [hs]; linarith) (by simp [hs]; linarith)
  have him : (s + 1).im = u := by simp [hs]
  rw [him, Complex.Gamma_add_one s hs0, norm_mul] at h1
  linarith [h1]

lemma amgm4 {a f : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f) : 4 * a ^ 3 * f ≤ f ^ 4 + 3 * a ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg (f - a)) (add_nonneg (add_nonneg (sq_nonneg f)
    (mul_nonneg (mul_nonneg zero_le_two ha) hf)) (mul_nonneg zero_le_three (sq_nonneg a)))]

lemma tail_alg {g fu T Cz C₅ u : ℝ} (hg0 : 0 ≤ g) (hT : 0 < T) (hCz : 0 ≤ Cz)
    (hgx : g * (1 + |u|) ^ 5 ≤ C₅) (hfx : fu ≤ 18 * T * Cz * (1 + |u|))
    (hLu : T / 4 < |u|) : g * fu ≤ 288 * C₅ * Cz / T * (1 + u ^ 2)⁻¹ := by
  set x : ℝ := 1 + |u| with hx
  have hx0 : 0 < x := by positivity
  have h1 : 1 + u ^ 2 ≤ x ^ 2 := by rw [hx]; nlinarith [sq_abs u, abs_nonneg u]
  have h2 : T ^ 2 ≤ 16 * x ^ 2 := by
    have h3 : T ≤ 4 * x := by rw [hx]; linarith
    have h4 : 0 ≤ T := hT.le
    nlinarith
  have hT2 : T ^ 2 * (1 + u ^ 2) ≤ 16 * x ^ 4 := by
    calc T ^ 2 * (1 + u ^ 2) ≤ (16 * x ^ 2) * x ^ 2 := by gcongr
      _ = 16 * x ^ 4 := by ring
  have hpos : 0 < 1 + u ^ 2 := by positivity
  rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
  calc g * fu * ((1 + u ^ 2) * T) ≤ g * (18 * T * Cz * x) * ((1 + u ^ 2) * T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfx hg0) (by positivity)
    _ = 18 * Cz * (g * x) * (T ^ 2 * (1 + u ^ 2)) := by ring
    _ ≤ 18 * Cz * (g * x) * (16 * x ^ 4) := by gcongr
    _ = 288 * Cz * (g * x ^ 5) := by ring
    _ ≤ 288 * Cz * C₅ := by gcongr
    _ = 288 * C₅ * Cz := by ring

lemma xi_bound {P A I E T : ℝ} (_hP0 : 0 < P) (hP1 : P ≤ 1) (hT : 0 < T) (hE0 : 0 ≤ E)
    (hET : 3 * E ≤ T)
    (h1 : 1 / 3 ≤ 1 / (2 * Real.pi) * (P * (A * I + E / T * Real.pi))) :
    Real.pi / 3 ≤ P * A * I := by
  have hpi := Real.pi_pos
  have hET' : E / T ≤ 1 / 3 := by rw [div_le_iff₀ hT]; linarith
  have h2 : P * (E / T * Real.pi) ≤ Real.pi / 3 := by
    have : 0 ≤ E / T := by positivity
    calc P * (E / T * Real.pi) ≤ 1 * (1 / 3 * Real.pi) := by gcongr
      _ = Real.pi / 3 := by ring
  have h3 : 2 * Real.pi / 3 ≤ P * (A * I + E / T * Real.pi) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul,
      show 2 * Real.pi * (1 / 3) = 2 * Real.pi / 3 by ring] at this
  have e : P * (A * I + E / T * Real.pi) = P * A * I + P * (E / T * Real.pi) := by ring
  linarith

lemma key_alg {X I Q' : ℝ} (hX0 : 0 < X) (hXI : Real.pi / 3 ≤ X * I)
    (hamgm : ∀ a : ℝ, 0 ≤ a → 4 * a ^ 3 * I ≤ Q' + 3 * a ^ 4 * Real.pi) :
    16 * Real.pi ≤ 2187 * (X ^ 4 * Q') := by
  have hpi := Real.pi_pos
  set a : ℝ := 2 / (9 * X) with ha
  have ha0 : 0 ≤ a := by positivity
  have haX : a * X = 2 / 9 := by rw [ha]; field_simp
  have h1 := hamgm a ha0
  have h2 : 4 * a ^ 3 * (Real.pi / 3) ≤ 4 * a ^ 3 * (X * I) := by gcongr
  have h3 : X * (4 * a ^ 3 * I) ≤ X * (Q' + 3 * a ^ 4 * Real.pi) :=
    mul_le_mul_of_nonneg_left h1 hX0.le
  have e3 : 3 * a ^ 4 * Real.pi * X = 2 * a ^ 3 * Real.pi / 3 := by
    rw [show 3 * a ^ 4 * Real.pi * X = 3 * a ^ 3 * Real.pi * (a * X) by ring, haX]; ring
  have h4 : 2 * a ^ 3 * Real.pi / 3 ≤ X * Q' := by linarith
  have h5 : X ^ 3 * (2 * a ^ 3 * Real.pi / 3) ≤ X ^ 3 * (X * Q') :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have e2 : X ^ 3 * (2 * a ^ 3 * Real.pi / 3) = 2 * (a * X) ^ 3 * Real.pi / 3 := by ring
  rw [e2, haX] at h5
  have e4 : X ^ 3 * (X * Q') = X ^ 4 * Q' := by ring
  linarith

lemma amgm_int {f : ℝ → ℝ} (hfc : Continuous f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : 0 ≤ L)
    {a : ℝ} (ha : 0 ≤ a) :
    4 * a ^ 3 * (∫ u in (-L)..L, (1 + u ^ 2)⁻¹ * f u) ≤
      (∫ u in (-L)..L, (1 + u ^ 2)⁻¹ * f u ^ 4) + 3 * a ^ 4 * Real.pi := by
  have hvc : Continuous (fun u : ℝ => (1 + u ^ 2)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun u => by positivity)
  have hW : ∫ u in (-L)..L, (1 + u ^ 2)⁻¹ ≤ Real.pi := by
    have e : (∫ u in (-L)..L, (1 + u ^ 2)⁻¹) = ∫ u in (-L)..L, 1 / (1 + u ^ 2) := by
      apply intervalIntegral.integral_congr; intro u _; simp
    rw [e, integral_one_div_one_add_sq]
    linarith [Real.arctan_lt_pi_div_two L, Real.neg_pi_div_two_lt_arctan (-L)]
  have hle : ∫ u in (-L)..L, 4 * a ^ 3 * ((1 + u ^ 2)⁻¹ * f u) ≤
      ∫ u in (-L)..L, ((1 + u ^ 2)⁻¹ * f u ^ 4 + 3 * a ^ 4 * (1 + u ^ 2)⁻¹) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_const.mul (hvc.mul hfc)).intervalIntegrable _ _
    · exact ((hvc.mul (hfc.pow 4)).add (continuous_const.mul hvc)).intervalIntegrable _ _
    · intro u _
      have h1 := amgm4 ha (hf0 u)
      have hv' : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hv']
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun u => (1 + u ^ 2)⁻¹ * f u ^ 4)
      (g := fun u => 3 * a ^ 4 * (1 + u ^ 2)⁻¹)
      ((hvc.mul (hfc.pow 4)).intervalIntegrable _ _)
      ((continuous_const.mul hvc).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hle
  have : 3 * a ^ 4 * ∫ u in (-L)..L, (1 + u ^ 2)⁻¹ ≤ 3 * a ^ 4 * Real.pi := by gcongr
  linarith

lemma Q_shift_le (T : ℝ) (ρ : ℂ) (hT : 0 < T) (h1 : T ≤ ρ.im) (h2 : ρ.im ≤ 2 * T) :
    ∫ u in (-(T / 4))..(T / 4), (1 + u ^ 2)⁻¹ * ‖F T (u + ρ.im)‖ ^ 4 ≤ Q T ρ := by
  set g : ℝ → ℝ := fun t => ‖F T t‖ ^ 4 * (1 + (t - ρ.im) ^ 2)⁻¹ with hg
  have hgc : Continuous g :=
    ((continuous_norm.comp (F_cont T)).pow 4).mul
      (Continuous.inv₀ (by fun_prop) (fun t => by positivity))
  have e1 : ∫ u in (-(T / 4))..(T / 4), (1 + u ^ 2)⁻¹ * ‖F T (u + ρ.im)‖ ^ 4 =
      ∫ u in (-(T / 4))..(T / 4), g (u + ρ.im) := by
    apply intervalIntegral.integral_congr; intro u _
    simp only [hg]
    rw [add_sub_cancel_right, mul_comm]
  rw [e1, intervalIntegral.integral_comp_add_right g ρ.im]
  have e2 : Q T ρ = ∫ t in T / 2..3 * T, g t := rfl
  rw [e2]
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
  · exact ae_of_all _ (fun t => by simp only [hg]; positivity)
  · exact hgc.intervalIntegrable _ _

lemma pointwise_bound {C₅ Cz T c γ : ℝ}
    (hΓ : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 → (1 + |z.im|) ^ 5 * ‖Complex.Gamma z‖ ≤ C₅)
    (hz : ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ Cz * (1 + |t|)) (hCz : 0 ≤ Cz)
    (hT4 : 4 ≤ T) (hc1 : -1 / 2 ≤ c) (hc0 : c < 0) (hcl1 : 1 ≤ -c * Real.log T)
    (hγ1 : T ≤ γ) (hγ2 : γ ≤ 2 * T) (u : ℝ) :
    ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * I)‖ * ‖F T (u + γ)‖ ≤
      (Icc (-(T / 4)) (T / 4)).indicator
        (fun u => C₅ * Real.log T * ((1 + u ^ 2)⁻¹ * ‖F T (u + γ)‖)) u +
      288 * C₅ * Cz / T * (1 + u ^ 2)⁻¹ := by
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  set L : ℝ := T / 4 with hL
  set E : ℝ := 288 * C₅ * Cz with hEdef
  set f : ℝ → ℝ := fun u => ‖F T (u + γ)‖ with hf
  have hf0 : ∀ u, 0 ≤ f u := fun u => norm_nonneg _
  set v : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹ with hv
  have hv0 : ∀ u, 0 < v u := fun u => by simp only [hv]; positivity
  have hE0 : 0 ≤ E := by
    have := (hΓ 1 (by norm_num) (by norm_num)); have := norm_nonneg (Complex.Gamma 1)
    rw [hEdef]; have : 0 ≤ C₅ := by nlinarith [pow_pos (show (0:ℝ) < 1 + |(1:ℂ).im| by positivity) 5]
    positivity
  show ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * I)‖ * f u ≤
      (Icc (-L) L).indicator (fun u => C₅ * Real.log T * (v u * f u)) u + E / T * v u
  have hgl := gamma_line C₅ hΓ hc1 hc0 u
  set g := ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * I)‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have hsc : -c ≤ ‖((c : ℂ) + (u : ℂ) * I)‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + (u : ℂ) * I)
    simp at this; linarith [neg_abs_le c, abs_of_neg hc0]
  have hsu : |u| ≤ ‖((c : ℂ) + (u : ℂ) * I)‖ := by
    have := Complex.abs_im_le_norm ((c : ℂ) + (u : ℂ) * I)
    simpa using this
  have hx1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
  have hx2 : 1 + u ^ 2 ≤ (1 + |u|) ^ 5 := by
    have h2 : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    calc 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := h2
      _ ≤ (1 + |u|) ^ 5 := pow_le_pow_right₀ hx1 (by norm_num)
  have hE' : 0 ≤ E / T * v u := by have := hv0 u; positivity
  by_cases hu : u ∈ Icc (-L) L
  · rw [Set.indicator_of_mem hu]
    have hgv : g ≤ C₅ * Real.log T * v u := by
      have hvpos := hv0 u
      simp only [hv]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have hs0 : 0 ≤ ‖((c : ℂ) + (u : ℂ) * I)‖ := norm_nonneg _
      calc g * (1 + u ^ 2) ≤ g * (1 + u ^ 2) * (-c * Real.log T) := by
            have : 0 ≤ g * (1 + u ^ 2) := by positivity
            nlinarith
        _ ≤ g * (1 + u ^ 2) * (‖((c : ℂ) + (u : ℂ) * I)‖ * Real.log T) := by
            gcongr
        _ = (g * ‖((c : ℂ) + (u : ℂ) * I)‖ * (1 + u ^ 2)) * Real.log T := by ring
        _ ≤ (g * ‖((c : ℂ) + (u : ℂ) * I)‖ * (1 + |u|) ^ 5) * Real.log T := by
            gcongr
        _ ≤ C₅ * Real.log T := by gcongr
    have := mul_le_mul_of_nonneg_right hgv (hf0 u)
    nlinarith
  · rw [Set.indicator_of_notMem hu, zero_add]
    have hLu : L < |u| := by
      by_contra hcon; push Not at hcon; exact hu (abs_le.mp hcon)
    set x : ℝ := 1 + |u| with hx
    have hu1 : 1 ≤ |u| := by linarith
    have hgx : g * x ^ 5 ≤ C₅ := by
      calc g * x ^ 5 ≤ g * ‖((c : ℂ) + (u : ℂ) * I)‖ * x ^ 5 := by
            have : 0 ≤ g * x ^ 5 := by positivity
            nlinarith
        _ ≤ C₅ := hgl
    have hfx : f u ≤ 18 * T * Cz * x := by
      have hb := F_bound Cz hz hT1 (u + γ)
      have hab : |u + γ| ≤ |u| + 2 * T := by
        refine (abs_add_le u γ).trans ?_
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ γ)]; linarith
      have h2T : 2 * T ≤ 8 * |u| := by rw [hL] at hLu; linarith
      calc f u ≤ 2 * T * (Cz * (1 + |u + γ|)) := hb
        _ ≤ 2 * T * (Cz * (9 * x)) := by
            gcongr; rw [hx]; linarith
        _ = 18 * T * Cz * x := by ring
    rw [hEdef]
    exact tail_alg hg0 hTpos hCz hgx hfx (by rw [hL] at hLu; exact hLu)

theorem detect_one : ∃ K T₀ : ℝ, 0 ≤ K ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
    1 / 2 + 1 / Real.log T ≤ σ → ∀ ρ ∈ S2 σ T,
      1 ≤ K * Real.log T ^ 4 * T ^ (1 - 2 * σ) * Q T ρ := by
  obtain ⟨C₅, hC₅, hΓ⟩ := gamma_decay (1 / 2) 1 (by norm_num) 5
  obtain ⟨Cz, hCz, hz⟩ := zeta_line_bound
  have hE0 : 0 ≤ 288 * C₅ * Cz := by positivity
  refine ⟨2187 / (16 * Real.pi) * C₅ ^ 4, 4 + 3 * (288 * C₅ * Cz), by positivity,
    by linarith, ?_⟩
  intro T hT σ hσ ρ hρ
  obtain ⟨hζ, hσβ, ⟨hγ1, hγ2⟩, hJ⟩ := hρ
  set E : ℝ := 288 * C₅ * Cz with hEdef
  have hT4 : 4 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hβ1 : ρ.re < 1 := by
    by_contra h; push Not at h; exact riemannZeta_ne_zero_of_one_le_re h hζ
  set c : ℝ := 1 / 2 - ρ.re with hc
  have hcL : 1 / Real.log T ≤ -c := by rw [hc]; linarith
  have hc0 : c < 0 := by have : 0 < 1 / Real.log T := by positivity
                         linarith
  have hc1 : -1 / 2 ≤ c := by rw [hc]; linarith
  have hcl1 : 1 ≤ -c * Real.log T := by
    rw [div_le_iff₀ hlog] at hcL; linarith
  set γ : ℝ := ρ.im with hγ
  set L : ℝ := T / 4 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  set P : ℝ := T ^ (c / 2) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hTpos _
  have hP1 : P ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by linarith)
  set f : ℝ → ℝ := fun u => ‖F T (u + γ)‖ with hf
  have hfc : Continuous f :=
    continuous_norm.comp ((F_cont T).comp (continuous_id.add continuous_const))
  have hf0 : ∀ u, 0 ≤ f u := fun u => norm_nonneg _
  set v : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹ with hv
  have hvc : Continuous v := by
    rw [hv]; exact Continuous.inv₀ (by fun_prop) (fun u => by positivity)
  have hv0 : ∀ u, 0 < v u := fun u => by simp only [hv]; positivity
  -- the integrand of `J`
  set G : ℝ → ℂ := fun u =>
    (T : ℂ) ^ ((((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I) / 2) *
      Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I) *
      Mf T (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)) *
      riemannZeta (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)) with hG
  have hJeq : J T ρ = (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, G u := rfl
  have hGnorm : ∀ u : ℝ, ‖G u‖ = P * (‖Complex.Gamma ((c : ℂ) + (u : ℂ) * I)‖ * f u) := by
    intro u
    have hρs : ρ + ((c : ℂ) + (u : ℂ) * I) = 1 / 2 + ((u + γ : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hc, hγ]
      ring
    simp only [hG, ← hc]
    rw [hρs, mul_assoc _ (Mf T _), norm_mul, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
    have hre : (((c : ℂ) + (u : ℂ) * I) / 2).re = c / 2 := by simp
    rw [hre, hf]
    simp only [F]
    ring
  -- pointwise majorant
  set h : ℝ → ℝ := fun u => P * ((Icc (-L) L).indicator
    (fun u => C₅ * Real.log T * (v u * f u)) u + E / T * v u) with hh
  have hGh : ∀ u, ‖G u‖ ≤ h u := by
    intro u
    rw [hGnorm u]
    exact mul_le_mul_of_nonneg_left (pointwise_bound hΓ hz hCz hT4 hc1 hc0 hcl1 hγ1 hγ2 u) hP0.le
  -- integrability and value of the majorant
  have hvf : Continuous (fun u => v u * f u) := hvc.mul hfc
  have hint1 : Integrable ((Icc (-L) L).indicator (fun u => C₅ * Real.log T * (v u * f u))) :=
    ((continuous_const.mul hvf).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hint2 : Integrable (fun u => E / T * v u) := integrable_inv_one_add_sq.const_mul _
  have hhint : Integrable h := (hint1.add hint2).const_mul P
  have hvint : ∫ u, v u = Real.pi := integral_univ_inv_one_add_sq
  have hhval : ∫ u, h u =
      P * (C₅ * Real.log T * (∫ u in (-L)..L, v u * f u) + E / T * Real.pi) := by
    simp only [hh]
    rw [integral_const_mul, integral_add hint1 hint2, integral_indicator measurableSet_Icc,
      integral_const_mul, integral_const_mul, hvint,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hnormJ : ‖J T ρ‖ ≤ 1 / (2 * Real.pi) * ∫ u, h u := by
    rw [hJeq, norm_mul]
    have hc2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hc2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ (fun u => norm_nonneg _)) hhint (ae_of_all _ hGh)
  -- `X I ≥ π/3`
  set I : ℝ := ∫ u in (-L)..L, v u * f u with hI
  set X : ℝ := P * C₅ * Real.log T with hX
  have hX0 : 0 < X := by positivity
  have hXI : Real.pi / 3 ≤ X * I := by
    have h1 := hJ.trans hnormJ
    rw [hhval] at h1
    have := xi_bound (P := P) (A := C₅ * Real.log T) hP0 hP1 hTpos hE0 (by linarith) h1
    rw [hX]; linarith [this, show P * (C₅ * Real.log T) * I = P * C₅ * Real.log T * I by ring]
  set Q' : ℝ := ∫ u in (-L)..L, v u * f u ^ 4 with hQ'
  have hamgm : ∀ a : ℝ, 0 ≤ a → 4 * a ^ 3 * I ≤ Q' + 3 * a ^ 4 * Real.pi :=
    fun a ha => amgm_int hfc hf0 (by linarith) ha
  have hQ'Q : Q' ≤ Q T ρ := Q_shift_le T ρ hTpos hγ1 hγ2
  have hQ'0 : 0 ≤ Q' := intervalIntegral.integral_nonneg (by linarith)
    (fun u _ => mul_nonneg (hv0 u).le (pow_nonneg (hf0 u) 4))
  have hkey := key_alg hX0 hXI hamgm
  have hP4 : P ^ 4 ≤ T ^ (1 - 2 * σ) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hc]; push_cast; linarith)
  have hX4 : X ^ 4 * Q' = C₅ ^ 4 * Real.log T ^ 4 * (P ^ 4 * Q') := by rw [hX]; ring
  have hpi := Real.pi_pos
  calc (1 : ℝ) ≤ 2187 / (16 * Real.pi) * (X ^ 4 * Q') := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    _ = 2187 / (16 * Real.pi) * C₅ ^ 4 * Real.log T ^ 4 * (P ^ 4 * Q') := by rw [hX4]; ring
    _ ≤ 2187 / (16 * Real.pi) * C₅ ^ 4 * Real.log T ^ 4 * (T ^ (1 - 2 * σ) * Q T ρ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hP4 hQ'Q hQ'0 (Real.rpow_nonneg hTpos.le _)
    _ = _ := by ring

end GuthMaynard.CitedZeros.L24.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
alias detect_one := GuthMaynard.CitedZeros.L24.PartD.detect_one

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-- Dyadic majorant of the Cauchy weight. -/
lemma pa_majorant (J : ℕ) (x : ℝ) (hx : |x| ≤ 2 ^ J) :
    (1 + x ^ 2)⁻¹ ≤ ∑ j ∈ Finset.range (J + 1),
      (if |x| ≤ 2 ^ j then (4 : ℝ) / 4 ^ j else 0) := by
  induction J with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero] at hx ⊢
    rw [if_pos hx]
    have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    linarith
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ ∑ j ∈ Finset.range (J + 1),
        (if |x| ≤ 2 ^ j then (4 : ℝ) / 4 ^ j else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    by_cases h : |x| ≤ 2 ^ J
    · have := ih h
      have : 0 ≤ (if |x| ≤ 2 ^ (J + 1) then (4 : ℝ) / 4 ^ (J + 1) else 0) := by
        rw [if_pos hx]; positivity
      linarith
    · rw [if_pos hx]
      push Not at h
      have h2 : (4 : ℝ) ^ J ≤ x ^ 2 := by
        rw [show (4 : ℝ) ^ J = (2 ^ J) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          ← sq_abs x]
        exact pow_le_pow_left₀ (by positivity) h.le 2
      have h3 : (1 + x ^ 2)⁻¹ ≤ (4 : ℝ) / 4 ^ (J + 1) := by
        rw [show (4 : ℝ) / 4 ^ (J + 1) = (4 ^ J)⁻¹ by rw [pow_succ]; field_simp]
        exact inv_anti₀ (by positivity) (by linarith)
      linarith

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
/-! ## Assembly (no `sorry` below) -/
theorem mult_nonneg (ρ : ℂ) : 0 ≤ mult ρ := Nat.cast_nonneg _

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-- `∑_ρ m_ρ (1+(t-γ)²)⁻¹ ≪ log T` for `t ∈ [T/2, 3T]`. -/
theorem weight_sum : ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ T : ℝ, T₀ ≤ T → ∀ G : Finset ℂ,
    (∀ ρ ∈ G, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T)) →
      ∀ t ∈ Set.Icc (T / 2) (3 * T), ∑ ρ ∈ G, mult ρ * (1 + (t - ρ.im) ^ 2)⁻¹ ≤ K * Real.log T := by
  obtain ⟨A, hA, hloc⟩ := local_count_finset
  refine ⟨32 * A, 7, by linarith, fun T hT G hG t ht => ?_⟩
  have hG' : ∀ ρ ∈ G, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => ⟨(hG ρ hρ).1, (hG ρ hρ).2.1⟩
  have hclose : ∀ ρ ∈ G, |ρ.im - t| ≤ 3 * T := by
    intro ρ hρ
    have := (hG ρ hρ).2.2
    rw [abs_le]; constructor <;> linarith [this.1, this.2, ht.1, ht.2]
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (3 * T) (by norm_num : (1 : ℝ) < 2)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog7 : Real.log (|t| + 3 * T + 3) ≤ 2 * Real.log T := by
    rw [abs_of_nonneg (by linarith [ht.1]), ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith [ht.1])
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [ht.2]
  -- each dyadic count
  have hcount : ∀ j : ℕ, ∑ ρ ∈ G.filter (fun ρ => |ρ.im - t| ≤ 2 ^ j), mult ρ ≤
      A * (2 ^ j + 1) * (2 * Real.log T) := by
    intro j
    have hsub : G.filter (fun ρ => |ρ.im - t| ≤ 2 ^ j) ⊆
        G.filter (fun ρ => |ρ.im - t| ≤ min (2 ^ j) (3 * T)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, le_min hρ.2 (hclose ρ hρ.1)⟩
    have hmin0 : 0 ≤ min ((2 : ℝ) ^ j) (3 * T) := le_min (by positivity) (by linarith)
    have hl0 : 0 ≤ Real.log (|t| + min ((2 : ℝ) ^ j) (3 * T) + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    calc ∑ ρ ∈ G.filter (fun ρ => |ρ.im - t| ≤ 2 ^ j), mult ρ
        ≤ ∑ ρ ∈ G.filter (fun ρ => |ρ.im - t| ≤ min (2 ^ j) (3 * T)), mult ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mult_nonneg _)
      _ ≤ A * (min (2 ^ j) (3 * T) + 1) * Real.log (|t| + min (2 ^ j) (3 * T) + 3) :=
          hloc G hG' t _ hmin0
      _ ≤ A * (2 ^ j + 1) * (2 * Real.log T) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [min_le_left ((2 : ℝ) ^ j) (3 * T)]) hA)
            _ hl0 (by positivity)
          refine le_trans (Real.log_le_log (by linarith [abs_nonneg t]) ?_) hlog7
          linarith [min_le_right ((2 : ℝ) ^ j) (3 * T)]
  calc ∑ ρ ∈ G, mult ρ * (1 + (t - ρ.im) ^ 2)⁻¹
      ≤ ∑ ρ ∈ G, mult ρ * ∑ j ∈ Finset.range (J + 1),
          (if |ρ.im - t| ≤ 2 ^ j then (4 : ℝ) / 4 ^ j else 0) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        apply mul_le_mul_of_nonneg_left _ (mult_nonneg ρ)
        rw [show (t - ρ.im) ^ 2 = (ρ.im - t) ^ 2 by ring]
        exact pa_majorant J _ ((hclose ρ hρ).trans hJ.le)
    _ = ∑ j ∈ Finset.range (J + 1),
          (∑ ρ ∈ G.filter (fun ρ => |ρ.im - t| ≤ 2 ^ j), mult ρ) * ((4 : ℝ) / 4 ^ j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ρ _
        split_ifs <;> simp
    _ ≤ ∑ j ∈ Finset.range (J + 1), (16 * A * Real.log T) * (1 / 2) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
          rw [← mul_pow]; norm_num
        have h2 : (0 : ℝ) < 2 ^ j := by positivity
        have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        calc (∑ ρ ∈ G.filter (fun ρ => |ρ.im - t| ≤ 2 ^ j), mult ρ) * ((4 : ℝ) / 4 ^ j)
            ≤ (A * (2 ^ j + 1) * (2 * Real.log T)) * ((4 : ℝ) / 4 ^ j) :=
              mul_le_mul_of_nonneg_right (hcount j) (by positivity)
          _ ≤ (A * (2 * 2 ^ j) * (2 * Real.log T)) * ((4 : ℝ) / 4 ^ j) := by
              gcongr; linarith
          _ = (16 * A * Real.log T) * (1 / 2) ^ j := by
              rw [h4, one_div_pow]; field_simp; ring
    _ = (16 * A * Real.log T) * ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (16 * A * Real.log T) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = 32 * A * Real.log T := by ring

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
alias weight_sum := GuthMaynard.CitedZeros.L24.PartA.weight_sum

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-- `t ↦ ‖F T t‖` is continuous (`ζ` is differentiable away from `1`). -/
theorem F_continuous (T : ℝ) : Continuous (fun t : ℝ => ‖F T t‖) := by
  have hz : Continuous (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have hc : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      hc.continuousAt
  have hm : Continuous (fun t : ℝ => Mf T (1 / 2 + (t : ℂ) * I)) := by
    unfold Mf
    refine continuous_finsetSum _ fun m hm => ?_
    have hm0 : (m : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hm).1; exact_mod_cast (by omega : m ≠ 0)
    exact continuous_const.mul
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).neg.const_cpow (Or.inl hm0))
  unfold F
  exact (hm.mul hz).norm

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24.PartA
open GuthMaynard.CitedZeros.L24
/-- Interchange: `∑ m_ρ Q(ρ) = ∫ ‖F‖^4 ∑ m_ρ (1+(t-γ)²)⁻¹ ≤ W ∫ ‖F‖^4`. -/
theorem sum_Q_le (T W : ℝ) (hT : 0 < T) (G : Finset ℂ) (hm : ∀ ρ ∈ G, 0 ≤ mult ρ)
    (hW : ∀ t ∈ Set.Icc (T / 2) (3 * T), ∑ ρ ∈ G, mult ρ * (1 + (t - ρ.im) ^ 2)⁻¹ ≤ W) :
    ∑ ρ ∈ G, mult ρ * Q T ρ ≤ W * ∫ t in T / 2..3 * T, ‖F T t‖ ^ 4 := by
  have hF := F_continuous T
  have hw : ∀ ρ : ℂ, Continuous (fun t : ℝ => (1 + (t - ρ.im) ^ 2)⁻¹) := fun ρ =>
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hint : ∀ ρ : ℂ, IntervalIntegrable
      (fun t : ℝ => mult ρ * (‖F T t‖ ^ 4 * (1 + (t - ρ.im) ^ 2)⁻¹)) volume (T / 2) (3 * T) :=
    fun ρ => (continuous_const.mul ((hF.pow 4).mul (hw ρ))).intervalIntegrable _ _
  have heq : ∑ ρ ∈ G, mult ρ * Q T ρ =
      ∫ t in T / 2..3 * T, ∑ ρ ∈ G, mult ρ * (‖F T t‖ ^ 4 * (1 + (t - ρ.im) ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_finsetSum (fun ρ _ => hint ρ)]
    apply Finset.sum_congr rfl
    intro ρ _
    unfold Q
    rw [intervalIntegral.integral_const_mul]
  rw [heq, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (continuous_finsetSum _ fun ρ _ =>
      continuous_const.mul ((hF.pow 4).mul (hw ρ))).intervalIntegrable _ _
  · exact (continuous_const.mul (hF.pow 4)).intervalIntegrable _ _
  · intro t ht
    have h1 : ∑ ρ ∈ G, mult ρ * (‖F T t‖ ^ 4 * (1 + (t - ρ.im) ^ 2)⁻¹) =
        ‖F T t‖ ^ 4 * ∑ ρ ∈ G, mult ρ * (1 + (t - ρ.im) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring
    rw [h1, mul_comm W]
    exact mul_le_mul_of_nonneg_left (hW t ht) (by positivity)

end GuthMaynard.CitedZeros.L24.PartA
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.L24
alias sum_Q_le := GuthMaynard.CitedZeros.L24.PartA.sum_Q_le

/-- The finite-set bound in the main range `σ ≥ 1/2 + 1/log T`. -/
theorem main_finset : ∃ A C T₀ : ℝ, 0 ≤ C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
    1 / 2 + 1 / Real.log T ≤ σ → ∀ G : Finset ℂ, (↑G : Set ℂ) ⊆ S2 σ T →
      ∑ ρ ∈ G, mult ρ ≤ C * T ^ (2 - 2 * σ) * Real.log T ^ A := by
  obtain ⟨A₄, C₄, T₄, h4⟩ := GuthMaynard.maynard_pratt_twisted_fourth_moment
  obtain ⟨K, T₁, hK, hT₁, hdet⟩ := detect_one
  obtain ⟨W, T₂, hW, hws⟩ := weight_sum
  refine ⟨A₄ + 5, K * W * |C₄|, max (max T₁ T₂) (max T₄ 3), by positivity, by
    simp, fun T hT σ hσ G hG => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT4 : T₄ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hTpos : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hT3
  have hlog0 : 0 < Real.log T := by linarith
  -- the moment
  have hmom : ∫ t in T / 2..3 * T, ‖F T t‖ ^ 4 ≤ C₄ * T * Real.log T ^ A₄ := h4 T hT4
  -- each zero: 1 ≤ K log^4 T^{1-2σ} Q
  have hzero : ∀ ρ ∈ G, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) := by
    intro ρ hρ
    have h := hG hρ
    refine ⟨h.1, ?_, h.2.2.1⟩
    exact (zero_re_pos_lt_one h.1 (by have := h.2.2.1.1; intro h0; linarith)).1
  have hwt := hws T hT2 G hzero
  have hsQ := sum_Q_le T (W * Real.log T) hTpos G (fun ρ _ => mult_nonneg ρ) hwt
  set P : ℝ := K * Real.log T ^ 4 * T ^ (1 - 2 * σ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hsum1 : ∑ ρ ∈ G, mult ρ ≤ ∑ ρ ∈ G, mult ρ * (P * Q T ρ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    have := hdet T hT1 σ hσ ρ (hG hρ)
    nlinarith [mult_nonneg ρ]
  have hsum2 : ∑ ρ ∈ G, mult ρ * (P * Q T ρ) = P * ∑ ρ ∈ G, mult ρ * Q T ρ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring
  have hint0 : 0 ≤ ∫ t in T / 2..3 * T, ‖F T t‖ ^ 4 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hTT : T ^ (1 - 2 * σ) * T = T ^ (2 - 2 * σ) := by
    rw [show (2 - 2 * σ) = (1 - 2 * σ) + 1 by ring, Real.rpow_add hTpos, Real.rpow_one]
  have hlogpow : Real.log T ^ 4 * Real.log T * Real.log T ^ A₄ = Real.log T ^ (A₄ + 5) := by
    rw [Real.rpow_add hlog0, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc ∑ ρ ∈ G, mult ρ ≤ P * ∑ ρ ∈ G, mult ρ * Q T ρ := hsum1.trans_eq hsum2
    _ ≤ P * ((W * Real.log T) * ∫ t in T / 2..3 * T, ‖F T t‖ ^ 4) :=
        mul_le_mul_of_nonneg_left hsQ hP0
    _ ≤ P * ((W * Real.log T) * (|C₄| * T * Real.log T ^ A₄)) := by
        apply mul_le_mul_of_nonneg_left _ hP0
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hmom.trans ?_
        gcongr
        exact le_abs_self _
    _ = K * W * |C₄| * (T ^ (1 - 2 * σ) * T) *
          (Real.log T ^ 4 * Real.log T * Real.log T ^ A₄) := by rw [hP]; ring
    _ = K * W * |C₄| * T ^ (2 - 2 * σ) * Real.log T ^ (A₄ + 5) := by
        rw [hTT, hlogpow]

/-- The finite-set bound in every range. -/
theorem all_finset : ∃ A C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
    ∀ G : Finset ℂ, (↑G : Set ℂ) ⊆ S2 σ T →
      ∑ ρ ∈ G, mult ρ ≤ C * T ^ (2 - 2 * σ) * Real.log T ^ A := by
  obtain ⟨A₁, C₁, T₁, hC₁, hT₁, hmain⟩ := main_finset
  obtain ⟨C₀, T₀, hC₀, htriv⟩ := trivial_count
  refine ⟨max A₁ 1, C₁ + C₀ * Real.exp 2, max (max T₁ T₀) 3, by positivity,
    fun T hT σ G hG => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT0 : T₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hT3
  have hlog0 : 0 < Real.log T := by linarith
  have hpowA : ∀ a : ℝ, a ≤ max A₁ 1 → Real.log T ^ a ≤ Real.log T ^ (max A₁ 1) :=
    fun a ha => Real.rpow_le_rpow_of_exponent_le hlog ha
  have hTp : 0 ≤ T ^ (2 - 2 * σ) := Real.rpow_nonneg hTpos.le _
  have hLp : 0 ≤ Real.log T ^ (max A₁ 1) := Real.rpow_nonneg hlog0.le _
  by_cases hσ : 1 / 2 + 1 / Real.log T ≤ σ
  · calc ∑ ρ ∈ G, mult ρ ≤ C₁ * T ^ (2 - 2 * σ) * Real.log T ^ A₁ := hmain T hT1 σ hσ G hG
      _ ≤ C₁ * T ^ (2 - 2 * σ) * Real.log T ^ (max A₁ 1) := by
          gcongr; exact le_max_left _ _
      _ ≤ (C₁ + C₀ * Real.exp 2) * T ^ (2 - 2 * σ) * Real.log T ^ (max A₁ 1) := by
          gcongr; nlinarith [Real.exp_pos 2]
  · push Not at hσ
    have hG' : ∀ ρ ∈ G, riemannZeta ρ = 0 ∧ ρ.im ∈ Set.Icc T (2 * T) := fun ρ hρ =>
      ⟨(hG hρ).1, (hG hρ).2.2.1⟩
    have h1 := htriv T hT0 G hG'
    -- T ≤ e² T^{2-2σ}
    have hexp : T ≤ Real.exp 2 * T ^ (2 - 2 * σ) := by
      have hge : 1 - 2 / Real.log T ≤ 2 - 2 * σ := by
        have : 2 * σ < 1 + 2 / Real.log T := by
          have := mul_lt_mul_of_pos_left hσ (by norm_num : (0 : ℝ) < 2)
          rw [mul_add] at this; field_simp at this ⊢; linarith
        linarith
      have hpw : T ^ (2 / Real.log T) = Real.exp 2 := by
        rw [Real.rpow_def_of_pos hTpos]
        congr 1
        field_simp
      calc T = Real.exp 2 * T ^ (1 - 2 / Real.log T) := by
            rw [Real.rpow_sub hTpos, Real.rpow_one, hpw]
            field_simp
        _ ≤ Real.exp 2 * T ^ (2 - 2 * σ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hge)
              (Real.exp_pos 2).le
    have hl1 : Real.log T ≤ Real.log T ^ (max A₁ 1) := by
      calc Real.log T = Real.log T ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := hpowA 1 (le_max_right _ _)
    calc ∑ ρ ∈ G, mult ρ ≤ C₀ * T * Real.log T := h1
      _ ≤ C₀ * (Real.exp 2 * T ^ (2 - 2 * σ)) * Real.log T ^ (max A₁ 1) := by
          gcongr
      _ ≤ (C₁ + C₀ * Real.exp 2) * T ^ (2 - 2 * σ) * Real.log T ^ (max A₁ 1) := by
          nlinarith [mul_nonneg hTp hLp, mul_nonneg (mul_nonneg hTp hLp) hC₁]

/-- **Maynard–Pratt, Lemma 24**, in the form of the published statement. -/
theorem maynard_pratt_card_typeII_zeros_le_dev :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
            let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
            (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖},
          analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) := by
  obtain ⟨A, C, T₀, _, h⟩ := all_finset
  refine ⟨A, C, T₀, fun T hT σ => ?_⟩
  exact count_le_of_finset_bound (S2 σ T) _ (h T hT σ)

end GuthMaynard.CitedZeros.L24
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open GuthMaynard
open GuthMaynard.CitedZeros
open GuthMaynard.CitedZeros.L24
theorem solution :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
            let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
            (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖},
          analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) := by
  exact GuthMaynard.CitedZeros.L24.maynard_pratt_card_typeII_zeros_le_dev
end
