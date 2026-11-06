-- Prove2me | solution 1 for LindelofHypothesis.ingham_density_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:29:55.061066+00:00
-- url     : https://prove2.me/submissions/6c6c5532-18ac-40c7-adad-9cd90827fdcd

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_moment_bound_of_k_le_two
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
/-!
# Ingham's zero-density estimate `N(σ,T) ≪ T^{3(1-σ)/(2-σ)+ε}`: blueprint

Montgomery's method (zero detection by a mollified Dirichlet series, large values for Type I
zeros, the fourth moment of `ζ` for Type II zeros), on top of the cited results
* `LindelofHypothesis.moment_bound_of_k_le_two` (the fourth moment, `k = 2`),
* `ArtinPrimitiveRoots.dirichlet_mean_value` (continuous mean value theorem),
* `Zeta23.RvM.zeta_local_zero_count` (`≪ log` zeros per unit window).

Parameters at height `T` (zeros with ordinate in `[T, 2T]`), for `1/2 < σ < 1`:
`X = T` (mollifier length), `Y = Ys σ T = T^{3/(2(2-σ))} ∈ [T, T^{3/2}]`, `L = T^η`,
Type I range `T < n ≤ Y T^η`.

Every lemma below is `sorry`; the assembly (`typeI_count`, `typeII_count`, `window_bound`,
`ingham_dev`) is sorry-free modulo them.
-/
/-! ## Definitions -/
/-- `a_X(n) = ∑_{d ∣ n, d ≤ X} μ(d)`. -/
noncomputable def aX (X : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X), (ArithmeticFunction.moebius d : ℂ)

/-- The mollifier `M_X(s) = ∑_{m ≤ X} μ(m) m^{-s}`. -/
noncomputable def molli (X : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- `Y = T^{3/(2(2-σ))}`. -/
noncomputable def Ys (σ T : ℝ) : ℝ := T ^ (3 / (2 * (2 - σ)))

/-- The Type I sum `∑_{X < n ≤ Y T^η} a_X(n) e^{-n/Y} n^{-s}` with `X = T`. -/
noncomputable def SI (T Y η : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊T⌋₊ ⌊Y * T ^ η⌋₊,
    aX T n * (Real.exp (-(n : ℝ) / Y) : ℂ) * (n : ℂ) ^ (-s)

/-- Type I zero: the Type I sum is large. -/
def IsTypeI (T Y η : ℝ) (s : ℂ) : Prop := 1 / 2 ≤ ‖SI T Y η s‖

/-- The Type II kernel `|Γ(1/2-β+iu)| · |M_T ζ(1/2+i(γ+u))|`. -/
noncomputable def kII (T β γ u : ℝ) : ℝ :=
  ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ *
    ‖molli T (1 / 2 + ((γ + u : ℝ) : ℂ) * I) * riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖

/-- Type II zero: the truncated line integral is large. -/
def IsTypeII (σ T Y η : ℝ) (s : ℂ) : Prop :=
  Y ^ (σ - 1 / 2) ≤ ∫ u in -(T ^ η)..(T ^ η), kII T s.re s.im u

/-- `I(ρ) = ∑ a_X(n) e^{-n/Y} n^{-ρ}`. -/
noncomputable def Iser (X Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, aX X n * (Real.exp (-(n : ℝ) / Y) : ℂ) * (n : ℂ) ^ (-ρ)

/-- `(1/2π) ∫ Y^s Γ(s) M_X(ρ+s) ζ(ρ+s) du` on `Re s = x`. -/
noncomputable def lineInt (X Y : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
    (Y : ℂ) ^ ((x : ℂ) + (u : ℂ) * I) * Complex.Gamma ((x : ℂ) + (u : ℂ) * I) *
      molli X (ρ + ((x : ℂ) + (u : ℂ) * I)) * riemannZeta (ρ + ((x : ℂ) + (u : ℂ) * I))

/-- The residue at `s = 1 - ρ`: `Y^{1-ρ} Γ(1-ρ) M_X(1)`. -/
noncomputable def Res (X Y : ℝ) (ρ : ℂ) : ℂ :=
  (Y : ℂ) ^ (1 - ρ) * Complex.Gamma (1 - ρ) * molli X 1

/-- Zeros in a set `S`, counted with multiplicity, in `ℕ∞` (as in `zeroDensityCount`). -/
noncomputable def zc (S : Set ℂ) : ℕ∞ := ∑' s : S, analyticOrderAt riemannZeta (s : ℂ)

/-- Zeros with `Re ≥ σ` and ordinate in `[T, 2T]`. -/
def win (σ T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ 2 * T}

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
lemma pc_enat_summable {β : Type*} (f : β → ℕ∞) : Summable f :=
  ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩

lemma pc_not_analytic_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hc : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have h2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1)
      (𝓝 ((1 - 1) * riemannZeta 1)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique riemannZeta_residue_one h2
  simp at this

lemma pc_order_ne_top (ρ : ℂ) : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  by_cases h : ρ = 1
  · subst h; rw [analyticOrderAt_of_not_analyticAt pc_not_analytic_one]; exact ENat.zero_ne_top
  · exact Zeta23.analyticOrderAt_riemannZeta_ne_top h

lemma pc_order_eq (ρ : ℂ) : ((analyticOrderAt riemannZeta ρ : ℕ∞) : ℝ≥0∞) =
    ENNReal.ofReal ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (pc_order_ne_top ρ)
  rw [← hn]; simp

lemma pc_zc_eq (S : Set ℂ) : (zc S : ℝ≥0∞) =
    ∑' s : S, ENNReal.ofReal ((analyticOrderAt riemannZeta (s : ℂ)).toNat : ℝ) := by
  unfold zc
  rw [show ((∑' s : S, analyticOrderAt riemannZeta (s : ℂ) : ℕ∞) : ℝ≥0∞) =
      ENat.toENNRealRingHom (∑' s : S, analyticOrderAt riemannZeta (s : ℂ)) from rfl,
    (pc_enat_summable _).map_tsum ENat.toENNRealRingHom ENat.continuous_toENNReal]
  exact tsum_congr fun s => pc_order_eq s

theorem count_union (S A B : Set ℂ) (h : S ⊆ A ∪ B) : zc S ≤ zc A + zc B := by
  rw [← ENat.toENNReal_le, ENat.toENNReal_add, pc_zc_eq, pc_zc_eq, pc_zc_eq]
  exact (ENNReal.tsum_mono_subtype (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) h).trans
    (ENNReal.tsum_union_le (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) A B)

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
/-! ## Counting primitives -/
alias count_union := GuthMaynard.CitedZeros.Ing.PartC.count_union

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem count_le_of_finset_bound (S : Set ℂ) (K : ℝ)
    (h : ∀ F : Finset ℂ, (↑F : Set ℂ) ⊆ S →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤ K) :
    (zc S : ℝ≥0∞) ≤ ENNReal.ofReal K := by
  rw [pc_zc_eq, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun u => ?_
  have hsub : (↑(u.map (Function.Embedding.subtype _)) : Set ℂ) ⊆ S := by
    intro x hx
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have := h _ hsub
  rw [Finset.sum_map] at this
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal this

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
alias count_le_of_finset_bound := GuthMaynard.CitedZeros.Ing.PartC.count_le_of_finset_bound

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
lemma pc_zc_biUnion {ι : Type*} (S : Set ℂ) (s : Finset ι) (A : ι → Set ℂ)
    (h : S ⊆ ⋃ i ∈ s, A i) : (zc S : ℝ≥0∞) ≤ ∑ i ∈ s, (zc (A i) : ℝ≥0∞) := by
  rw [pc_zc_eq]
  simp_rw [pc_zc_eq]
  exact (ENNReal.tsum_mono_subtype (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) h).trans
    (ENNReal.tsum_biUnion_le (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) s A)

lemma pc_zeta_conj_iff (ρ : ℂ) : riemannZeta ((starRingEnd ℂ) ρ) = 0 ↔ riemannZeta ρ = 0 := by
  by_cases h : ρ = 1
  · subst h; simp
  · rw [Zeta23.riemannZeta_conj h]; simp

lemma pc_order_conj (ρ : ℂ) :
    analyticOrderAt riemannZeta ((starRingEnd ℂ) ρ) = analyticOrderAt riemannZeta ρ := by
  by_cases h : ρ = 1
  · subst h; simp
  · exact Zeta23.analyticOrderAt_zeta_conj h

theorem conj_win (σ T : ℝ) :
    zc {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -(2 * T) ≤ ρ.im ∧ ρ.im ≤ -T} = zc (win σ T) := by
  unfold zc
  let e : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -(2 * T) ≤ ρ.im ∧ ρ.im ≤ -T} ≃ win σ T :=
    { toFun := fun x => ⟨(starRingEnd ℂ) x.1, by
        obtain ⟨h1, h2, h3, h4⟩ := x.2
        refine ⟨(pc_zeta_conj_iff _).2 h1, ?_, ?_, ?_⟩ <;> simp <;> linarith⟩
      invFun := fun x => ⟨(starRingEnd ℂ) x.1, by
        obtain ⟨h1, h2, h3, h4⟩ := x.2
        refine ⟨(pc_zeta_conj_iff _).2 h1, ?_, ?_, ?_⟩ <;> simp <;> linarith⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← e.tsum_eq]
  exact tsum_congr fun x => (pc_order_conj x.1).symm

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem low_finite (M : ℝ) :
    zc {ρ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im| ≤ M} ≠ ⊤ := by
  have hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im| ≤ M}.Finite := by
    refine (Zeta23.zetaSeam.finite_window (-M - 1) M).subset ?_
    rintro ρ ⟨h1, h2, h3⟩
    have hre : ρ.re < 1 := by
      by_contra hc
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h1
    refine ⟨⟨h1, by linarith, hre⟩, ?_, (abs_le.1 h3).2⟩
    linarith [(abs_le.1 h3).1]
  have := count_le_of_finset_bound _
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) (fun F hF =>
      Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => hfin.mem_toFinset.2 (hF hx))
        (fun _ _ _ => Nat.cast_nonneg _))
  intro htop
  rw [htop] at this
  simp at this

/-! ## Local count, separated covers -/
lemma pc_zerosIn_finite (a b : ℝ) : (Zeta23.zerosIn a b).Finite := Zeta23.zetaSeam.finite_window a b

lemma pc_Ncount_eq (a b : ℝ) : (Zeta23.Ncount a b : ℝ) =
    ∑ ρ ∈ (pc_zerosIn_finite a b).toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (pc_zerosIn_finite a b)]
  push_cast; rfl

lemma pc_window_sum_le (F : Finset ℂ) (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re) (a b : ℝ) :
    ∑ ρ ∈ F.filter (fun ρ => a < ρ.im ∧ ρ.im ≤ b), ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
      Zeta23.Ncount a b := by
  rw [pc_Ncount_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ.1
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨h1, h2, ?_⟩, hρ.2.1, hρ.2.2⟩
    by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h1
  · intros; positivity

lemma pc_ceil_sub_one {x : ℝ} (hx : 0 < x) :
    (((⌈x⌉₊ - 1 : ℕ) : ℝ) < x) ∧ x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  rw [Nat.cast_sub h1]
  push_cast
  constructor
  · linarith [Nat.ceil_lt_add_one hx.le]
  · linarith [Nat.le_ceil x]

lemma pc_log_shift {x : ℝ} (hx : 3 ≤ x) : Real.log (x + 1) ≤ 2 * Real.log x := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by linarith)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith

theorem local_count_finset : ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Finset ℂ,
    (∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re) → ∀ t H : ℝ, 0 ≤ H →
      ∑ ρ ∈ F.filter (fun ρ => |ρ.im - t| ≤ H), ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
        A * (H + 1) * Real.log (|t| + H + 3) := by
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
      obtain ⟨c1, c2⟩ := pc_ceil_sub_one hx
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
      _ ≤ Zeta23.Ncount (a + j) (a + j + 1) := pc_window_sum_le F hF _ _
      _ ≤ A₀ * Real.log (|a + j| + 3) := hA (a + j)
      _ ≤ A₀ * (2 * Real.log (|t| + H + 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          refine le_trans (Real.log_le_log (by positivity) (?_ : |a + j| + 3 ≤ (|t| + H + 3) + 1))
            (pc_log_shift (by linarith [abs_nonneg t]))
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

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem exists_separated_cover (F : Finset ℂ) :
    ∃ P ⊆ F, (∀ s ∈ P, ∀ s' ∈ P, s ≠ s' → 1 ≤ |s.im - s'.im|) ∧
      ∀ ρ ∈ F, ∃ p ∈ P, |ρ.im - p.im| ≤ 1 := by
  induction F using Finset.strongInduction with
  | H F ih =>
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ⟨∅, by simp, by simp, by simp [hF]⟩
    obtain ⟨p, hpF, hpmin⟩ := F.exists_min_image Complex.im hF
    set F' := F.filter (fun ρ => p.im + 1 ≤ ρ.im) with hF'
    have hss : F' ⊂ F := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : p ∈ F' := h ▸ hpF
      rw [hF', Finset.mem_filter] at this
      linarith [this.2]
    obtain ⟨P', hP'F, hsep, hcov⟩ := ih F' hss
    have hpP' : p ∉ P' := fun h => by
      have := hP'F h
      rw [hF', Finset.mem_filter] at this
      linarith [this.2]
    have hP'big : ∀ q ∈ P', p.im + 1 ≤ q.im := fun q hq => by
      have := hP'F hq
      rw [hF', Finset.mem_filter] at this
      exact this.2
    refine ⟨insert p P', ?_, ?_, ?_⟩
    · exact Finset.insert_subset hpF (hP'F.trans (Finset.filter_subset _ _))
    · intro s hs s' hs' hne
      rw [Finset.mem_insert] at hs hs'
      rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
      · exact absurd rfl hne
      · have := hP'big s' hs'; exact le_abs.2 (Or.inr (by linarith))
      · have := hP'big s hs; exact le_abs.2 (Or.inl (by linarith))
      · exact hsep s hs s' hs' hne
    · intro ρ hρ
      by_cases h : p.im + 1 ≤ ρ.im
      · obtain ⟨q, hq, hq'⟩ := hcov ρ (by rw [hF', Finset.mem_filter]; exact ⟨hρ, h⟩)
        exact ⟨q, Finset.mem_insert_of_mem hq, hq'⟩
      · refine ⟨p, Finset.mem_insert_self _ _, ?_⟩
        have := hpmin ρ hρ
        rw [abs_le]; constructor <;> linarith

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

/-- No zeros with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`). -/
theorem count_re_ge_one (σ T : ℝ) (hσ : 1 ≤ σ) :
    LindelofHypothesis.zeroDensityCount σ T = 0 := by
  unfold LindelofHypothesis.zeroDensityCount
  have : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} = ∅ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h hs
    exact absurd h (riemannZeta_ne_zero_of_one_le_re (le_trans hσ hs))
  rw [this]
  simp

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
/-! ## Window at `σ = 1/2` and dyadic assembly -/
theorem window_bound_half (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      (zc (win (1 / 2) T) : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (1 + ε)) := by
  obtain ⟨A, hA, hloc⟩ := local_count_finset
  refine ⟨A * 2 * (5 ^ ε / ε), 1, by positivity, fun T hT => ?_⟩
  apply count_le_of_finset_bound
  intro F hF
  have hF' : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => by
    obtain ⟨h1, h2, _, _⟩ := hF hρ
    exact ⟨h1, by linarith⟩
  have hfilt : F.filter (fun ρ => |ρ.im - 3 * T / 2| ≤ T / 2) = F := by
    rw [Finset.filter_eq_self]
    intro ρ hρ
    obtain ⟨_, _, h3, h4⟩ := hF hρ
    rw [abs_le]; constructor <;> linarith
  have h := hloc F hF' (3 * T / 2) (T / 2) (by linarith)
  rw [hfilt, abs_of_nonneg (by linarith)] at h
  refine h.trans ?_
  have hT0 : 0 < T := by linarith
  have hlog : Real.log (3 * T / 2 + T / 2 + 3) ≤ (5 * T) ^ ε / ε :=
    (Real.log_le_log (by linarith) (by linarith : 3 * T / 2 + T / 2 + 3 ≤ 5 * T)).trans
      (Real.log_le_rpow_div (by linarith) hε)
  rw [Real.mul_rpow (by norm_num) hT0.le] at hlog
  have hpow : T ^ (1 + ε) = T * T ^ ε := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  rw [hpow]
  have hl0 : 0 ≤ Real.log (3 * T / 2 + T / 2 + 3) := Real.log_nonneg (by linarith)
  calc A * (T / 2 + 1) * Real.log (3 * T / 2 + T / 2 + 3)
      ≤ A * (2 * T) * (5 ^ ε * T ^ ε / ε) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA) hlog hl0 (by positivity)
    _ = A * 2 * (5 ^ ε / ε) * (T * T ^ ε) := by ring

lemma pc_floor_logb {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ ⌊Real.logb 2 x⌋₊ ≤ x ∧ x < (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ + 1) := by
  have hl : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hx0 : 0 < x := by linarith
  constructor
  · have h := Nat.floor_le hl
    calc (2 : ℝ) ^ ⌊Real.logb 2 x⌋₊ = (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) := by
          rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (Real.logb 2 x) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
      _ = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  · have h := Nat.lt_floor_add_one (Real.logb 2 x)
    calc x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
      _ < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
      _ = (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ + 1) := by
          rw [← Real.rpow_natCast]; push_cast; rfl

theorem dyadic_assembly (σ a : ℝ) (hσ : 1 / 2 ≤ σ) (ha : 0 ≤ a)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      (zc (win σ T) : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (a + ε))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ T in atTop,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (a + ε)) := by
  intro ε hε
  obtain ⟨C, T₀, hC, hb⟩ := h (ε / 2) (by linarith)
  set T₁ := max T₀ 1 with hT₁
  have hT₁1 : 1 ≤ T₁ := le_max_right _ _
  have hT₁0 : T₀ ≤ T₁ := le_max_left _ _
  set L : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im| ≤ 2 * T₁} with hL
  have hLne : (zc L : ℝ≥0∞) ≠ ⊤ := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (low_finite (2 * T₁))
    rw [← hn]; simp
  set Z₀ := (zc L : ℝ≥0∞).toReal with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := ENNReal.toReal_nonneg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z₀ + 2 * C * (2 / (ε * Real.log 2)), ?_⟩
  filter_upwards [eventually_ge_atTop T₁] with T hT
  have hT1 : 1 ≤ T := hT₁1.trans hT
  have hT0 : 0 < T := by linarith
  set K := ⌊Real.logb 2 (T / T₁)⌋₊ with hK
  have hTT : 1 ≤ T / T₁ := by rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨hK1, hK2⟩ := pc_floor_logb hTT
  rw [← hK] at hK1 hK2
  -- the windows
  let W : ℕ → Set ℂ := fun k => win σ (T / 2 ^ (k + 1))
  let W' : ℕ → Set ℂ := fun k =>
    {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -(2 * (T / 2 ^ (k + 1))) ≤ ρ.im ∧ ρ.im ≤ -(T / 2 ^ (k + 1))}
  have hcover : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} ⊆
      L ∪ ⋃ k ∈ Finset.range K, (W k ∪ W' k) := by
    rintro s ⟨h1, h2, h3⟩
    by_cases hs : |s.im| ≤ 2 * T₁
    · exact Or.inl ⟨h1, by linarith, hs⟩
    right
    push Not at hs
    set y := |s.im| with hy
    have hy0 : 0 < y := by linarith
    have hTy : 1 ≤ T / y := by rw [le_div_iff₀ hy0]; linarith
    obtain ⟨hk1, hk2⟩ := pc_floor_logb hTy
    set k := ⌊Real.logb 2 (T / y)⌋₊ with hk
    have hkK : k < K := by
      have : (2 : ℝ) ^ k < 2 ^ K := by
        have e1 : T / y < T / (2 * T₁) := div_lt_div_of_pos_left hT0 (by linarith) hs
        have e2 : T / (2 * T₁) = (T / T₁) / 2 := by field_simp
        rw [pow_succ] at hK2
        linarith
      exact (pow_lt_pow_iff_right₀ (by norm_num)).1 this
    rw [Set.mem_iUnion₂]
    refine ⟨k, Finset.mem_range.2 hkK, ?_⟩
    have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have hlo : T / 2 ^ (k + 1) ≤ y := by
      rw [div_le_iff₀ hp]; rw [div_lt_iff₀ hy0] at hk2; linarith
    have hhi : y ≤ 2 * (T / 2 ^ (k + 1)) := by
      rw [pow_succ, ← mul_div_assoc, mul_comm 2 T, mul_div_mul_right _ _ (by norm_num : (2:ℝ) ≠ 0),
        le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hy0] at hk1; linarith
    rcases le_or_gt 0 s.im with him | him
    · rw [abs_of_nonneg him] at hy
      exact Or.inl ⟨h1, h2, by linarith, by linarith⟩
    · rw [abs_of_neg him] at hy
      exact Or.inr ⟨h1, h2, by linarith, by linarith⟩
  have hwin : ∀ k ∈ Finset.range K, (zc (W k ∪ W' k) : ℝ≥0∞) ≤
      2 * ENNReal.ofReal (C * T ^ (a + ε / 2)) := by
    intro k hk
    have hk' : k + 1 ≤ K := Finset.mem_range.1 hk
    have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have hTk : T₁ ≤ T / 2 ^ (k + 1) := by
      rw [le_div_iff₀ hp]
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hk'
      rw [le_div_iff₀ (by linarith)] at hK1
      nlinarith
    have hTk' : T / 2 ^ (k + 1) ≤ T := div_le_self hT0.le (one_le_pow₀ (by norm_num))
    have hbk := hb _ (hT₁0.trans hTk)
    have hmono : ENNReal.ofReal (C * (T / 2 ^ (k + 1)) ^ (a + ε / 2)) ≤
        ENNReal.ofReal (C * T ^ (a + ε / 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hTk' (by linarith)) hC)
    have hu := count_union (W k ∪ W' k) (W k) (W' k) le_rfl
    have hc : zc (W' k) = zc (W k) := conj_win σ _
    calc (zc (W k ∪ W' k) : ℝ≥0∞) ≤ ((zc (W k) + zc (W' k) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr hu
      _ = 2 * (zc (W k) : ℝ≥0∞) := by rw [hc, ENat.toENNReal_add]; ring
      _ ≤ 2 * ENNReal.ofReal (C * T ^ (a + ε / 2)) := by
          gcongr; exact hbk.trans hmono
  have hKlog : (K : ℝ) ≤ T ^ (ε / 2) * (2 / (ε * Real.log 2)) := by
    have e1 : (K : ℝ) ≤ Real.logb 2 (T / T₁) := Nat.floor_le (Real.logb_nonneg (by norm_num) hTT)
    have e2 : Real.logb 2 (T / T₁) ≤ Real.logb 2 T :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (div_le_self hT0.le hT₁1)
    have e3 : Real.log T ≤ T ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hT0.le (by linarith)
    rw [Real.logb] at e2
    have e4 : Real.log T / Real.log 2 ≤ T ^ (ε / 2) / (ε / 2) / Real.log 2 :=
      div_le_div_of_nonneg_right e3 hl2.le
    calc (K : ℝ) ≤ _ := e1.trans (e2.trans e4)
      _ = T ^ (ε / 2) * (2 / (ε * Real.log 2)) := by field_simp
  have hpow1 : 1 ≤ T ^ (a + ε) := Real.one_le_rpow hT1 (by linarith)
  have hpow2 : T ^ (a + ε / 2) * T ^ (ε / 2) = T ^ (a + ε) := by
    rw [← Real.rpow_add hT0]; ring_nf
  have hpos : 0 ≤ T ^ (a + ε / 2) := by positivity
  calc (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞)
      = (zc {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} : ℝ≥0∞) := rfl
    _ ≤ ((zc L + zc (⋃ k ∈ Finset.range K, (W k ∪ W' k)) : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (count_union _ _ _ hcover)
    _ = (zc L : ℝ≥0∞) + (zc (⋃ k ∈ Finset.range K, (W k ∪ W' k)) : ℝ≥0∞) := ENat.toENNReal_add _ _
    _ ≤ ENNReal.ofReal Z₀ + ∑ k ∈ Finset.range K, 2 * ENNReal.ofReal (C * T ^ (a + ε / 2)) := by
        gcongr
        · rw [hZ₀, ENNReal.ofReal_toReal hLne]
        · exact (pc_zc_biUnion _ _ _ le_rfl).trans (Finset.sum_le_sum hwin)
    _ = ENNReal.ofReal (Z₀ + K * (2 * (C * T ^ (a + ε / 2)))) := by
        rw [Finset.sum_const, Finset.card_range, ENNReal.ofReal_add hZ₀0 (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        simp
    _ ≤ ENNReal.ofReal ((Z₀ + 2 * C * (2 / (ε * Real.log 2))) * T ^ (a + ε)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (K : ℝ) * (2 * (C * T ^ (a + ε / 2))) ≤
            T ^ (ε / 2) * (2 / (ε * Real.log 2)) * (2 * (C * T ^ (a + ε / 2))) :=
          mul_le_mul_of_nonneg_right hKlog (by positivity)
        have e : T ^ (ε / 2) * (2 / (ε * Real.log 2)) * (2 * (C * T ^ (a + ε / 2))) =
            2 * C * (2 / (ε * Real.log 2)) * T ^ (a + ε) := by rw [← hpow2]; ring
        nlinarith

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
alias dyadic_assembly := GuthMaynard.CitedZeros.Ing.PartC.dyadic_assembly

alias window_bound_half := GuthMaynard.CitedZeros.Ing.PartC.window_bound_half

/-- `T ≤ Y ≤ T²`. -/
theorem Ys_bounds (σ T : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (hT : 1 ≤ T) :
    T ≤ Ys σ T ∧ Ys σ T ≤ T ^ 2 := by
  unfold Ys
  have h2 : 0 < 2 * (2 - σ) := by linarith
  have e1 : (1 : ℝ) ≤ 3 / (2 * (2 - σ)) := by rw [le_div_iff₀ h2]; linarith
  have e2 : 3 / (2 * (2 - σ)) ≤ (2 : ℝ) := by rw [div_le_iff₀ h2]; linarith
  constructor
  · calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT e1
  · calc T ^ (3 / (2 * (2 - σ))) ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT e2
      _ = T ^ 2 := by norm_cast

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing.PartD
open GuthMaynard.CitedZeros.Ing
/-!
# Ingham blueprint, Part D: zero detection

`detect_shift`, `res_small`, `tail_small`, `trunc_small`, `detect`, `gamma_line_bound`,
generalising `MP23.lean` (there `X = 2T^{1/100}`, `Y = T^{1/2}`) to general `X`, `Y`.
-/

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

lemma one_add_sq_le (u : ℝ) : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by
  nlinarith [sq_abs u, abs_nonneg u]

/-- `|Γ(z)| ≤ C / (1 + (Im z)^2)` in the strip `a ≤ Re z ≤ b`, `a > 0`. -/
lemma gamma_sq_decay (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C, hC, h⟩ := gamma_decay a b ha 2
  refine ⟨C, hC, fun z hza hzb => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have := h z hza hzb
  have h2 := one_add_sq_le z.im
  nlinarith [norm_nonneg (Complex.Gamma z)]

/-- Uniform bound for `∫ |Γ|` on the vertical lines we need. -/
lemma gamma_int_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, (σ = -1 / 2 ∨ σ ∈ Icc (1 / 2 : ℝ) 3) →
    ‖∫ u : ℝ, Complex.Gamma ((σ : ℂ) + (u : ℂ) * I)‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := gamma_sq_decay (1 / 2) 3 (by norm_num)
  refine ⟨2 * C * Real.pi, by positivity, ?_⟩
  intro σ hσ
  have hb : ∀ u : ℝ, ‖Complex.Gamma ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (2 * C) * (1 + u ^ 2)⁻¹ := by
    intro u
    rcases hσ with hσ | hσ
    · subst hσ
      set z : ℂ := (((-1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I with hz
      have hzre : z.re = -1 / 2 := by simp [hz]
      have hz0 : z ≠ 0 := by intro h0; rw [h0] at hzre; norm_num at hzre
      have hn : (1 / 2 : ℝ) ≤ ‖z‖ := by
        have := Complex.abs_re_le_norm z
        rw [hzre] at this; norm_num at this; linarith
      have hΓ : ‖Complex.Gamma z‖ ≤ 2 * ‖Complex.Gamma (z + 1)‖ := by
        rw [Complex.Gamma_add_one z hz0, norm_mul]
        nlinarith [norm_nonneg (Complex.Gamma z)]
      have h1 := h (z + 1) (by simp [hzre]; norm_num) (by simp [hzre]; norm_num)
      have him : (z + 1).im = u := by simp [hz]
      rw [him] at h1
      calc ‖Complex.Gamma z‖ ≤ 2 * ‖Complex.Gamma (z + 1)‖ := hΓ
        _ ≤ 2 * (C / (1 + u ^ 2)) := by gcongr
        _ = _ := by ring
    · have h1 := h ((σ : ℂ) + (u : ℂ) * I) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2])
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h1
      calc _ ≤ C / (1 + u ^ 2) := h1
        _ ≤ 2 * C / (1 + u ^ 2) := by gcongr; linarith
        _ = _ := by ring
  have hint := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (2 * C))
    (ae_of_all _ hb)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  exact hint

/-! ### Contour shift -/
theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1
    funext t
    simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      have hz' : z.re ∈ Icc a b := by
        simpa [uIcc_of_le hab] using hz.1
      exact (hdiff z hz'.1 hz'.2).differentiableWithinAt
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

/-- A bound valid for large heights extends to the whole closed strip by compactness. -/
lemma strip_bound (φ : ℂ → ℂ) (a b C H : ℝ)
    (hc : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ContinuousAt φ z)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) :
    ∃ C' : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖φ z‖ ≤ C' / (1 + z.im ^ 2) := by
  let K : Set ℂ := Icc a b ×ℂ Icc (-H) H
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖φ z‖) K := by
    intro z hz
    exact ((continuous_const.add (continuous_im.pow 2)).continuousAt.mul
      (hc z hz.1.1 hz.1.2).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hw
  refine ⟨max B C, fun z hza hzb => ?_⟩
  by_cases ht : H ≤ |z.im|
  · exact (hd z hza hzb ht).trans (by gcongr; exact le_max_right _ _)
  · have hzK : z ∈ K := ⟨⟨hza, hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have := hB (Set.mem_image_of_mem _ hzK)
    rw [le_div_iff₀ (by positivity)]
    have h2 : (1 + z.im ^ 2) * ‖φ z‖ ≤ max B C := this.trans (le_max_left _ _)
    linarith

lemma line_integrable (φ : ℂ → ℂ) (x C : ℝ)
    (hc : ∀ u : ℝ, ContinuousAt φ ((x : ℂ) + (u : ℂ) * I))
    (hb : ∀ u : ℝ, ‖φ ((x : ℂ) + (u : ℂ) * I)‖ ≤ C / (1 + u ^ 2)) :
    Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
  have hcont : Continuous (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact ContinuousAt.comp (g := φ) (hc u)
      (by fun_prop : ContinuousAt (fun u : ℝ => (x : ℂ) + (u : ℂ) * I) u)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  apply ae_of_all
  intro u
  simpa [div_eq_mul_inv] using hb u

/-- Integrability on a vertical line from continuity and a large-height bound. -/
lemma line_integrable' (φ : ℂ → ℂ) (x C H : ℝ)
    (hc : ∀ u : ℝ, ContinuousAt φ ((x : ℂ) + (u : ℂ) * I))
    (hd : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
  have hc' : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → ContinuousAt φ z := by
    intro z h1 h2
    have hz : z = (x : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp <;> linarith
    rw [hz]; exact hc _
  obtain ⟨C', hC'⟩ := strip_bound φ x x C H hc' hd
  refine line_integrable φ x C' hc (fun u => ?_)
  have := hC' ((x : ℂ) + (u : ℂ) * I) (by simp) (by simp)
  simpa using this

/-- Contour shift across one simple pole, comparing with a reference function `g` of residue 1. -/
lemma shift_pole (f g : ℂ → ℂ) (a b : ℝ) (s₀ R : ℂ) (ha : a < s₀.re) (hb : s₀.re < b)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ g z)
    (hfl : Tendsto (fun z => (z - s₀) * f z) (𝓝[≠] s₀) (𝓝 R))
    (hgl : Tendsto (fun z => (z - s₀) * g z) (𝓝[≠] s₀) (𝓝 1))
    (hfd : ∃ C H : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖f z‖ ≤ C / (1 + z.im ^ 2))
    (hgd : ∃ C H : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖g z‖ ≤ C / (1 + z.im ^ 2)) :
    (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)) - ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I) =
      R * ((∫ u : ℝ, g ((a : ℂ) + (u : ℂ) * I)) - ∫ u : ℝ, g ((b : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨Cf, Hf, hfd⟩ := hfd
  obtain ⟨Cg, Hg, hgd⟩ := hgd
  have hab : a ≤ b := by linarith
  set h : ℂ → ℂ := fun z => f z - R * g z with hh
  set h' : ℂ → ℂ := Function.update h s₀ ((𝓝[≠] s₀).limUnder h) with hh'
  -- the open strip around `s₀`
  set U : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hUs : U ∈ 𝓝 s₀ := hUo.mem_nhds ⟨ha, hb⟩
  have hhd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ h z :=
    fun z h1 h2 h3 => (hf z h1 h2 h3).sub ((hg z h1 h2 h3).const_mul R)
  have hlim : Tendsto (fun z => (z - s₀) * h z) (𝓝[≠] s₀) (𝓝 0) := by
    have := hfl.sub (hgl.const_mul R)
    simp only [mul_one, sub_self] at this
    refine this.congr (fun z => ?_)
    simp only [hh]; ring
  have hlo : (fun z => h z - h s₀) =o[𝓝[≠] s₀] fun z => (z - s₀)⁻¹ := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h2 : Tendsto (fun z => (z - s₀) * h s₀) (𝓝[≠] s₀) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => z - s₀) (𝓝[≠] s₀) (𝓝 0) := by
          have h0 : Tendsto (fun z : ℂ => z - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
            tendsto_id.sub_const s₀
          rw [sub_self] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        simpa using this.mul_const (h s₀)
      have := hlim.sub h2
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - s₀ ≠ 0 := sub_ne_zero.mpr hz
      field_simp
    · filter_upwards [self_mem_nhdsWithin] with z hz h0
      exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))
  have hdon : DifferentiableOn ℂ h (U \ {s₀}) := by
    intro z hz
    exact (hhd z hz.1.1.le hz.1.2.le hz.2).differentiableWithinAt
  have hD := Complex.differentiableOn_update_limUnder_of_isLittleO hUs hdon hlo
  have hh'd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ h' z := by
    intro z h1 h2
    by_cases hz : z = s₀
    · subst hz
      exact hD.differentiableAt hUs
    · have heq : h' =ᶠ[𝓝 z] h := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        simp only [hh']
        exact Function.update_of_ne hw _ _
      exact (hhd z h1 h2 hz).congr_of_eventuallyEq heq
  -- large-height bound for `h'`
  set H := max (max Hf Hg) (|s₀.im| + 1) with hH
  have hh'b : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| →
      ‖h' z‖ ≤ (Cf + ‖R‖ * Cg) / (1 + z.im ^ 2) := by
    intro z h1 h2 h3
    have hz : z ≠ s₀ := by
      intro hz; rw [hz] at h3
      have : |s₀.im| + 1 ≤ H := le_max_right _ _
      linarith
    have : h' z = h z := by simp only [hh']; exact Function.update_of_ne hz _ _
    rw [this]
    have e1 := hfd z h1 h2 (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h3)
    have e2 := hgd z h1 h2 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h3)
    calc ‖h z‖ ≤ ‖f z‖ + ‖R‖ * ‖g z‖ := by
          simp only [hh]; exact (norm_sub_le _ _).trans (by rw [norm_mul])
      _ ≤ Cf / (1 + z.im ^ 2) + ‖R‖ * (Cg / (1 + z.im ^ 2)) := by gcongr
      _ = _ := by ring
  obtain ⟨C', hC'⟩ := strip_bound h' a b _ H (fun z h1 h2 => (hh'd z h1 h2).continuousAt) hh'b
  -- integrability of `f`, `g` on the two lines
  have hne : ∀ x : ℝ, x ≠ s₀.re → ∀ u : ℝ, (x : ℂ) + (u : ℂ) * I ≠ s₀ := by
    intro x hx u he; apply hx; rw [← he]; simp
  have hint : ∀ φ : ℂ → ℂ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ φ z) →
      ∀ C H : ℝ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) →
      ∀ x : ℝ, a ≤ x → x ≤ b → x ≠ s₀.re → Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
    intro φ hφ C H hφb x hx1 hx2 hx3
    refine line_integrable' φ x C H (fun u => (hφ _ (by simpa using hx1) (by simpa using hx2)
      (hne x hx3 u)).continuousAt) (fun z h1 h2 h3 => hφb z (by linarith) (by linarith) h3)
  have hfa := hint f hf Cf Hf hfd a le_rfl hab (by linarith)
  have hfb := hint f hf Cf Hf hfd b hab le_rfl (by linarith)
  have hga := hint g hg Cg Hg hgd a le_rfl hab (by linarith)
  have hgb := hint g hg Cg Hg hgd b hab le_rfl (by linarith)
  have hline : ∀ x : ℝ, x ≠ s₀.re → (fun u : ℝ => h' ((x : ℂ) + (u : ℂ) * I)) =
      fun u : ℝ => f ((x : ℂ) + (u : ℂ) * I) - R * g ((x : ℂ) + (u : ℂ) * I) := by
    intro x hx; funext u
    simp only [hh']
    rw [Function.update_of_ne (hne x hx u)]
  have hh'a : Integrable (fun u : ℝ => h' ((a : ℂ) + (u : ℂ) * I)) := by
    rw [hline a (by linarith)]; exact hfa.sub (hga.const_mul R)
  have hh'bb : Integrable (fun u : ℝ => h' ((b : ℂ) + (u : ℂ) * I)) := by
    rw [hline b (by linarith)]; exact hfb.sub (hgb.const_mul R)
  have hmain := integral_eq_of_strip_decay h' a b C' hab hh'd hh'a hh'bb
    (fun σ (hσ : σ ∈ Icc a b) t => by
      simpa using hC' ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ.1) (by simpa using hσ.2))
  rw [hline a (by linarith), hline b (by linarith), integral_sub hfa (hga.const_mul R),
    integral_sub hfb (hgb.const_mul R), integral_const_mul, integral_const_mul] at hmain
  linear_combination hmain

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

lemma g_decay {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖Complex.Gamma (z - (1 - ρ))‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₂, hC₂, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 2
  refine ⟨4 * C₂, 2 * |ρ.im| + 2, fun z hz1 hz2 hzi => ?_⟩
  set w := z - (1 - ρ) with hw
  have hwim : w.im = z.im + ρ.im := by simp [hw]
  have hwre : w.re = z.re - 1 + ρ.re := by simp [hw]; ring
  have hwi : |z.im| / 2 + 1 ≤ |w.im| := by
    rw [hwim]
    have := abs_sub_abs_le_abs_sub z.im (-ρ.im)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwi; simp at hwi; linarith [abs_nonneg z.im]
  have hwn : 1 ≤ ‖w‖ := le_trans (by linarith [abs_nonneg z.im]) (hwi.trans (Complex.abs_im_le_norm w))
  have hg := hΓ (w + 1) (by simp; linarith) (by simp; linarith)
  simp only [add_im, one_im, add_zero] at hg
  have h1 : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ := by
    rw [Complex.Gamma_add_one w hw0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hwn
  have hsq : 1 + z.im ^ 2 ≤ 4 * (1 + |w.im|) ^ 2 := by
    nlinarith [sq_abs z.im, abs_nonneg z.im, abs_nonneg w.im]
  rw [le_div_iff₀ (by positivity)]
  calc ‖Complex.Gamma w‖ * (1 + z.im ^ 2) ≤ ‖Complex.Gamma (w + 1)‖ * (4 * (1 + |w.im|) ^ 2) := by
        gcongr
    _ = 4 * ((1 + |w.im|) ^ 2 * ‖Complex.Gamma (w + 1)‖) := by ring
    _ ≤ 4 * C₂ := by gcongr

lemma g_res (s₀ : ℂ) :
    Tendsto (fun z => (z - s₀) * Complex.Gamma (z - s₀)) (𝓝[≠] s₀) (𝓝 1) := by
  have hc : ContinuousAt (fun z : ℂ => Complex.Gamma (z - s₀ + 1)) s₀ := by
    refine ((Complex.differentiableAt_Gamma _ ?_).comp s₀
      ((differentiableAt_id.sub_const s₀).add_const 1)).continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
  simp only [sub_self, zero_add, Complex.Gamma_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [Complex.Gamma_add_one _ (sub_ne_zero.mpr hz)]

lemma g_diff {ρ : ℂ} (z : ℂ) (hz1 : 1 / 2 - ρ.re ≤ z.re) (hz : z ≠ 1 - ρ) :
    DifferentiableAt ℂ (fun z => Complex.Gamma (z - (1 - ρ))) z := by
  refine (Complex.differentiableAt_Gamma _ ?_).comp z (differentiableAt_id.sub_const _)
  intro m hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; apply hz; simpa [sub_eq_zero] using hm
  · have := congrArg Complex.re hm
    simp at this
    have : (1 : ℝ) ≤ m := by exact_mod_cast h
    linarith

/-! ### The contour shift -/
lemma ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  rw [MeasureTheory.ae_iff]; simp

lemma g_line (s₀ : ℂ) (x : ℝ) :
    (∫ u : ℝ, Complex.Gamma ((x : ℂ) + (u : ℂ) * I - s₀)) =
      ∫ u : ℝ, Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I) := by
  have := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I)) s₀.im
  rw [← this]
  congr 1
  funext u
  congr 1
  apply Complex.ext <;> simp

lemma moeb_norm_le (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := m)
  rw [show ((ArithmeticFunction.moebius m : ℤ) : ℂ) = (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
    by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast this

/-- `mellin (e^{-x}) = Γ`. -/
lemma mellin_exp {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs]
  unfold mellin Complex.GammaIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [smul_eq_mul]
  ring

lemma gamma_line_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _, h⟩ := gamma_sq_decay c c hc
  refine line_integrable Complex.Gamma c C (fun u => ?_) (fun u => ?_)
  · apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · simpa using h ((c : ℂ) + (u : ℂ) * I) (by simp) (by simp)

/-- Cahen–Mellin: `(1/2π) ∫ Γ(c+iu) x^{-(c+iu)} du = e^{-x}`. -/
lemma cahen_mellin (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, (x : ℂ) ^ (-((c : ℂ) + (u : ℂ) * I)) *
      Complex.Gamma ((c : ℂ) + (u : ℂ) * I) = (Real.exp (-x) : ℂ) := by
  have hconv : MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (c : ℂ) := by
    unfold MellinConvergent
    have := Complex.GammaIntegral_convergent (s := (c : ℂ)) (by simpa using hc)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hvert : VerticalIntegrable (mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ))) c := by
    unfold VerticalIntegrable
    refine (gamma_line_integrable c hc).congr (ae_of_all _ (fun u => ?_))
    simp only
    rw [mellin_exp (by simpa using hc)]
  have hcont : ContinuousAt (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) x := by fun_prop
  have := mellinInv_mellin_eq c _ hx hconv hvert hcont
  unfold mellinInv at this
  rw [← this, Complex.real_smul]
  push_cast
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun u => ?_)
  have hm := mellin_exp (s := (c : ℂ) + (u : ℂ) * I) (by simp [hc])
  push_cast at hm
  simp only [smul_eq_mul]
  rw [hm]

/-- The Mellin kernel `x^{-(2+iu)} Γ(2+iu)`. -/
noncomputable def Kx (x : ℝ) (u : ℝ) : ℂ :=
  (x : ℂ) ^ (-((2 : ℝ) + (u : ℂ) * I)) * Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)

lemma Kx_norm {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖Kx x u‖ = x ^ (-(2 : ℝ)) * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  unfold Kx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma Kx_integrable {x : ℝ} (hx : 0 < x) : Integrable (Kx x) := by
  have hG := gamma_line_integrable 2 (by norm_num)
  have hc : Continuous (Kx x) := by
    unfold Kx
    apply Continuous.mul
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · rw [continuous_iff_continuousAt]
      intro u
      apply ContinuousAt.comp (g := Complex.Gamma) _ (by fun_prop)
      apply (Complex.differentiableAt_Gamma _ _).continuousAt
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  refine (hG.norm.const_mul (x ^ (-(2 : ℝ)))).mono' hc.aestronglyMeasurable
    (ae_of_all _ (fun u => ?_))
  rw [Kx_norm hx]

lemma Kx_integral {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Kx x u = (Real.exp (-x) : ℂ) := by
  have := cahen_mellin 2 (by norm_num) hx
  rw [← this]
  rfl

/-- Geometric tail estimate. -/
lemma tail_est {Y X : ℝ} (hY : 1 ≤ Y) (hX : 0 ≤ X) (k : ℕ) (hk : X ≤ k) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ i, (((i + k : ℕ) : ℝ) * Real.exp (-((i + k : ℕ) : ℝ) / Y)) ≤ g i) ∧
      ∑' i, g i ≤ Real.exp (-X / (2 * Y)) * (2 * Y + 1) ^ 2 := by
  have hY0 : 0 < Y := by linarith
  set q : ℝ := Real.exp (-1 / (2 * Y)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : Real.exp (-1 / (2 * Y)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) (by linarith))
    rw [Real.exp_zero] at this; exact this
  have hqn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hqpow : ∀ m : ℕ, q ^ m = Real.exp (-(m : ℝ) / (2 * Y)) := by
    intro m; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set c : ℝ := Real.exp (-X / (2 * Y)) with hc
  refine ⟨fun i => c * (((i + k : ℕ) : ℝ) * q ^ (i + k)), ?_, ?_, ?_⟩
  · have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hqn
    simp only [pow_one] at hs
    exact ((summable_nat_add_iff k).mpr hs).mul_left c
  · intro i
    set m := i + k with hm
    have hmk : X ≤ (m : ℝ) := by rw [hm]; push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have e : Real.exp (-(m : ℝ) / Y) = Real.exp (-(m : ℝ) / (2 * Y)) * Real.exp (-(m : ℝ) / (2 * Y)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    show (m : ℝ) * Real.exp (-(m : ℝ) / Y) ≤ c * ((m : ℝ) * q ^ m)
    rw [e, hqpow]
    have hle : Real.exp (-(m : ℝ) / (2 * Y)) ≤ c := by
      rw [hc, Real.exp_le_exp]
      apply div_le_div_of_nonneg_right _ (by linarith); linarith
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    calc (m : ℝ) * (Real.exp (-(m : ℝ) / (2 * Y)) * Real.exp (-(m : ℝ) / (2 * Y)))
        = Real.exp (-(m : ℝ) / (2 * Y)) * ((m : ℝ) * Real.exp (-(m : ℝ) / (2 * Y))) := by ring
      _ ≤ c * ((m : ℝ) * Real.exp (-(m : ℝ) / (2 * Y))) := by gcongr
  · rw [tsum_mul_left]
    have hc0 : 0 ≤ c := (Real.exp_pos _).le
    have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hqn
    simp only [pow_one] at hs
    have hshift : ∑' i, (((i + k : ℕ) : ℝ) * q ^ (i + k)) ≤ ∑' m : ℕ, (m : ℝ) * q ^ m := by
      rw [← hs.sum_add_tsum_nat_add k]
      have : 0 ≤ ∑ i ∈ Finset.range k, (i : ℝ) * q ^ i :=
        Finset.sum_nonneg (fun i _ => by positivity)
      push_cast
      linarith
    have hgeo := tsum_coe_mul_geometric_of_norm_lt_one hqn
    have h1q : 1 / (2 * Y + 1) ≤ 1 - q := by
      have hexp := Real.add_one_le_exp (1 / (2 * Y))
      have hqe : q * Real.exp (1 / (2 * Y)) = 1 := by
        rw [hq, ← Real.exp_add]; simp [neg_div]
      have : q * (1 / (2 * Y) + 1) ≤ 1 := by
        calc q * (1 / (2 * Y) + 1) ≤ q * Real.exp (1 / (2 * Y)) := by gcongr
          _ = 1 := hqe
      have e2 : q * (1 / (2 * Y) + 1) = q * (2 * Y + 1) / (2 * Y) := by field_simp; ring
      rw [e2, div_le_one (by linarith)] at this
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hgeo_le : q / (1 - q) ^ 2 ≤ (2 * Y + 1) ^ 2 := by
      have hpos : 0 < 1 - q := by linarith
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ (2 * Y + 1) * (1 - q) := by
        rw [div_le_iff₀ (by linarith)] at h1q; linarith
      nlinarith
    calc c * ∑' i, (((i + k : ℕ) : ℝ) * q ^ (i + k)) ≤ c * ∑' m : ℕ, (m : ℝ) * q ^ m := by gcongr
      _ = c * (q / (1 - q) ^ 2) := by rw [hgeo]
      _ ≤ c * (2 * Y + 1) ^ 2 := by gcongr

/-! ### The integrand for general `X`, `Y` -/
/-- The integrand `Y^s Γ(s) M_X(ρ+s) ζ(ρ+s)`. -/
noncomputable def Ff (X Y : ℝ) (ρ s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma s * molli X (ρ + s) * riemannZeta (ρ + s)

/-- The integrand with the `Γ` pole at `0` cancelled against `ζ(ρ) = 0`. -/
noncomputable def Ft (X Y : ℝ) (ρ s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma (s + 1) * dslope (fun w => riemannZeta (ρ + w)) 0 s *
    molli X (ρ + s)

lemma lineInt_eq (X Y : ℝ) (ρ : ℂ) (x : ℝ) :
    lineInt X Y ρ x = (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Ff X Y ρ ((x : ℂ) + (u : ℂ) * I) := rfl

lemma molli_bound (X : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : ‖molli X w‖ ≤ (⌊X⌋₊ : ℝ) := by
  unfold molli
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊,
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [norm_mul]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := moeb_norm_le m
    have h2 : ‖(m : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by simp; linarith)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma molli_diff (X : ℝ) (ρ s : ℂ) : DifferentiableAt ℂ (fun s : ℂ => molli X (ρ + s)) s := by
  unfold molli
  apply DifferentiableAt.fun_sum
  intro m hm
  have hm0 : (m : ℂ) ≠ 0 := by
    have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact_mod_cast (by omega : m ≠ 0)
  exact (differentiableAt_const _).mul
    ((differentiableAt_const ρ |>.add differentiableAt_id).neg.const_cpow (Or.inl hm0))

lemma Ft_eq {X Y : ℝ} {ρ s : ℂ} (h0 : riemannZeta ρ = 0) (hs : s ≠ 0) :
    Ft X Y ρ s = Ff X Y ρ s := by
  unfold Ft Ff
  rw [dslope_of_ne _ hs, slope_def_field, Complex.Gamma_add_one s hs]
  simp only [add_zero, h0, sub_zero]
  field_simp

lemma Ft_diff {X Y : ℝ} (hY : 0 < Y) {ρ s : ℂ} (hρ : ρ ≠ 1) (hs : -1 < s.re)
    (hs1 : s ≠ 1 - ρ) : DifferentiableAt ℂ (Ft X Y ρ) s := by
  have hY0 : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have d1 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hY0)
  have d2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + 1)) s := by
    refine (Complex.differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.add_const 1)
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have d3 : DifferentiableAt ℂ (dslope (fun w => riemannZeta (ρ + w)) 0) s := by
    set V : Set ℂ := {w : ℂ | ρ + w ≠ 1} with hV
    have hVo : IsOpen V := isOpen_ne_fun (continuous_const.add continuous_id) continuous_const
    have h0V : V ∈ 𝓝 (0 : ℂ) := hVo.mem_nhds (by simp [hV, hρ])
    have hd : DifferentiableOn ℂ (fun w => riemannZeta (ρ + w)) V := by
      intro w hw
      exact ((differentiableAt_riemannZeta hw).comp w
        (differentiableAt_const ρ |>.add differentiableAt_id)).differentiableWithinAt
    have := (differentiableOn_dslope h0V).mpr hd
    have hsV : s ∈ V := by
      simp only [hV, mem_setOf_eq]
      intro h; apply hs1; rw [← h]; ring
    exact this.differentiableAt (hVo.mem_nhds hsV)
  exact ((d1.mul d2).mul d3).mul (molli_diff X ρ s)

lemma Ft_res {X Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ : ρ.re < 1) :
    Tendsto (fun z => (z - (1 - ρ)) * Ft X Y ρ z) (𝓝[≠] (1 - ρ)) (𝓝 (Res X Y ρ)) := by
  set s₀ := 1 - ρ with hs₀
  have hs₀re : 0 < s₀.re := by simp [hs₀]; linarith
  have hs₀0 : s₀ ≠ 0 := by intro h; rw [h] at hs₀re; simp at hs₀re
  have hY0 : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  set A : ℂ → ℂ := fun z => (Y : ℂ) ^ z * Complex.Gamma z * molli X (ρ + z) with hA
  have hAc : ContinuousAt A s₀ := by
    have d1 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ s) s₀ :=
      differentiableAt_id.const_cpow (Or.inl hY0)
    have d2 : DifferentiableAt ℂ Complex.Gamma s₀ := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    exact ((d1.mul d2).mul (molli_diff X ρ s₀)).continuousAt
  have hAlim : Tendsto A (𝓝[≠] s₀) (𝓝 (Res X Y ρ)) := by
    have := hAc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
    convert this using 2
    have e : ρ + s₀ = 1 := by rw [hs₀]; ring
    simp only [hA, Res, e]
    rw [hs₀]
  have hmap : Tendsto (fun z : ℂ => ρ + z) (𝓝[≠] s₀) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun z : ℂ => ρ + z) (𝓝 s₀) (𝓝 (ρ + s₀)) :=
        (continuous_const.add continuous_id).tendsto s₀
      rw [show ρ + s₀ = 1 by simp [hs₀]] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h; apply hz; show z = s₀; rw [hs₀]; linear_combination h
  have hZ : Tendsto (fun z : ℂ => (ρ + z - 1) * riemannZeta (ρ + z)) (𝓝[≠] s₀) (𝓝 1) :=
    riemannZeta_residue_one.comp hmap
  have hprod := hAlim.mul hZ
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  have hne0 : ∀ᶠ z in 𝓝[≠] s₀, z ≠ 0 := (eventually_ne_nhds hs₀0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne0] with z hz
  rw [Ft_eq h0 hz]
  simp only [hA, Ff, hs₀]
  ring

lemma Ft_decay {X Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖Ft X Y ρ z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₃, hC₃, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 3
  obtain ⟨Cz, hCz, hζ⟩ := zeta_growth
  set Mm : ℝ := (⌊X⌋₊ : ℝ) with hMm
  have hMm0 : 0 ≤ Mm := by positivity
  refine ⟨Y ^ (2 : ℝ) * C₃ * Mm * Cz * (3 + ‖ρ‖), |ρ.im| + 3, fun z hz1 hz2 hzi => ?_⟩
  have hY0 : 0 < Y := by linarith
  set t := z.im with ht
  have hti : 1 ≤ |t| := by linarith [abs_nonneg ρ.im]
  have hz0 : z ≠ 0 := by
    intro h
    have : t = 0 := by rw [ht, h]; simp
    rw [this] at hti; simp at hti; linarith
  rw [Ft_eq h0 hz0]
  unfold Ff
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0]
  have f1 : Y ^ z.re ≤ Y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY hz2
  have hznorm : 1 ≤ ‖z‖ := hti.trans (by rw [ht]; exact Complex.abs_im_le_norm z)
  have f2 : (1 + |t|) ^ 3 * ‖Complex.Gamma z‖ ≤ C₃ := by
    have hg := hΓ (z + 1) (by simp; linarith) (by simp; linarith)
    simp only [add_im, one_im, add_zero] at hg
    have : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ := by
      rw [Complex.Gamma_add_one z hz0, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hznorm
    calc (1 + |t|) ^ 3 * ‖Complex.Gamma z‖ ≤ (1 + |t|) ^ 3 * ‖Complex.Gamma (z + 1)‖ := by gcongr
      _ ≤ C₃ := hg
  have f3 : ‖molli X (ρ + z)‖ ≤ Mm := molli_bound X (by simp; linarith)
  have f4 : ‖riemannZeta (ρ + z)‖ ≤ Cz * ((3 + ‖ρ‖) * (1 + |t|)) := by
    have hw1 : 1 / 2 ≤ (ρ + z).re := by simp; linarith
    have hw2 : 2 ≤ |(ρ + z).im| := by
      simp only [add_im]
      have := abs_sub_abs_le_abs_sub z.im (-ρ.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      rw [← ht] at this ⊢
      linarith
    refine (hζ _ hw1 hw2).trans ?_
    gcongr
    have hzn : ‖z‖ ≤ 2 + |t| := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 + |t| := by
          rw [← ht]; gcongr; rw [abs_le]; constructor <;> linarith
    have := norm_add_le ρ z
    nlinarith [norm_nonneg ρ, abs_nonneg t]
  have hA : 0 < 1 + |t| := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hG : ‖Complex.Gamma z‖ ≤ C₃ / (1 + |t|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  calc Y ^ z.re * ‖Complex.Gamma z‖ * ‖molli X (ρ + z)‖ * ‖riemannZeta (ρ + z)‖ * (1 + t ^ 2)
      ≤ Y ^ (2 : ℝ) * (C₃ / (1 + |t|) ^ 3) * Mm * (Cz * ((3 + ‖ρ‖) * (1 + |t|))) *
          (1 + |t|) ^ 2 := by
        gcongr
    _ = Y ^ (2 : ℝ) * C₃ * Mm * Cz * (3 + ‖ρ‖) := by
        field_simp

lemma line_eq (X Y : ℝ) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (x : ℝ) :
    (∫ u : ℝ, Ff X Y ρ ((x : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, Ft X Y ρ ((x : ℂ) + (u : ℂ) * I) := by
  apply integral_congr_ae
  filter_upwards [ae_ne_zero] with u hu
  rw [Ft_eq h0]
  intro h
  apply hu
  have := congrArg Complex.im h
  simpa using this

/-- The contour shift from `Re s = 2` to `Re s = 1/2 - β`. -/
lemma contour_shift : ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y : ℝ, 1 ≤ Y → ∀ ρ : ℂ, riemannZeta ρ = 0 →
    0 < ρ.re → ρ.re < 1 →
    ‖lineInt X Y ρ (1 / 2 - ρ.re) - lineInt X Y ρ 2‖ ≤ K * ‖Res X Y ρ‖ := by
  obtain ⟨K₀, hK₀, hK⟩ := gamma_int_bound
  refine ⟨K₀ / Real.pi, by positivity, fun X Y hY ρ h0 hρ0 hρ1 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hρ1' : ρ ≠ 1 := by intro h; rw [h] at hρ1; simp at hρ1
  have hshift := shift_pole (Ft X Y ρ) (fun z => Complex.Gamma (z - (1 - ρ))) (1 / 2 - ρ.re) 2
    (1 - ρ) (Res X Y ρ) (by simp; linarith) (by simp; linarith)
    (fun z h1 _ h3 => Ft_diff hY0 hρ1' (by linarith) h3)
    (fun z h1 _ h3 => g_diff z h1 h3)
    (Ft_res hY0 h0 hρ1) (g_res (1 - ρ)) (Ft_decay hY h0 hρ0 hρ1) (g_decay hρ0 hρ1)
  rw [lineInt_eq, lineInt_eq, line_eq X Y h0, line_eq X Y h0, ← mul_sub]
  push_cast at hshift ⊢
  rw [hshift]
  have e1 := g_line (1 - ρ) (1 / 2 - ρ.re)
  have e2 := g_line (1 - ρ) 2
  push_cast at e1 e2
  rw [e1, e2]
  have b1 := hK ((1 / 2 - ρ.re) - (1 - ρ).re) (Or.inl (by simp; ring))
  have b2 := hK (2 - (1 - ρ).re) (Or.inr ⟨by simp; linarith, by simp; linarith⟩)
  push_cast at b1 b2
  rw [norm_mul, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hsub := norm_sub_le
    (∫ u : ℝ, Complex.Gamma (((1 / 2 - ρ.re - (1 - ρ).re : ℝ) : ℂ) + (u : ℂ) * I))
    (∫ u : ℝ, Complex.Gamma (((2 - (1 - ρ).re : ℝ) : ℂ) + (u : ℂ) * I))
  push_cast at hsub
  have hRn := norm_nonneg (Res X Y ρ)
  calc 1 / (2 * Real.pi) * (‖Res X Y ρ‖ * ‖_ - _‖)
      ≤ 1 / (2 * Real.pi) * (‖Res X Y ρ‖ * (K₀ + K₀)) := by gcongr; linarith
    _ = K₀ / Real.pi * ‖Res X Y ρ‖ := by field_simp; ring

/-! ### Mellin inversion on `Re s = 2` -/
lemma aX_norm_le (X : ℝ) (n : ℕ) : ‖aX X n‖ ≤ n := by
  unfold aX
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun m _ => moeb_norm_le m)).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self n)

/-- The Dirichlet series of `a_X(n)` is `M_X(w) ζ(w)`. -/
lemma dirichlet_aX {X : ℝ} (hX : 0 ≤ X) {w : ℂ} (hw : 1 < w.re) :
    ∑' n : ℕ, aX X n * (n : ℂ) ^ (-w) = molli X w * riemannZeta w := by
  set N := ⌊X⌋₊ with hN
  set f : ℕ → ℂ := fun m => if 1 ≤ m ∧ m ≤ N then (ArithmeticFunction.moebius m : ℂ) else 0
    with hf
  have hfs : LSeriesSummable f w := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
    intro m hm
    rw [LSeries.term_def]
    simp only [Finset.mem_Icc] at hm
    simp [hf, hm]
  have h1s : LSeriesSummable 1 w := LSeriesSummable_one_iff.mpr hw
  have hconv := LSeries_convolution' hfs h1s
  rw [LSeries_one_eq_riemannZeta hw] at hconv
  have hLf : LSeries f w = molli X w := by
    unfold LSeries molli
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      rw [LSeries.term_def, if_neg (by omega), hf]
      simp only [hm', and_self, if_true]
      rw [Complex.cpow_neg, div_eq_mul_inv]
    · intro m hm
      rw [LSeries.term_def]
      simp only [Finset.mem_Icc] at hm
      simp [hf, hm]
  rw [hLf] at hconv
  rw [← hconv]
  unfold LSeries
  congr 1
  funext n
  rw [LSeries.term_def, LSeries.convolution_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aX]
  rw [if_neg hn.ne', Complex.cpow_neg, div_eq_mul_inv]
  congr 1
  show aX X n = ∑ p ∈ n.divisorsAntidiagonal, f p.1 * (1 : ℕ → ℂ) p.2
  rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * (1 : ℕ → ℂ) b)]
  unfold aX
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  simp only [Pi.one_apply, mul_one, hf]
  have : (d ≤ N) ↔ ((d : ℝ) ≤ X) := by rw [hN]; exact Nat.le_floor_iff hX
  by_cases hdN : d ≤ N
  · rw [if_pos (this.mp hdN), if_pos ⟨hd1, hdN⟩]
  · rw [if_neg (fun h => hdN (this.mpr h)), if_neg (fun h => hdN h.2)]

lemma cpow_split {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : 0 < n) (ρ s : ℂ) :
    (Y : ℂ) ^ s * (n : ℂ) ^ (-(ρ + s)) =
      (n : ℂ) ^ (-ρ) * (((n : ℝ) / Y : ℝ) : ℂ) ^ (-s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) / Y := div_pos hn' hY
  have hY0 : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx0 : (((n : ℝ) / Y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hY0, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hx0, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hY.le,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hn'.le,
    Real.log_div hn'.ne' hY.ne']
  push_cast
  ring

/-- Mellin inversion on `Re s = 2`. -/
lemma mellin_line {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y) {ρ : ℂ} (hρ : 0 < ρ.re) :
    lineInt X Y ρ 2 = Iser X Y ρ := by
  set c : ℕ → ℂ := fun n => aX X n * (n : ℂ) ^ (-ρ) with hc
  set x : ℕ → ℝ := fun n => (n : ℝ) / Y with hx
  have hc0 : c 0 = 0 := by simp [hc, aX]
  have hpt : ∀ u : ℝ, Ff X Y ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I) = ∑' n : ℕ, c n * Kx (x n) u := by
    intro u
    set s : ℂ := ((2 : ℝ) : ℂ) + (u : ℂ) * I with hs
    have hre : 1 < (ρ + s).re := by simp [hs]; linarith
    unfold Ff
    rw [mul_assoc _ (molli X (ρ + s)), ← dirichlet_aX hX hre, ← tsum_mul_left]
    congr 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, aX]
    simp only [hc, hx, Kx]
    have := cpow_split hY hn ρ s
    rw [← hs]
    calc (Y : ℂ) ^ s * Complex.Gamma s * (aX X n * (n : ℂ) ^ (-(ρ + s)))
        = aX X n * Complex.Gamma s * ((Y : ℂ) ^ s * (n : ℂ) ^ (-(ρ + s))) := by ring
      _ = _ := by rw [this]; ring
  have hint : ∀ n : ℕ, Integrable (fun u : ℝ => c n * Kx (x n) u) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]
    exact (Kx_integrable (div_pos (by exact_mod_cast hn) hY)).const_mul _
  set G : ℝ := ∫ u : ℝ, ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ with hG
  have hG0 : 0 ≤ G := integral_nonneg (fun _ => norm_nonneg _)
  have hnorm : ∀ n : ℕ, ∫ u : ℝ, ‖c n * Kx (x n) u‖ ≤ Y ^ 2 * G * (n : ℝ) ^ (-1 - ρ.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hxn : 0 < x n := div_pos hn' hY
    have e : (fun u : ℝ => ‖c n * Kx (x n) u‖) =
        fun u : ℝ => (‖c n‖ * x n ^ (-(2 : ℝ))) *
          ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
      funext u; rw [norm_mul, Kx_norm hxn]; ring
    rw [e, integral_const_mul]
    have hcn : ‖c n‖ ≤ (n : ℝ) * (n : ℝ) ^ (-ρ.re) := by
      simp only [hc]
      rw [norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hn']
      simp only [neg_re]
      gcongr
      exact aX_norm_le X n
    have hxp : x n ^ (-(2 : ℝ)) = Y ^ 2 * (n : ℝ) ^ (-(2 : ℝ)) := by
      simp only [hx]
      rw [Real.div_rpow hn'.le hY.le, Real.rpow_neg hY.le, Real.rpow_neg hn'.le,
        Real.rpow_two, Real.rpow_two]
      field_simp
    calc ‖c n‖ * x n ^ (-(2 : ℝ)) * G
        ≤ ((n : ℝ) * (n : ℝ) ^ (-ρ.re)) * x n ^ (-(2 : ℝ)) * G := by gcongr
      _ = Y ^ 2 * G * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-ρ.re) * (n : ℝ) ^ (-(2 : ℝ))) := by
          rw [hxp, Real.rpow_one]; ring
      _ = Y ^ 2 * G * (n : ℝ) ^ (-1 - ρ.re) := by
          rw [← Real.rpow_add hn', ← Real.rpow_add hn']; ring_nf
  have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖c n * Kx (x n) u‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hfub := integral_tsum_of_summable_integral_norm hint hsum
  rw [lineInt_eq]
  unfold Iser
  rw [show (fun u : ℝ => Ff X Y ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I)) =
    fun u => ∑' n : ℕ, c n * Kx (x n) u from funext hpt]
  push_cast at hfub ⊢
  rw [← hfub, ← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hc0, aX]
  have hxn : 0 < x n := div_pos (by exact_mod_cast hn) hY
  rw [integral_const_mul]
  calc (1 / (2 * (Real.pi : ℂ))) * (c n * ∫ u : ℝ, Kx (x n) u)
      = c n * ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Kx (x n) u) := by push_cast; ring
    _ = c n * (Real.exp (-x n) : ℂ) := by rw [Kx_integral hxn]
    _ = _ := by
        simp only [hc, hx, neg_div]
        push_cast
        ring

/-! ### Targets: `detect_shift`, `res_small` -/
theorem detect_shift : ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y → ∀ ρ : ℂ,
    riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 ≤ ρ.im →
      ‖lineInt X Y ρ (1 / 2 - ρ.re) - Iser X Y ρ‖ ≤ K * ‖Res X Y ρ‖ := by
  obtain ⟨K, hK0, hK⟩ := contour_shift
  refine ⟨K, hK0, fun X Y hX hY ρ h0 hρ0 hρ1 _ => ?_⟩
  rw [← mellin_line (by linarith) (by linarith) hρ0]
  exact hK X Y hY ρ h0 hρ0 hρ1

end GuthMaynard.CitedZeros.Ing.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
/-! ## Step 1: zero detection (generalises `MP23.lean`) -/

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing.PartD
open GuthMaynard.CitedZeros.Ing
theorem res_small (ε : ℝ) (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, T ≤ Y →
    Y ≤ T ^ 2 → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → T ≤ ρ.im → ‖Res T Y ρ‖ ≤ ε := by
  obtain ⟨C₄, hC₄, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 4
  refine ⟨max 1 (C₄ / ε), fun T hT Y hTY hYT ρ hρ0 hρ1 hγ => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTε : C₄ / ε ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  unfold Res
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0]
  have f1 : Y ^ ((1 - ρ).re) ≤ T ^ 2 := by
    calc Y ^ ((1 - ρ).re) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by simp; linarith)
      _ = Y := Real.rpow_one Y
      _ ≤ T ^ 2 := hYT
  have f3 : ‖molli T 1‖ ≤ T := (molli_bound T (by simp)).trans (Nat.floor_le hT0.le)
  have hs : (1 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hg := hΓ (1 - ρ + 1) (by simp; linarith) (by simp; linarith)
  simp only [add_im, sub_im, one_im, zero_sub, add_zero, abs_neg] at hg
  have hγ' : T ≤ |ρ.im| := hγ.trans (le_abs_self _)
  have hsn : T ≤ ‖1 - ρ‖ := by
    refine hγ.trans ?_
    have := Complex.abs_im_le_norm (1 - ρ)
    simp at this
    exact (le_abs_self _).trans this
  have f2 : ‖Complex.Gamma (1 - ρ)‖ * T ^ 4 ≤ C₄ := by
    have e : ‖Complex.Gamma (1 - ρ + 1)‖ = ‖1 - ρ‖ * ‖Complex.Gamma (1 - ρ)‖ := by
      rw [Complex.Gamma_add_one _ hs, norm_mul]
    rw [e] at hg
    have h4 : T ^ 4 ≤ (1 + |ρ.im|) ^ 4 * ‖1 - ρ‖ := by
      have : T ^ 4 ≤ (1 + |ρ.im|) ^ 4 := by gcongr; linarith
      exact this.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    have hGn := norm_nonneg (Complex.Gamma (1 - ρ))
    calc ‖Complex.Gamma (1 - ρ)‖ * T ^ 4
        ≤ ‖Complex.Gamma (1 - ρ)‖ * ((1 + |ρ.im|) ^ 4 * ‖1 - ρ‖) := by gcongr
      _ = (1 + |ρ.im|) ^ 4 * (‖1 - ρ‖ * ‖Complex.Gamma (1 - ρ)‖) := by ring
      _ ≤ C₄ := hg
  have hG : ‖Complex.Gamma (1 - ρ)‖ ≤ C₄ / T ^ 4 := by
    rw [le_div_iff₀ (by positivity)]; exact f2
  calc Y ^ ((1 - ρ).re) * ‖Complex.Gamma (1 - ρ)‖ * ‖molli T 1‖
      ≤ T ^ 2 * (C₄ / T ^ 4) * T := by gcongr
    _ = C₄ / T := by field_simp
    _ ≤ ε := by
        rw [div_le_iff₀ hT0]
        rw [div_le_iff₀ hε] at hTε
        linarith

end GuthMaynard.CitedZeros.Ing.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing.PartD
open GuthMaynard.CitedZeros.Ing
/-! ### `tail_small` -/
lemma aX_one {X : ℝ} (h : 1 ≤ X) : aX X 1 = 1 := by
  unfold aX
  rw [Nat.divisors_one, Finset.filter_singleton, if_pos (by simpa using h)]
  simp

lemma aX_zero_of {X : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnX : (n : ℝ) ≤ X) : aX X n = 0 := by
  unfold aX
  rw [Finset.filter_true_of_mem]
  · have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
      ArithmeticFunction.moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne (by omega)] at h
    exact_mod_cast h
  · intro d hd
    have := Nat.divisor_le hd
    have : (d : ℝ) ≤ n := by exact_mod_cast this
    linarith

lemma tail_numeric (η : ℝ) (hη : 0 < η) : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
    Real.exp (-(T ^ η) / 2) * (2 * T ^ 2 + 1) ^ 2 ≤ 1 / 100 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (4 / η) * Real.exp (-(1 / 2) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / η) (1 / 2) (by norm_num)
  have h2 := h1.comp (tendsto_rpow_atTop hη)
  have h3 := h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 900))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (h3.and (eventually_ge_atTop 1))
  refine ⟨T₁, fun T hT => ?_⟩
  obtain ⟨hlt, hT1⟩ := hT₁ T hT
  simp only [Function.comp] at hlt
  have hT0 : 0 ≤ T := by linarith [hT1]
  have e : (T ^ η) ^ (4 / η) = T ^ 4 := by
    rw [← Real.rpow_mul hT0, mul_div_cancel₀ _ hη.ne']
    norm_cast
  rw [e] at hlt
  have e2 : Real.exp (-(1 / 2) * T ^ η) = Real.exp (-(T ^ η) / 2) := by ring_nf
  rw [e2] at hlt
  have h9 : (2 * T ^ 2 + 1) ^ 2 ≤ 9 * T ^ 4 := by
    have h1 : 0 ≤ T ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 5 * T ^ 2 + 1) h1]
  calc Real.exp (-(T ^ η) / 2) * (2 * T ^ 2 + 1) ^ 2
      ≤ Real.exp (-(T ^ η) / 2) * (9 * T ^ 4) := by gcongr
    _ = 9 * (T ^ 4 * Real.exp (-(T ^ η) / 2)) := by ring
    _ ≤ 9 * (1 / 900) := by gcongr
    _ = 1 / 100 := by norm_num

theorem tail_small (η : ℝ) (hη : 0 < η) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, T ≤ Y →
    Y ≤ T ^ 2 → ∀ ρ : ℂ, 0 < ρ.re →
      ‖Iser T Y ρ - (Real.exp (-1 / Y) : ℂ) - SI T Y η ρ‖ ≤ 1 / 100 := by
  obtain ⟨T₁, hT₁⟩ := tail_numeric η hη
  refine ⟨max T₁ 1, fun T hT Y hTY hYT ρ hρ => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTn := hT₁ T (le_trans (le_max_left _ _) hT)
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  set b : ℕ → ℂ := fun n => aX T n * (Real.exp (-(n : ℝ) / Y) : ℂ) * (n : ℂ) ^ (-ρ) with hb
  have hbn : ∀ n : ℕ, ‖b n‖ ≤ (n : ℝ) * Real.exp (-(n : ℝ) / Y) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb, aX]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hb]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hn']
    have h1 : (n : ℝ) ^ (-ρ).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
    have h2 := aX_norm_le T n
    calc ‖aX T n‖ * Real.exp (-(n : ℝ) / Y) * (n : ℝ) ^ (-ρ).re
        ≤ (n : ℝ) * Real.exp (-(n : ℝ) / Y) * 1 := by gcongr
      _ = _ := by ring
  have hsumm : Summable b := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) / Y))
    · obtain ⟨g, hg, hgb, _⟩ := tail_est hY1 (le_refl (0 : ℝ)) 0 (by simp)
      refine (hg.of_nonneg_of_le (fun i => by positivity) (fun i => ?_))
      simpa using hgb i
    · exact hbn
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
  have hYT' : T ≤ Y * T ^ η := by nlinarith
  set M : ℕ := ⌊Y * T ^ η⌋₊ with hM
  set F : ℕ := ⌊T⌋₊ with hF
  have hF1 : 1 ≤ F := Nat.le_floor (by simpa using hT1)
  have hFM : F ≤ M := Nat.floor_le_floor hYT'
  have hsplit := hsumm.sum_add_tsum_nat_add (M + 1)
  have hfin : ∑ n ∈ Finset.range (M + 1), b n =
      b 0 + b 1 + ∑ n ∈ Finset.Ico 2 (F + 1), b n + ∑ n ∈ Finset.Ioc F M, b n := by
    rw [Finset.range_eq_Ico, ← Finset.Ico_add_one_add_one_eq_Ioc,
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ F + 1 by omega) (show F + 1 ≤ M + 1 by omega),
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by omega) (show 2 ≤ F + 1 by omega),
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ 1 by omega) (show 1 ≤ 2 by omega)]
    simp
  have hmid : ∑ n ∈ Finset.Ico 2 (F + 1), b n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnT : (n : ℝ) ≤ T := by
      have : n ≤ F := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
    simp [hb, aX_zero_of hn.1 hnT]
  have hb0 : b 0 = 0 := by simp [hb, aX]
  have hb1 : b 1 = (Real.exp (-1 / Y) : ℂ) := by
    simp [hb, aX_one hT1]
  have hSI : SI T Y η ρ = ∑ n ∈ Finset.Ioc F M, b n := rfl
  have hI : Iser T Y ρ = ∑' n : ℕ, b n := rfl
  have hid : Iser T Y ρ - (Real.exp (-1 / Y) : ℂ) - SI T Y η ρ = ∑' i, b (i + (M + 1)) := by
    rw [hI, ← hsplit, hfin, hmid, hb0, hb1, hSI]
    ring
  rw [hid]
  have hXk : Y * T ^ η ≤ ((M + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (Y * T ^ η)
    push_cast
    linarith
  obtain ⟨g, hg, hgb, hgs⟩ := tail_est hY1 (by positivity) (M + 1) hXk
  have hnorm : ‖∑' i, b (i + (M + 1))‖ ≤ ∑' i, g i :=
    tsum_of_norm_bounded hg.hasSum (fun i => (hbn (i + (M + 1))).trans (hgb i))
  refine hnorm.trans (hgs.trans ?_)
  have e : -(Y * T ^ η) / (2 * Y) = -(T ^ η) / 2 := by field_simp
  rw [e]
  calc Real.exp (-(T ^ η) / 2) * (2 * Y + 1) ^ 2
      ≤ Real.exp (-(T ^ η) / 2) * (2 * T ^ 2 + 1) ^ 2 := by gcongr
    _ ≤ 1 / 100 := hTn

end GuthMaynard.CitedZeros.Ing.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
/-! ## Arithmetic: divisor bound, `a_X`, mollifier mean square, fourth moment -/
lemma pc_kp1_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    (k : ℝ) + 1 ≤ max 1 (1 / (ε * Real.log 2)) * ((2 : ℝ) ^ ε) ^ k := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := ε * Real.log 2 with hc
  have hc0 : 0 < c := by positivity
  have he : ((2 : ℝ) ^ ε) ^ k = Real.exp (k * c) := by
    rw [Real.exp_nat_mul, Real.rpow_def_of_pos (by norm_num), hc, mul_comm (Real.log 2)]
  rw [he]
  have h1 := Real.add_one_le_exp (k * c)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (k : ℝ) + 1 ≤ max 1 (1 / c) * (k * c + 1) := by
    rcases le_total c 1 with h | h
    · have hm : 1 / c ≤ max 1 (1 / c) := le_max_right _ _
      have e : 1 / c * (k * c + 1) = k + 1 / c := by field_simp
      have h1c : 1 ≤ 1 / c := by rw [le_div_iff₀ hc0]; linarith
      calc (k : ℝ) + 1 ≤ k + 1 / c := by linarith
        _ = 1 / c * (k * c + 1) := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)
    · have hm : 1 ≤ max 1 (1 / c) := le_max_left _ _
      calc (k : ℝ) + 1 ≤ 1 * (k * c + 1) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_left _ _)))

theorem divisor_bound (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set C₁ := max 1 (1 / (ε * Real.log 2)) with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_left _ _
  set M : ℝ := (2 : ℝ) ^ (1 / ε) with hM
  set B := ⌈M⌉₊ with hB
  refine ⟨C₁ ^ B, by positivity, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  have hnprod : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  rw [hnprod]
  push_cast
  set D : ℕ → ℝ := fun p => if (p : ℝ) < M then C₁ else 1 with hD
  have hterm : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      D p * ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpM : (p : ℝ) < M
    · simp only [hD, if_pos hpM]
      refine (pc_kp1_le hε _).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _
    · simp only [hD, if_neg hpM, one_mul]
      have hMε : M ^ ε = 2 := by
        rw [hM, ← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        rw [← hMε]; exact Real.rpow_le_rpow (by positivity) (not_lt.1 hpM) hε.le
      have h3 : ((n.factorization p : ℕ) : ℝ) + 1 ≤ 2 ^ (n.factorization p) := by
        have := Nat.lt_two_pow_self (n := n.factorization p)
        exact_mod_cast this
      exact h3.trans (pow_le_pow_left₀ (by norm_num) h2 _)
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (D p * ((p : ℝ) ^ ε) ^ (n.factorization p)) :=
        Finset.prod_le_prod (fun _ _ => by positivity) hterm
    _ = (∏ p ∈ n.primeFactors, D p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) :=
        Finset.prod_mul_distrib
    _ ≤ C₁ ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => by positivity)
        rw [hD, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply pow_le_pow_right₀ hC₁1
        calc (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < M)).card
            ≤ (Finset.range B).card := by
              apply Finset.card_le_card
              intro p hp
              rw [Finset.mem_filter] at hp
              rw [Finset.mem_range]
              have := hp.2.trans_le (Nat.le_ceil M)
              exact_mod_cast this
          _ = B := Finset.card_range B

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
lemma pc_norm_aX_le (X : ℝ) (n : ℕ) : ‖aX X n‖ ≤ n.divisors.card := by
  unfold aX
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X), ‖(ArithmeticFunction.moebius d : ℂ)‖
      ≤ ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [show ((ArithmeticFunction.moebius d : ℤ) : ℂ) = ((ArithmeticFunction.moebius d : ℝ) : ℂ)
          by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = (n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X)).card := by simp
    _ ≤ n.divisors.card := by exact_mod_cast Finset.card_filter_le _ _

theorem aX_sq_sum (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X σ : ℝ, 0 ≤ σ → ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Ioc N (2 * N), ‖aX X n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤
      C * (N : ℝ) ^ (1 - 2 * σ + ε) := by
  obtain ⟨Cd, hCd, hdiv⟩ := divisor_bound (ε / 2) (by linarith)
  refine ⟨Cd ^ 2 * 2 ^ ε, by positivity, fun X σ hσ N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ n ∈ Finset.Ioc N (2 * N), ‖aX X n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤
      Cd ^ 2 * 2 ^ ε * ((N : ℝ) ^ ε * (N : ℝ) ^ (-2 * σ)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (N : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
    have hn0 : (0 : ℝ) < n := by linarith
    have ha : ‖aX X n‖ ≤ Cd * (n : ℝ) ^ (ε / 2) :=
      (pc_norm_aX_le X n).trans (hdiv n (by omega))
    have ha2 : ‖aX X n‖ ^ 2 ≤ Cd ^ 2 * (n : ℝ) ^ ε := by
      calc ‖aX X n‖ ^ 2 ≤ (Cd * (n : ℝ) ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
        _ = Cd ^ 2 * (n : ℝ) ^ ε := by
          have : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ (ε / 2)) 2, ← Real.rpow_mul hn0.le]; norm_num
          rw [mul_pow, this]
    have hpe : (n : ℝ) ^ ε ≤ 2 ^ ε * (N : ℝ) ^ ε := by
      rw [← Real.mul_rpow (by norm_num) hN0.le]
      exact Real.rpow_le_rpow hn0.le hn2 hε.le
    have hps : (n : ℝ) ^ (-2 * σ) ≤ (N : ℝ) ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hN0 hn1 (by linarith)
    calc ‖aX X n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤ (Cd ^ 2 * (2 ^ ε * (N : ℝ) ^ ε)) * (N : ℝ) ^ (-2 * σ) :=
          mul_le_mul (ha2.trans (mul_le_mul_of_nonneg_left hpe (by positivity))) hps
            (by positivity) (by positivity)
      _ = _ := by ring
  calc ∑ n ∈ Finset.Ioc N (2 * N), ‖aX X n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)
      ≤ ∑ n ∈ Finset.Ioc N (2 * N), Cd ^ 2 * 2 ^ ε * ((N : ℝ) ^ ε * (N : ℝ) ^ (-2 * σ)) :=
        Finset.sum_le_sum hterm
    _ = N * (Cd ^ 2 * 2 ^ ε * ((N : ℝ) ^ ε * (N : ℝ) ^ (-2 * σ))) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; congr 1
        rw [Nat.cast_sub (by omega)]; push_cast; ring
    _ = Cd ^ 2 * 2 ^ ε * (N : ℝ) ^ (1 - 2 * σ + ε) := by
        rw [show (1 - 2 * σ + ε) = 1 + ε + (-2 * σ) by ring, Real.rpow_add hN0,
          Real.rpow_add hN0, Real.rpow_one]; ring

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing.PartD
open GuthMaynard.CitedZeros.Ing
/-! ### `gamma_line_bound`, `trunc_small` -/
lemma gamma_left_decay (σ : ℝ) (hσ : 1 / 2 < σ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, σ ≤ β → β ≤ 1 → ∀ u : ℝ,
      (1 + |u|) ^ n * ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C₀, hC₀, hΓ⟩ := gamma_decay (1 / 2) 2 (by norm_num) n
  refine ⟨C₀ / (σ - 1 / 2), div_pos hC₀ (by linarith), fun β hβ hβ1 u => ?_⟩
  set z : ℂ := ((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I with hz
  have hzre : z.re = 1 / 2 - β := by simp [hz]
  have hzim : z.im = u := by simp [hz]
  have hzn : σ - 1 / 2 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre, abs_of_nonpos (by linarith)] at this; linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith
  have hg := hΓ (z + 1) (by simp [hzre]; linarith) (by simp [hzre]; linarith)
  have him : (z + 1).im = u := by simp [hzim]
  rw [him, Complex.Gamma_add_one z hz0, norm_mul] at hg
  rw [le_div_iff₀ (by linarith)]
  calc (1 + |u|) ^ n * ‖Complex.Gamma z‖ * (σ - 1 / 2)
      ≤ (1 + |u|) ^ n * ‖Complex.Gamma z‖ * ‖z‖ := by gcongr
    _ = (1 + |u|) ^ n * (‖z‖ * ‖Complex.Gamma z‖) := by ring
    _ ≤ C₀ := hg

theorem gamma_line_bound (σ : ℝ) (hσ : 1 / 2 < σ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, σ ≤ β → β ≤ 1 →
    ∀ u : ℝ, ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := gamma_left_decay σ hσ 0
  refine ⟨C, hC.le, fun β hβ hβ1 u => ?_⟩
  simpa using h β hβ hβ1 u

lemma zeta_crit_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨Cz, hCz, hζ⟩ := zeta_growth
  have hcont : ContinuousOn (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) (Icc (-2) 2) := by
    intro t _
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp (g := riemannZeta) _ (by fun_prop)
    apply (differentiableAt_riemannZeta _).continuousAt
    intro h; have := congrArg Complex.re h; simp at this
  obtain ⟨B, hB⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨|B| + 2 * Cz, by positivity, fun t => ?_⟩
  by_cases ht : 2 ≤ |t|
  · have hw : ‖(1 / 2 + (t : ℂ) * I : ℂ)‖ ≤ 1 / 2 + |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp
    have := hζ (1 / 2 + (t : ℂ) * I) (by simp) (by simpa using ht)
    calc ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ Cz * (1 + ‖(1 / 2 + (t : ℂ) * I : ℂ)‖) := this
      _ ≤ Cz * (2 * (1 + |t|)) := by gcongr; linarith [abs_nonneg t]
      _ ≤ (|B| + 2 * Cz) * (1 + |t|) := by nlinarith [abs_nonneg B, abs_nonneg t]
  · push Not at ht
    have hmem : t ∈ Icc (-2 : ℝ) 2 := by
      rw [abs_lt] at ht; exact ⟨by linarith, by linarith⟩
    have := hB t hmem
    have hB' : B ≤ |B| := le_abs_self B
    nlinarith [abs_nonneg B, abs_nonneg t]

lemma kII_bound (σ : ℝ) (hσ : 1 / 2 < σ) (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 1 ≤ T →
    ∀ β γ : ℝ, σ ≤ β → β ≤ 1 → 0 ≤ γ → γ ≤ 2 * T → ∀ u : ℝ,
      (1 + |u|) ^ n * kII T β γ u ≤ A * T ^ 2 * (1 + |u|) := by
  obtain ⟨C, hC, hΓ⟩ := gamma_left_decay σ hσ n
  obtain ⟨Cζ, hCζ, hζ⟩ := zeta_crit_bound
  refine ⟨3 * C * Cζ, by positivity, fun T hT β γ hβ hβ1 hγ0 hγ2 u => ?_⟩
  unfold kII
  rw [norm_mul]
  have h1 := hΓ β hβ hβ1 u
  have h2 : ‖molli T (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖ ≤ T :=
    (molli_bound T (by simp)).trans (Nat.floor_le (by linarith))
  have h3 := hζ (γ + u)
  have h4 : 1 + |γ + u| ≤ 3 * T * (1 + |u|) := by
    have := abs_add_le γ u
    rw [abs_of_nonneg hγ0] at this
    nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr hT) (abs_nonneg u)]
  have h5 : ‖riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖ ≤ Cζ * (3 * T * (1 + |u|)) :=
    h3.trans (mul_le_mul_of_nonneg_left h4 hCζ)
  calc (1 + |u|) ^ n * (‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        (‖molli T (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖ *
          ‖riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖))
      = ((1 + |u|) ^ n * ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖) *
        (‖molli T (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖ *
          ‖riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖) := by ring
    _ ≤ C * (T * (Cζ * (3 * T * (1 + |u|)))) :=
        mul_le_mul h1 (mul_le_mul h2 h5 (norm_nonneg _) (by linarith))
          (by positivity) hC.le
    _ = 3 * C * Cζ * T ^ 2 * (1 + |u|) := by ring

lemma kII_continuous (T β γ : ℝ) (hβ0 : 1 / 2 < β) (hβ1 : β < 3 / 2) :
    Continuous (fun u : ℝ => kII T β γ u) := by
  unfold kII
  apply Continuous.mul
  · apply Continuous.norm
    rw [continuous_iff_continuousAt]; intro u
    apply ContinuousAt.comp (g := Complex.Gamma) _ (by fun_prop)
    apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at this; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      linarith
  · apply Continuous.norm
    apply Continuous.mul
    · unfold molli
      apply continuous_finset_sum; intro m hm
      apply Continuous.mul continuous_const
      apply Continuous.const_cpow (by fun_prop) (Or.inl ?_)
      have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      exact_mod_cast (by omega : m ≠ 0)
    · rw [continuous_iff_continuousAt]; intro u
      apply ContinuousAt.comp (g := riemannZeta) _ (by fun_prop)
      apply (differentiableAt_riemannZeta _).continuousAt
      intro h; have := congrArg Complex.re h; simp at this

theorem trunc_small (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ β γ : ℝ, σ ≤ β → β < 1 → T ≤ γ → γ ≤ 2 * T →
      Integrable (fun u : ℝ => kII T β γ u) ∧
        ∫ u : ℝ, kII T β γ u ≤ (∫ u in -(T ^ η)..(T ^ η), kII T β γ u) + 1 := by
  set m : ℕ := ⌈2 / η⌉₊ + 1 with hm
  obtain ⟨A, hA, hk⟩ := kII_bound σ hσ (m + 3)
  have hev : ∀ᶠ T : ℝ in atTop, A * Real.pi ≤ T ^ η ∧ 1 ≤ T :=
    ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (A * Real.pi))).and
      (eventually_ge_atTop 1)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨T₀, fun T hT β γ hβ hβ1 hγ1 hγ2 => ?_⟩
  obtain ⟨hTA, hT1⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith
  set L := T ^ η with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hT1 hη.le
  have hnn : ∀ u, 0 ≤ kII T β γ u := fun u => by unfold kII; positivity
  -- pointwise: `kII · (1+u²)(1+|u|)^m ≤ A T²`
  have hb' : ∀ u : ℝ, kII T β γ u * ((1 + u ^ 2) * (1 + |u|) ^ m) ≤ A * T ^ 2 := by
    intro u
    have h := hk T hT1 β γ hβ hβ1.le (by linarith) hγ2 u
    have hpos : 0 < 1 + |u| := by positivity
    have h' : (1 + |u|) ^ (m + 2) * kII T β γ u ≤ A * T ^ 2 := by
      have e : (1 + |u|) ^ (m + 3) * kII T β γ u =
          ((1 + |u|) ^ (m + 2) * kII T β γ u) * (1 + |u|) := by ring
      rw [e] at h
      exact le_of_mul_le_mul_right h hpos
    have hsq := one_add_sq_le u
    have : (1 + u ^ 2) * (1 + |u|) ^ m ≤ (1 + |u|) ^ (m + 2) := by
      calc (1 + u ^ 2) * (1 + |u|) ^ m ≤ (1 + |u|) ^ 2 * (1 + |u|) ^ m :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (1 + |u|) ^ (m + 2) := by ring
    calc kII T β γ u * ((1 + u ^ 2) * (1 + |u|) ^ m)
        ≤ kII T β γ u * (1 + |u|) ^ (m + 2) := mul_le_mul_of_nonneg_left this (hnn u)
      _ = (1 + |u|) ^ (m + 2) * kII T β γ u := by ring
      _ ≤ A * T ^ 2 := h'
  have hb1 : ∀ u : ℝ, kII T β γ u ≤ A * T ^ 2 * (1 + u ^ 2)⁻¹ := by
    intro u
    have h1 : 1 ≤ (1 + |u|) ^ m := one_le_pow₀ (by linarith [abs_nonneg u])
    have := hb' u
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (hnn u) (by positivity : (0 : ℝ) ≤ 1 + u ^ 2))]
  have hcont := kII_continuous T β γ (by linarith) (by linarith)
  have hint : Integrable (fun u => kII T β γ u) := by
    refine (integrable_inv_one_add_sq.const_mul (A * T ^ 2)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (hnn u)]; exact hb1 u
  refine ⟨hint, ?_⟩
  -- the tail constant
  have hLm : A * Real.pi * T ^ 2 ≤ L ^ m := by
    have hm' : 2 + η ≤ η * m := by
      have hc : 2 / η ≤ (⌈2 / η⌉₊ : ℝ) := Nat.le_ceil _
      rw [hm]; push_cast
      have : 2 ≤ η * ⌈2 / η⌉₊ := by
        rw [div_le_iff₀ hη] at hc; linarith
      nlinarith
    have e1 : L ^ m = T ^ (η * m) := by
      rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    have e2 : T ^ (2 + η) = T ^ 2 * L := by
      rw [Real.rpow_add hT0, hL]; norm_cast
    have h3 : T ^ (2 + η) ≤ T ^ (η * m) := Real.rpow_le_rpow_of_exponent_le hT1 hm'
    rw [e1]
    calc A * Real.pi * T ^ 2 ≤ L * T ^ 2 := by gcongr
      _ = T ^ (2 + η) := by rw [e2]; ring
      _ ≤ _ := h3
  have hLm0 : 0 < L ^ m := by positivity
  set B : ℝ := A * T ^ 2 / L ^ m with hB
  have hBpi : B * Real.pi ≤ 1 := by
    rw [hB, div_mul_eq_mul_div, div_le_one hLm0]; linarith
  rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L),
    ← integral_add_compl (measurableSet_Ioc : MeasurableSet (Ioc (-L) L)) hint]
  have hgi : Integrable (fun u : ℝ => B * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  have h1 : ∫ u in (Ioc (-L) L)ᶜ, kII T β γ u ≤ ∫ u in (Ioc (-L) L)ᶜ, B * (1 + u ^ 2)⁻¹ := by
    refine setIntegral_mono_on hint.integrableOn hgi.integrableOn measurableSet_Ioc.compl
      (fun u hu => ?_)
    have hLu : L ≤ |u| := by
      by_contra hc
      push Not at hc
      rw [abs_lt] at hc
      exact hu ⟨hc.1, hc.2.le⟩
    have hpow : L ^ m ≤ (1 + |u|) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have := hb' u
    rw [show B * (1 + u ^ 2)⁻¹ = A * T ^ 2 / ((1 + u ^ 2) * L ^ m) by
      rw [hB]; field_simp]
    rw [le_div_iff₀ (by positivity)]
    calc kII T β γ u * ((1 + u ^ 2) * L ^ m)
        ≤ kII T β γ u * ((1 + u ^ 2) * (1 + |u|) ^ m) := by
          apply mul_le_mul_of_nonneg_left _ (hnn u)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ A * T ^ 2 := this
  have h2 : ∫ u in (Ioc (-L) L)ᶜ, B * (1 + u ^ 2)⁻¹ ≤ ∫ u, B * (1 + u ^ 2)⁻¹ :=
    setIntegral_le_integral hgi (ae_of_all _ fun u => by
      have : 0 ≤ B := by rw [hB]; positivity
      positivity)
  have h3 : ∫ u : ℝ, B * (1 + u ^ 2)⁻¹ = B * Real.pi := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  linarith

end GuthMaynard.CitedZeros.Ing.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing.PartD
open GuthMaynard.CitedZeros.Ing
/-! ### `detect` -/
lemma lineInt_upper (T Y : ℝ) (hY : 0 < Y) (ρ : ℂ) :
    ‖lineInt T Y ρ (1 / 2 - ρ.re)‖ ≤
      1 / (2 * Real.pi) * (Y ^ (1 / 2 - ρ.re) * ∫ u : ℝ, kII T ρ.re ρ.im u) := by
  rw [lineInt_eq, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  gcongr
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  rw [← integral_const_mul]
  congr 1
  funext u
  have e : ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I) = 1 / 2 + ((ρ.im + u : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  unfold Ff kII
  rw [e]
  simp only [norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  ring

theorem detect (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, T ≤ Y → Y ≤ T ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → σ ≤ ρ.re → T ≤ ρ.im → ρ.im ≤ 2 * T →
        IsTypeI T Y η ρ ∨ IsTypeII σ T Y η ρ := by
  obtain ⟨K, hK0, hK⟩ := detect_shift
  obtain ⟨T₁, hT₁⟩ := res_small (1 / 100 / (K + 1)) (by positivity)
  obtain ⟨T₂, hT₂⟩ := tail_small η hη
  obtain ⟨T₃, hT₃⟩ := trunc_small σ hσ hσ1 η hη
  refine ⟨max (max T₁ T₂) (max T₃ 100), fun T hT Y hTY hYT ρ h0 hβ hγ1 hγ2 => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT100 : (100 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hY100 : (100 : ℝ) ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hρ0 : 0 < ρ.re := by linarith
  have hρ1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h h0
  by_cases hI : IsTypeI T Y η ρ
  · exact Or.inl hI
  right
  unfold IsTypeI at hI
  push Not at hI
  have hR := hT₁ T hT1 Y hTY hYT ρ hρ0 hρ1 hγ1
  have hKR : K * ‖Res T Y ρ‖ ≤ 1 / 100 := by
    calc K * ‖Res T Y ρ‖ ≤ K * (1 / 100 / (K + 1)) := by gcongr
      _ ≤ 1 / 100 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith
  have hsh := hK T Y (by linarith) (by linarith) ρ h0 hρ0 hρ1 (by linarith)
  have htail := hT₂ T hT2 Y hTY hYT ρ hρ0
  have hexp : 99 / 100 ≤ Real.exp (-1 / Y) := by
    have h1 := Real.add_one_le_exp (-1 / Y)
    have h2 : 1 / Y ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h3 : -1 / Y = -(1 / Y) := by ring
    linarith
  have hIs : 48 / 100 ≤ ‖Iser T Y ρ‖ := by
    have e1 : (Real.exp (-1 / Y) : ℂ) = Iser T Y ρ -
        (Iser T Y ρ - (Real.exp (-1 / Y) : ℂ) - SI T Y η ρ) - SI T Y η ρ := by ring
    have e2 : ‖(Real.exp (-1 / Y) : ℂ)‖ = Real.exp (-1 / Y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h3 := norm_sub_le (Iser T Y ρ -
        (Iser T Y ρ - (Real.exp (-1 / Y) : ℂ) - SI T Y η ρ)) (SI T Y η ρ)
    have h4 := norm_sub_le (Iser T Y ρ)
        (Iser T Y ρ - (Real.exp (-1 / Y) : ℂ) - SI T Y η ρ)
    rw [← e1, e2] at h3
    linarith
  have hL : 47 / 100 ≤ ‖lineInt T Y ρ (1 / 2 - ρ.re)‖ := by
    have := norm_sub_norm_le (Iser T Y ρ) (Iser T Y ρ - lineInt T Y ρ (1 / 2 - ρ.re))
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hsh
    linarith
  have hU := lineInt_upper T Y hY0 ρ
  obtain ⟨_, htr⟩ := hT₃ T hT3 ρ.re ρ.im hβ hρ1 hγ1 hγ2
  unfold IsTypeII
  set J := ∫ u : ℝ, kII T ρ.re ρ.im u with hJ
  set a := Y ^ (ρ.re - 1 / 2) with ha
  have hY1 : 1 ≤ Y := by linarith
  have hb1 : 1 ≤ Y ^ (σ - 1 / 2) := Real.one_le_rpow hY1 (by linarith)
  have hab : Y ^ (σ - 1 / 2) ≤ a := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have ha0 : 0 < a := by positivity
  have hinv : Y ^ (1 / 2 - ρ.re) = a⁻¹ := by
    rw [ha, ← Real.rpow_neg hY0.le]; ring_nf
  rw [hinv] at hU
  have hJa : 47 / 100 * (2 * Real.pi) * a ≤ J := by
    have h1 : 47 / 100 ≤ 1 / (2 * Real.pi) * (a⁻¹ * J) := hL.trans hU
    have h2 : 1 / (2 * Real.pi) * (a⁻¹ * J) = J / (2 * Real.pi * a) := by
      field_simp
    rw [h2, le_div_iff₀ (by positivity)] at h1
    linarith
  have hpi := Real.pi_gt_three
  nlinarith

end GuthMaynard.CitedZeros.Ing.PartD
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
alias detect := GuthMaynard.CitedZeros.Ing.PartD.detect

/-! ## Step 3: Type II zeros (fourth moment) -/
alias gamma_line_bound := GuthMaynard.CitedZeros.Ing.PartD.gamma_line_bound

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem fourth_moment (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
    ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤ C * T ^ (1 + ε) := by
  have h := LindelofHypothesis.moment_bound_of_k_le_two 2 (Or.inr rfl) ε hε
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hc
  refine ⟨max c 0, max T₁ 1, le_max_right _ _, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  set I0 := ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 4 with hI0
  have hb : ‖1 / T * I0‖ ≤ c * T ^ ε := by
    have := hT₁ T ((le_max_left _ _).trans hT)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le ε)] at this
    simpa only [show (2 : ℕ) * 2 = 4 from rfl] using this
  have h1 : I0 ≤ T * ‖1 / T * I0‖ := by
    rw [norm_mul, Real.norm_of_nonneg (by positivity), ← mul_assoc, mul_one_div_cancel hT0.ne',
      one_mul]
    exact le_abs_self I0
  have h2 : T * ‖1 / T * I0‖ ≤ T * (c * T ^ ε) := mul_le_mul_of_nonneg_left hb hT0.le
  have h3 : T * (c * T ^ ε) ≤ max c 0 * T ^ (1 + ε) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
    have : c * T ^ ε ≤ max c 0 * T ^ ε := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith
  linarith

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem molli_mean_square (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖molli X (1 / 2 + (t : ℂ) * I)‖ ^ 2 ≤
      (T + 4 * X * (1 + Real.log X)) * (1 + Real.log X) := by
  set N := ⌊X⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set c : ℕ → ℂ := fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-(1 / 2 : ℂ)) with hc
  have hmv := (ArtinPrimitiveRoots.dirichlet_mean_value (Finset.Icc 1 N) N
    (fun n hn => Finset.mem_Icc.1 hn) c).1 (-T) 0 (by linarith)
  have heq : ∀ t : ℝ, molli X (1 / 2 + (t : ℂ) * I) =
      ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) := by
    intro t
    unfold molli
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (m : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hm).1; exact_mod_cast (by omega : m ≠ 0)
    simp only [hc]
    rw [mul_assoc, ← Complex.cpow_add _ _ hm0]
    congr 2
    push_cast; ring
  have hint : (∫ t in (0 : ℝ)..T, ‖molli X (1 / 2 + (t : ℂ) * I)‖ ^ 2) =
      ∫ t in (-T)..0, ‖∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 := by
    simp_rw [heq]
    rw [intervalIntegral.integral_comp_neg
      (fun t : ℝ => ‖∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2)]
    simp
  rw [hint]
  refine hmv.trans ?_
  have hsum : ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 ≤ 1 + Real.log X := by
    calc ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn0 : 0 < n := by have := (Finset.mem_Icc.1 hn).1; omega
          simp only [hc, norm_mul]
          rw [norm_natCast_cpow_of_pos hn0]
          have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
            rw [show ((ArithmeticFunction.moebius n : ℤ) : ℂ) =
              ((ArithmeticFunction.moebius n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
              Real.norm_eq_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
          rw [hre]
          have hp : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
            exact Real.rpow_neg_one _
          rw [mul_pow, hp]
          have : ‖(ArithmeticFunction.moebius n : ℂ)‖ ^ 2 ≤ 1 := by
            nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ)]
          have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
          nlinarith
      _ = (harmonic N : ℝ) := by
          rw [harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log X := by linarith [Real.log_le_log hN0 hNX]
  have hlogN : Real.log N ≤ Real.log X := Real.log_le_log hN0 hNX
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hA : 0 - -T + 4 * (N : ℝ) * (1 + Real.log N) ≤ T + 4 * X * (1 + Real.log X) := by
    have : (N : ℝ) * (1 + Real.log N) ≤ X * (1 + Real.log X) :=
      mul_le_mul hNX (by linarith) (by linarith) (by linarith)
    linarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hXl : 0 ≤ X * (1 + Real.log X) := mul_nonneg (by linarith) (by linarith)
  exact mul_le_mul hA hsum hS0 (by linarith)

/-! ## Subharmonicity -/
lemma pc_circle_mean (f : ℂ → ℂ) (z : ℂ) (r : ℝ)
    (hf : DifferentiableOn ℂ f (closedBall z r)) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    2 * Real.pi * ‖f z‖ ^ 2 ≤ ∫ θ in (-Real.pi)..Real.pi, ‖f (circleMap z ρ θ)‖ ^ 2 := by
  set h : ℂ → ℂ := fun w => f w ^ 2 with hh
  have hd : DiffContOnCl ℂ h (ball z |ρ|) := by
    rw [abs_of_pos hρ]
    refine ⟨?_, ?_⟩
    · exact (hf.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hρr))).pow 2
    · rw [closure_ball z hρ.ne']
      exact (hf.continuousOn.mono (closedBall_subset_closedBall hρr)).pow 2
  have hca := hd.circleAverage
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ => h (circleMap z ρ θ))] at hca
  have e1 : (0 : ℝ) + -Real.pi = -Real.pi := by ring
  have e2 : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [e1, e2] at hca
  have hn : ‖h z‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, ‖h (circleMap z ρ θ)‖ := by
    rw [← hca, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos]))
      (by positivity)
  have hz : ‖h z‖ = ‖f z‖ ^ 2 := by simp [hh, norm_pow]
  have hθ : ∀ θ, ‖h (circleMap z ρ θ)‖ = ‖f (circleMap z ρ θ)‖ ^ 2 := fun θ => by
    simp [hh, norm_pow]
  simp_rw [hθ] at hn
  rw [hz] at hn
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [← div_eq_inv_mul, le_div_iff₀ hpi] at hn
  linarith

theorem disc_avg (f : ℂ → ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z r)) :
    Real.pi * r ^ 2 * ‖f z‖ ^ 2 ≤ ∫ w in Metric.ball z r, ‖f w‖ ^ 2 := by
  classical
  set g : ℂ → ℝ := fun w => ‖f w‖ ^ 2 with hg
  have hfc : ContinuousOn f (closedBall z r) := hf.continuousOn
  have hgc : ContinuousOn g (closedBall z r) := hfc.norm.pow 2
  have hint : IntegrableOn g (ball z r) :=
    (hgc.integrableOn_compact (isCompact_closedBall z r)).mono_set ball_subset_closedBall
  have hg0 : ∀ w, 0 ≤ g w := fun w => by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hint.aestronglyMeasurable]
  have hfin : ∫⁻ w in ball z r, ENNReal.ofReal (g w) ≠ ⊤ :=
    hint.lintegral_lt_top.ne
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  set G : ℂ → ℝ≥0∞ := (ball (0 : ℂ) r).piecewise (fun v => ENNReal.ofReal (g (z + v))) 0 with hG
  have hmaps : MapsTo (fun v : ℂ => z + v) (ball (0 : ℂ) r) (closedBall z r) := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hv.le
  have hGm : Measurable G := by
    apply ContinuousOn.measurable_piecewise _ continuousOn_const measurableSet_ball
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (hgc.comp (continuousOn_const.add continuousOn_id) hmaps)
  have htrans : ∫⁻ w in ball z r, ENNReal.ofReal (g w) = ∫⁻ v, G v := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self (fun w => (ball z r).indicator (fun w => ENNReal.ofReal (g w)) w) z]
    congr 1; ext v
    have hiff : z + v ∈ ball z r ↔ v ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, mem_ball_zero_iff]
    by_cases hv : v ∈ ball (0 : ℂ) r
    · simp only [hG, Set.piecewise_eq_of_mem _ _ _ hv, Set.indicator_of_mem (hiff.2 hv)]
    · simp only [hG, Set.piecewise_eq_of_notMem _ _ _ hv,
        Set.indicator_of_notMem (fun h => hv (hiff.1 h)), Pi.zero_apply]
  rw [htrans, ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  have hFm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi))) := by
    refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).smul (hGm.comp ?_)
    have : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
        fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I) := funext Complex.polarCoord_symm_apply
    rw [this]
    fun_prop
  rw [lintegral_prod _ hFm]
  have hinner : ∀ ρ ∈ Ioo 0 r, ENNReal.ofReal ρ * ENNReal.ofReal (2 * Real.pi * ‖f z‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (ρ, θ).1 • G (Complex.polarCoord.symm (ρ, θ)) := by
    intro ρ hρ
    have hφc : Continuous (fun θ => g (circleMap z ρ θ)) := by
      refine hgc.comp_continuous (continuous_circleMap z ρ) fun θ => ?_
      rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hρ.1]; exact hρ.2.le
    have hpt : ∀ θ, ENNReal.ofReal (ρ, θ).1 • G (Complex.polarCoord.symm (ρ, θ)) =
        ENNReal.ofReal ρ * ENNReal.ofReal (g (circleMap z ρ θ)) := by
      intro θ
      have hmem : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hρ.1]; exact hρ.2
      simp only [hG, Set.piecewise_eq_of_mem _ _ _ hmem, smul_eq_mul]
      congr 3
      rw [Complex.polarCoord_symm_apply, circleMap]
      rw [show (θ : ℂ) * I = (θ : ℂ) * I from rfl, Complex.exp_mul_I]
      push_cast; ring
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hφc.integrableOn_Icc).mono_set Ioo_subset_Icc_self) (Eventually.of_forall fun _ => hg0 _)]
    apply ENNReal.ofReal_le_ofReal
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact pc_circle_mean f z r hf ρ hρ.1 hρ.2.le
  calc ENNReal.ofReal (Real.pi * r ^ 2 * ‖f z‖ ^ 2)
      = (∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ) * ENNReal.ofReal (2 * Real.pi * ‖f z‖ ^ 2) := by
        have hlin : ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ = ENNReal.ofReal (r ^ 2 / 2) := by
          have hI : IntegrableOn (fun x : ℝ => x) (Ioo (0 : ℝ) r) :=
            (continuous_id'.integrableOn_Icc (a := (0 : ℝ)) (b := r)).mono_set Ioo_subset_Icc_self
          have := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioo (0 : ℝ) r))
            (f := fun x : ℝ => x) hI
            (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => hx.1.le)
          rw [← this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_id]
          congr 1; ring
        rw [hlin, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ = ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ * ENNReal.ofReal (2 * Real.pi * ‖f z‖ ^ 2) :=
        (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ρ in Ioo 0 r, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (ρ, θ).1 • G (Complex.polarCoord.symm (ρ, θ)) :=
        setLIntegral_mono_ae' measurableSet_Ioo (Eventually.of_forall hinner)
    _ ≤ ∫⁻ ρ in Ioi 0, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (ρ, θ).1 • G (Complex.polarCoord.symm (ρ, θ)) :=
        lintegral_mono_set Ioo_subset_Ioi_self

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
/-! ## Step 2: Type I zeros (large values) -/

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
/-! ## Large values -/
lemma pc_setIntegral_reProdIm (F : ℂ → ℝ) (A B : Set ℝ) (hF : IntegrableOn F (A ×ℂ B)) :
    ∫ z in A ×ℂ B, F z = ∫ x in A, ∫ y in B, F (x + y * I) := by
  have e := Complex.volume_preserving_equiv_real_prod.symm _
  have hsymm : ∀ p : ℝ × ℝ, (measurableEquivRealProd.symm p : ℂ) = p.1 + p.2 * I := by
    intro p; simp [measurableEquivRealProd, Complex.equivRealProdCLM_symm_apply]
  have hpre : (measurableEquivRealProd.symm : ℝ × ℝ → ℂ) ⁻¹' (A ×ℂ B) = A ×ˢ B := by
    ext p; simp only [mem_preimage, hsymm, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, add_im, mul_im, mem_prod]; simp
  rw [← e.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _), hpre]
  rw [← e.integrableOn_comp_preimage (MeasurableEquiv.measurableEmbedding _), hpre] at hF
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [setIntegral_prod (f := fun p => F (measurableEquivRealProd.symm p)) hF]
  simp_rw [hsymm]

lemma pc_line_mv (N : ℕ) (b : ℕ → ℂ) (x y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
    ∫ y in Icc y₁ y₂, ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ (-((x : ℂ) + (y : ℂ) * I))‖ ^ 2 ≤
      (y₂ - y₁ + 4 * (2 * N) * (1 + Real.log (2 * N))) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * x) := by
  set c : ℕ → ℂ := fun n => b n * (n : ℂ) ^ (-(x : ℂ)) with hc
  have hmv := (ArtinPrimitiveRoots.dirichlet_mean_value (Finset.Ioc N (2 * N)) (2 * N)
    (fun n hn => by rw [Finset.mem_Ioc] at hn; exact ⟨by omega, hn.2⟩) c).1 (-y₂) (-y₁) (by linarith)
  have heq : ∀ y : ℝ, ∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ (-((x : ℂ) + (y : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc N (2 * N), c n * (n : ℂ) ^ (Complex.I * ((-y : ℝ) : ℂ)) := by
    intro y
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Ioc] at hn; exact_mod_cast (by omega : n ≠ 0)
    simp only [hc]
    rw [mul_assoc, ← Complex.cpow_add _ _ hn0]
    congr 2; push_cast; ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_neg
    (fun y : ℝ => ‖∑ n ∈ Finset.Ioc N (2 * N), c n * (n : ℂ) ^ (Complex.I * (y : ℂ))‖ ^ 2)]
  refine hmv.trans (le_of_eq ?_)
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := by rw [Finset.mem_Ioc] at hn; omega
    simp only [hc, norm_mul, mul_pow]
    rw [norm_natCast_cpow_of_pos hn0]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; simp; ring

theorem large_values_points : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ T : ℝ, 0 ≤ σ → 1 ≤ T →
    ∀ (N : ℕ) (b : ℕ → ℂ) (P : Finset ℂ),
      (∀ s ∈ P, σ ≤ s.re ∧ s.re ≤ 1 ∧ T ≤ s.im ∧ s.im ≤ 2 * T) →
      (∀ s ∈ P, ∀ s' ∈ P, s ≠ s' → 1 ≤ |s.im - s'.im|) →
      ∑ s ∈ P, ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ (-s)‖ ^ 2 ≤
        C * Real.log (N + 2) ^ 2 * (T + N * Real.log (N + 2)) *
          ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  refine ⟨1728, by norm_num, fun σ T hσ hT N b P hP hsep => ?_⟩
  set S := ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) hS0
  have hRHS0 : 0 ≤ 1728 * Real.log (N + 2) ^ 2 * (T + N * Real.log (N + 2)) * S := by
    have : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
    have : 0 ≤ T + N * Real.log ((N : ℝ) + 2) := by positivity
    positivity
  rcases P.eq_empty_or_nonempty with hPe | ⟨s₀, hs₀⟩
  · subst hPe; simpa using hRHS0
  have hσ1 : σ ≤ 1 := (hP s₀ hs₀).1.trans (hP s₀ hs₀).2.1
  set D : ℂ → ℂ := fun s => ∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ (-s) with hD
  have hDd : Differentiable ℂ D := by
    have : ∀ n ∈ Finset.Ioc N (2 * N), Differentiable ℂ (fun s : ℂ => b n * (n : ℂ) ^ (-s)) := by
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        rw [Finset.mem_Ioc] at hn; exact_mod_cast (by omega : n ≠ 0)
      exact (differentiable_neg.const_cpow (Or.inl hn0)).const_mul (b n)
    simpa [hD] using Differentiable.fun_sum this
  set L := Real.log (N + 2) with hLdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  set δ := 1 / (4 * L) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set R := Icc (σ - δ) (1 + δ) ×ℂ Icc (T - 1) (2 * T + 1) with hR
  have hcont : Continuous (fun w => ‖D w‖ ^ 2) := hDd.continuous.norm.pow 2
  have hRint : IntegrableOn (fun w => ‖D w‖ ^ 2) R :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.reProdIm isCompact_Icc)
  have hball : ∀ s ∈ P, ball s δ ⊆ R := by
    intro s hs w hw
    obtain ⟨h1, h2, h3, h4⟩ := hP s hs
    rw [mem_ball, dist_eq_norm] at hw
    have hre := (abs_le.1 ((Complex.abs_re_le_norm (w - s)).trans hw.le))
    have him := (abs_le.1 ((Complex.abs_im_le_norm (w - s)).trans hw.le))
    simp only [sub_re, sub_im] at hre him
    rw [hR, mem_reProdIm, mem_Icc, mem_Icc]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hdisj : (P : Set ℂ).Pairwise (Function.onFun Disjoint fun s => ball s δ) := by
    intro s hs s' hs' hne
    rw [Function.onFun, Set.disjoint_left]
    intro w hw hw'
    rw [mem_ball, dist_eq_norm] at hw hw'
    have a1 := (Complex.abs_im_le_norm (w - s)).trans hw.le
    have a2 := (Complex.abs_im_le_norm (w - s')).trans hw'.le
    simp only [sub_im] at a1 a2
    have := hsep s hs s' hs' hne
    have : |s.im - s'.im| ≤ |w.im - s.im| + |w.im - s'.im| := by
      rw [abs_sub_comm w.im s.im]; exact abs_sub_le _ _ _
    linarith
  have hunion : ∑ s ∈ P, ∫ w in ball s δ, ‖D w‖ ^ 2 = ∫ w in ⋃ s ∈ P, ball s δ, ‖D w‖ ^ 2 :=
    (integral_biUnion_finset P (fun _ _ => measurableSet_ball) hdisj
      (fun s hs => hRint.mono_set (hball s hs))).symm
  have hmono : ∫ w in ⋃ s ∈ P, ball s δ, ‖D w‖ ^ 2 ≤ ∫ w in R, ‖D w‖ ^ 2 :=
    setIntegral_mono_set hRint (Eventually.of_forall fun _ => by positivity)
      (Eventually.of_forall (iUnion₂_subset hball))
  have hfub := pc_setIntegral_reProdIm (fun w => ‖D w‖ ^ 2) _ _ hRint
  set M := (T + 2 + 4 * (2 * N) * (1 + Real.log (2 * N))) * (3 * S) with hM
  have hlog2N : Real.log (2 * N) ≤ 2 * L := by
    rw [hLdef, ← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hcmp : ∀ x ∈ Icc (σ - δ) (1 + δ), ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * x) ≤
      3 * S := by
    intro x hx
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
    have hn0 : (0 : ℝ) < n := by linarith
    have e1 : (n : ℝ) ^ (-2 * x) = (n : ℝ) ^ (-2 * σ) * (n : ℝ) ^ (2 * (σ - x)) := by
      rw [← Real.rpow_add hn0]; ring_nf
    have e2 : (n : ℝ) ^ (2 * (σ - x)) ≤ (n : ℝ) ^ (2 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hx.1])
    have e3 : (n : ℝ) ^ (2 * δ) ≤ 3 := by
      rw [Real.rpow_def_of_pos hn0]
      have hl : Real.log n ≤ 2 * L := (Real.log_le_log hn0 hn2).trans hlog2N
      have : Real.log n * (2 * δ) ≤ 1 := by
        have : Real.log n * (2 * δ) ≤ 2 * L * (2 * δ) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        have h4 : 2 * L * (2 * δ) = 1 := by rw [hδdef]; field_simp; ring
        linarith
      calc Real.exp (Real.log n * (2 * δ)) ≤ Real.exp 1 := Real.exp_le_exp.2 this
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    rw [e1]
    have : 0 ≤ ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by positivity
    calc ‖b n‖ ^ 2 * ((n : ℝ) ^ (-2 * σ) * (n : ℝ) ^ (2 * (σ - x)))
        = (‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) * (n : ℝ) ^ (2 * (σ - x)) := by ring
      _ ≤ (‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) * 3 :=
          mul_le_mul_of_nonneg_left (e2.trans e3) this
      _ = _ := by ring
  have hline : ∀ x ∈ Icc (σ - δ) (1 + δ),
      ‖∫ y in Icc (T - 1) (2 * T + 1), ‖D (x + y * I)‖ ^ 2‖ ≤ M := by
    intro x hx
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity)]
    have h1 := pc_line_mv N b x (T - 1) (2 * T + 1) (by linarith)
    have h2 := hcmp x hx
    have hpos : 0 ≤ 2 * T + 1 - (T - 1) + 4 * (2 * (N : ℝ)) * (1 + Real.log (2 * N)) := by
      have : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
      have : 0 ≤ 4 * (2 * (N : ℝ)) * (1 + Real.log (2 * N)) := by positivity
      linarith
    calc ∫ y in Icc (T - 1) (2 * T + 1), ‖D (x + y * I)‖ ^ 2
        = ∫ y in Icc (T - 1) (2 * T + 1), ‖∑ n ∈ Finset.Ioc N (2 * N),
            b n * (n : ℂ) ^ (-((x : ℂ) + (y : ℂ) * I))‖ ^ 2 := rfl
      _ ≤ _ := h1
      _ ≤ (2 * T + 1 - (T - 1) + 4 * (2 * N) * (1 + Real.log (2 * N))) * (3 * S) :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = M := by rw [hM]; ring
  have hx : ∫ x in Icc (σ - δ) (1 + δ), ∫ y in Icc (T - 1) (2 * T + 1), ‖D (x + y * I)‖ ^ 2 ≤
      M * (3 / 2) := by
    refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
      hline).trans ?_)
    rw [Real.volume_real_Icc_of_le (by linarith)]
    have hM0 : 0 ≤ M := by
      have : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
      rw [hM]; positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hM0
  have hsum : Real.pi * δ ^ 2 * ∑ s ∈ P, ‖D s‖ ^ 2 ≤ M * (3 / 2) := by
    rw [Finset.mul_sum]
    calc ∑ s ∈ P, Real.pi * δ ^ 2 * ‖D s‖ ^ 2 ≤ ∑ s ∈ P, ∫ w in ball s δ, ‖D w‖ ^ 2 :=
          Finset.sum_le_sum fun s _ => disc_avg D s δ hδ0 hDd.differentiableOn
      _ ≤ M * (3 / 2) := by
          rw [hunion]; refine hmono.trans ?_
          rw [hfub]; exact hx
  have hMb : M ≤ 72 * (T + N * L) * S := by
    have : T + 2 + 4 * (2 * N) * (1 + Real.log (2 * N)) ≤ 24 * (T + N * L) := by nlinarith
    rw [hM]; nlinarith
  set X := ∑ s ∈ P, ‖D s‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hδL : 16 * L ^ 2 * δ ^ 2 = 1 := by rw [hδdef]; field_simp; ring
  show X ≤ 1728 * L ^ 2 * (T + N * L) * S
  have h1 : X ≤ 16 * L ^ 2 * (Real.pi * δ ^ 2 * X) := by
    have : 16 * L ^ 2 * (Real.pi * δ ^ 2 * X) = Real.pi * X := by
      rw [show 16 * L ^ 2 * (Real.pi * δ ^ 2 * X) = (16 * L ^ 2 * δ ^ 2) * (Real.pi * X) by ring,
        hδL, one_mul]
    rw [this]; nlinarith
  have hL0 : 0 ≤ 16 * L ^ 2 := by positivity
  calc X ≤ 16 * L ^ 2 * (Real.pi * δ ^ 2 * X) := h1
    _ ≤ 16 * L ^ 2 * (M * (3 / 2)) := mul_le_mul_of_nonneg_left hsum hL0
    _ ≤ 16 * L ^ 2 * (72 * (T + N * L) * S * (3 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hL0
    _ = 1728 * L ^ 2 * (T + N * L) * S := by ring

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
/-! ## Overlap + Hölder -/
lemma pc_cs (μ : Measure ℝ) (u v : ℝ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hv0 : ∀ t, 0 ≤ v t)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ t, u t * v t ∂μ) ^ 2 ≤ (∫ t, u t ^ 2 ∂μ) * (∫ t, v t ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Eventually.of_forall hu0)
    (Eventually.of_forall hv0) (by simpa using hu) (by simpa using hv)
  simp_rw [Real.rpow_two] at h
  have hA : 0 ≤ ∫ t, u t ^ 2 ∂μ := integral_nonneg fun t => by positivity
  have hB : 0 ≤ ∫ t, v t ^ 2 ∂μ := integral_nonneg fun t => by positivity
  have h0 : 0 ≤ ∫ t, u t * v t ∂μ := integral_nonneg fun t => mul_nonneg (hu0 t) (hv0 t)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hA] at h
  calc (∫ t, u t * v t ∂μ) ^ 2 ≤ (Real.sqrt ((∫ t, u t ^ 2 ∂μ) * ∫ t, v t ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = _ := Real.sq_sqrt (mul_nonneg hA hB)

theorem overlap_holder (f g : ℝ → ℂ) (a b L B : ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b)) (hL : 0 ≤ L) (F : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ ρ ∈ F, 0 ≤ w ρ) (hsub : ∀ ρ ∈ F, a ≤ ρ.im - L ∧ ρ.im + L ≤ b)
    (hB : ∀ t : ℝ, ∑ ρ ∈ F.filter (fun ρ => |ρ.im - t| ≤ L), w ρ ≤ B) :
    ∑ ρ ∈ F, w ρ * ∫ t in (ρ.im - L)..(ρ.im + L), ‖f t‖ * ‖g t‖ ≤
      B * (∫ t in a..b, ‖f t‖ ^ 4) ^ (1 / 4 : ℝ) * (∫ t in a..b, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ) *
        (2 * L * F.card) ^ (1 / 4 : ℝ) := by
  classical
  rcases F.eq_empty_or_nonempty with hF | ⟨ρ₀, hρ₀⟩
  · subst hF; simp
  have hab : a ≤ b := by have := hsub ρ₀ hρ₀; linarith
  have hB0 : 0 ≤ B :=
    (Finset.sum_nonneg fun ρ hρ => hw ρ (Finset.mem_filter.1 hρ).1).trans (hB 0)
  set I : ℂ → Set ℝ := fun ρ => Icc (ρ.im - L) (ρ.im + L) with hI
  set U := ⋃ ρ ∈ F, I ρ with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion F fun _ _ => measurableSet_Icc
  have hIU : ∀ ρ ∈ F, I ρ ⊆ U := fun ρ hρ => subset_biUnion_of_mem (u := I) hρ
  have hUab : U ⊆ Icc a b :=
    iUnion₂_subset fun ρ hρ => Icc_subset_Icc (hsub ρ hρ).1 (hsub ρ hρ).2
  set h : ℝ → ℝ := fun t => ‖f t‖ * ‖g t‖ with hh
  have hhc : ContinuousOn h (Icc a b) := hf.norm.mul hg.norm
  have hhab : IntegrableOn h (Icc a b) := hhc.integrableOn_compact isCompact_Icc
  have hhU : IntegrableOn h U := hhab.mono_set hUab
  have step12 : ∑ ρ ∈ F, w ρ * ∫ t in (ρ.im - L)..(ρ.im + L), h t =
      ∫ t in U, ∑ ρ ∈ F, w ρ * (I ρ).indicator h t := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [integral_const_mul, setIntegral_indicator measurableSet_Icc,
        Set.inter_eq_right.2 (hIU ρ hρ), intervalIntegral.integral_of_le (by linarith),
        integral_Icc_eq_integral_Ioc]
    · intro ρ _; exact (hhU.indicator measurableSet_Icc).const_mul _
  have hpt : ∀ t, ∑ ρ ∈ F, w ρ * (I ρ).indicator h t ≤ B * h t := by
    intro t
    have e : ∑ ρ ∈ F, w ρ * (I ρ).indicator h t =
        (∑ ρ ∈ F.filter (fun ρ => |ρ.im - t| ≤ L), w ρ) * h t := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      by_cases ht : t ∈ I ρ
      · have : |ρ.im - t| ≤ L := by
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        rw [Set.indicator_of_mem ht, if_pos this]
      · have : ¬ |ρ.im - t| ≤ L := fun h' =>
          ht ⟨by linarith [(abs_le.1 h').2], by linarith [(abs_le.1 h').1]⟩
        rw [Set.indicator_of_notMem ht, if_neg this, mul_zero]
    rw [e]; exact mul_le_mul_of_nonneg_right (hB t) (by positivity)
  have step3 : ∫ t in U, ∑ ρ ∈ F, w ρ * (I ρ).indicator h t ≤ B * ∫ t in U, h t := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun ρ _ =>
      (hhU.indicator measurableSet_Icc).const_mul _) (hhU.const_mul _) hpt
  -- Cauchy–Schwarz twice on `U`
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hUab).trans_lt measure_Icc_lt_top⟩
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have mf : MemLp (fun t => ‖f t‖) 2 (volume.restrict U) :=
    MemLp.of_bound ((hf.norm.mono hUab).aestronglyMeasurable hUm) Cf
      (ae_restrict_of_forall_mem hUm fun t ht => by simpa using hCf t (hUab ht))
  have mg : MemLp (fun t => ‖g t‖) 2 (volume.restrict U) :=
    MemLp.of_bound ((hg.norm.mono hUab).aestronglyMeasurable hUm) Cg
      (ae_restrict_of_forall_mem hUm fun t ht => by simpa using hCg t (hUab ht))
  have mf2 : MemLp (fun t => ‖f t‖ ^ 2) 2 (volume.restrict U) :=
    MemLp.of_bound (((hf.norm.pow 2).mono hUab).aestronglyMeasurable hUm) (Cf ^ 2)
      (ae_restrict_of_forall_mem hUm fun t ht => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCf t (hUab ht)) 2)
  have m1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict U) := memLp_const 1
  have cs1 := pc_cs (volume.restrict U) (fun t => ‖f t‖) (fun t => ‖g t‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) mf mg
  have cs2 := pc_cs (volume.restrict U) (fun t => ‖f t‖ ^ 2) (fun _ => (1 : ℝ))
    (fun _ => by positivity) (fun _ => zero_le_one) mf2 m1
  simp only [mul_one, one_pow] at cs2
  simp_rw [← pow_mul] at cs2
  simp only [show (2 * 2 : ℕ) = 4 from rfl] at cs2
  set A4 := ∫ t in a..b, ‖f t‖ ^ 4 with hA4
  set A2 := ∫ t in a..b, ‖g t‖ ^ 2 with hA2
  set V := 2 * L * (F.card : ℝ) with hV
  have hf4 : ∫ t in U, ‖f t‖ ^ 4 ≤ A4 := by
    rw [hA4, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set (((hf.norm.pow 4)).integrableOn_compact isCompact_Icc)
      (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall hUab)
  have hg2 : ∫ t in U, ‖g t‖ ^ 2 ≤ A2 := by
    rw [hA2, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set (((hg.norm.pow 2)).integrableOn_compact isCompact_Icc)
      (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall hUab)
  have hvol : ∫ _ in U, (1 : ℝ) ≤ V := by
    rw [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
    have := measureReal_biUnion_finset_le (μ := volume) F I
    refine this.trans ?_
    rw [hV]
    have : ∀ ρ ∈ F, volume.real (I ρ) = 2 * L := fun ρ _ => by
      rw [hI, Real.volume_real_Icc_of_le (by linarith)]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring_nf; rfl
  have hX0 : 0 ≤ ∫ t in U, h t := integral_nonneg fun t => by positivity
  have hF20 : 0 ≤ ∫ t in U, ‖f t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hG20 : 0 ≤ ∫ t in U, ‖g t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hF40 : 0 ≤ ∫ t in U, ‖f t‖ ^ 4 := integral_nonneg fun t => by positivity
  have hV0 : 0 ≤ V := by positivity
  have hA40 : 0 ≤ A4 := hF40.trans hf4
  have hA20 : 0 ≤ A2 := hG20.trans hg2
  have hfour : (∫ t in U, h t) ^ 4 ≤ A4 * V * A2 ^ 2 := by
    have e1 : (∫ t in U, h t) ^ 4 = ((∫ t in U, h t) ^ 2) ^ 2 := by ring
    have c1 : ((∫ t in U, h t) ^ 2) ^ 2 ≤
        ((∫ t in U, ‖f t‖ ^ 2) * (∫ t in U, ‖g t‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) cs1 2
    have c2 : ((∫ t in U, ‖f t‖ ^ 2) * (∫ t in U, ‖g t‖ ^ 2)) ^ 2 =
        (∫ t in U, ‖f t‖ ^ 2) ^ 2 * (∫ t in U, ‖g t‖ ^ 2) ^ 2 := by ring
    have c3 : (∫ t in U, ‖f t‖ ^ 2) ^ 2 ≤ A4 * V :=
      cs2.trans (mul_le_mul hf4 hvol (integral_nonneg fun _ => zero_le_one) hA40)
    have c4 : (∫ t in U, ‖g t‖ ^ 2) ^ 2 ≤ A2 ^ 2 := pow_le_pow_left₀ hG20 hg2 2
    rw [e1]
    refine c1.trans (c2 ▸ ?_)
    exact mul_le_mul c3 c4 (by positivity) (by positivity)
  have hroot : ∫ t in U, h t ≤ A4 ^ (1 / 4 : ℝ) * A2 ^ (1 / 2 : ℝ) * V ^ (1 / 4 : ℝ) := by
    have e : (∫ t in U, h t) = ((∫ t in U, h t) ^ 4) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
    rw [e]
    refine (Real.rpow_le_rpow (by positivity) hfour (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (mul_nonneg hA40 hV0) (sq_nonneg A2), Real.mul_rpow hA40 hV0]
    have : (A2 ^ 2) ^ (1 / 4 : ℝ) = A2 ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA20]; norm_num
    rw [this]; ring
  calc ∑ ρ ∈ F, w ρ * ∫ t in (ρ.im - L)..(ρ.im + L), ‖f t‖ * ‖g t‖
      = ∫ t in U, ∑ ρ ∈ F, w ρ * (I ρ).indicator h t := step12
    _ ≤ B * ∫ t in U, h t := step3
    _ ≤ B * (A4 ^ (1 / 4 : ℝ) * A2 ^ (1 / 2 : ℝ) * V ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hroot hB0
    _ = _ := by ring

/-! ## Type I -/
lemma pc_dyadic_sum (f : ℕ → ℂ) (M₀ J : ℕ) :
    ∑ n ∈ Finset.Ioc M₀ (M₀ * 2 ^ J), f n =
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (M₀ * 2 ^ j) (2 * (M₀ * 2 ^ j)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * (M₀ * 2 ^ J) = M₀ * 2 ^ (J + 1) by ring]
    exact (Finset.sum_Ioc_consecutive f (Nat.le_mul_of_pos_right _ (by positivity))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

lemma pc_pigeon (P : Finset ℂ) (J : ℕ) (hJ : 1 ≤ J) (D : ℕ → ℂ → ℝ)
    (hP : ∀ s ∈ P, 1 / 2 ≤ ∑ j ∈ Finset.range J, D j s) (V : ℕ → ℝ)
    (hV : ∀ j ∈ Finset.range J, ∑ s ∈ P, D j s ^ 2 ≤ V j) :
    (P.card : ℝ) ≤ ∑ j ∈ Finset.range J, 4 * (J : ℝ) ^ 2 * V j := by
  classical
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  set c : ℝ := 1 / (2 * J) with hc
  have hc0 : 0 < c := by positivity
  set Pj : ℕ → Finset ℂ := fun j => P.filter (fun s => c ≤ D j s) with hPj
  have hcov : P ⊆ (Finset.range J).biUnion Pj := by
    intro s hs
    rw [Finset.mem_biUnion]
    by_contra hno
    push Not at hno
    have hlt : ∀ j ∈ Finset.range J, D j s < c := fun j hj => by
      have := hno j hj
      rw [hPj, Finset.mem_filter] at this
      push Not at this
      exact this hs
    have h1 := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega)) hlt
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc] at h1
    have : (J : ℝ) * (1 / (2 * J)) = 1 / 2 := by field_simp
    linarith [hP s hs]
  have hcard : (P.card : ℝ) ≤ ∑ j ∈ Finset.range J, ((Pj j).card : ℝ) := by
    have := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast this
  refine hcard.trans (Finset.sum_le_sum fun j hj => ?_)
  have h1 : ((Pj j).card : ℝ) * c ^ 2 ≤ V j := by
    calc ((Pj j).card : ℝ) * c ^ 2 = ∑ s ∈ Pj j, c ^ 2 := by simp
      _ ≤ ∑ s ∈ Pj j, D j s ^ 2 := Finset.sum_le_sum fun s hs => by
          rw [hPj, Finset.mem_filter] at hs
          exact pow_le_pow_left₀ hc0.le hs.2 2
      _ ≤ ∑ s ∈ P, D j s ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ V j := hV j hj
  have hc2 : c ^ 2 * (4 * (J : ℝ) ^ 2) = 1 := by rw [hc]; field_simp; ring
  calc ((Pj j).card : ℝ) = ((Pj j).card : ℝ) * c ^ 2 * (4 * (J : ℝ) ^ 2) := by
        rw [mul_assoc, hc2, mul_one]
    _ ≤ V j * (4 * (J : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 4 * (J : ℝ) ^ 2 * V j := by ring

/-- The per-block size bound (pure real inequality). -/
lemma pc_block_bound (σ η ε' T N : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hη : 0 < η)
    (hη1 : η ≤ 1) (hε' : 0 < ε') (hT1 : 1 ≤ T) (hN1 : T / 2 ≤ N)
    (hN2 : N ≤ T ^ (3 / (2 * (2 - σ))) * T ^ η) :
    Real.log (N + 2) ^ 2 * (T + N * Real.log (N + 2)) * N ^ (1 - 2 * σ + ε') ≤
      ((3 : ℝ) ^ (ε' / 3) * (3 / ε')) ^ 2 * (2 + (3 : ℝ) ^ (ε' / 3) * (3 / ε')) *
        T ^ (6 * ε' + (3 / (2 - σ) * (1 - σ) + η)) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  set a := 3 / (2 - σ) * (1 - σ) with ha
  set cL := (3 : ℝ) ^ (ε' / 3) * (3 / ε') with hcL
  have h2σ : 0 < 2 - σ := by linarith
  have hYT : T ^ (3 / (2 * (2 - σ))) * T ^ η ≤ T ^ (3 : ℝ) := by
    rw [← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT1
    have : 3 / (2 * (2 - σ)) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hN3 : N ≤ T ^ (3 : ℝ) := hN2.trans hYT
  have hT3 : 1 ≤ T ^ (3 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  -- logarithm
  have hlog : Real.log (N + 2) ≤ cL * T ^ ε' := by
    have e1 : Real.log (N + 2) ≤ Real.log (3 * T ^ (3 : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have e2 := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 3 * T ^ (3 : ℝ))
      (by linarith : 0 < ε' / 3)
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hT0.le] at e2
    have e3 : (3 : ℝ) * (ε' / 3) = ε' := by ring
    rw [e3] at e2
    calc Real.log (N + 2) ≤ _ := e1.trans e2
      _ = cL * T ^ ε' := by rw [hcL]; field_simp
  have hlog0 : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hcL0 : 0 ≤ cL := by positivity
  -- powers of N
  have hNe : N ^ ε' ≤ T ^ (3 * ε') := by
    calc N ^ ε' ≤ (T ^ (3 : ℝ)) ^ ε' := Real.rpow_le_rpow hN0.le hN3 hε'.le
      _ = T ^ (3 * ε') := by rw [← Real.rpow_mul hT0.le]
  have hNs : N ^ (1 - 2 * σ) ≤ (T / 2) ^ (1 - 2 * σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hN1 (by linarith)
  have hTa : T * (T / 2) ^ (1 - 2 * σ) ≤ 2 * T ^ (a + η) := by
    rw [Real.div_rpow hT0.le (by norm_num), mul_div_assoc', ← Real.rpow_one_add' hT0.le
      (by linarith)]
    have h2 : (1 : ℝ) ≤ 2 ^ (1 - 2 * σ) * 2 := by
      rw [← Real.rpow_add_one (by norm_num)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    have h3 : T ^ (1 + (1 - 2 * σ)) ≤ T ^ (a + η) := by
      apply Real.rpow_le_rpow_of_exponent_le hT1
      have : 2 * (1 - σ) ≤ a := by
        rw [ha, div_mul_eq_mul_div, le_div_iff₀ h2σ]; nlinarith
      linarith
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ T ^ (a + η) := by positivity
    nlinarith
  have hN22 : N * N ^ (1 - 2 * σ) ≤ T ^ (a + η) := by
    rw [← Real.rpow_one_add' hN0.le (by linarith)]
    calc N ^ (1 + (1 - 2 * σ)) ≤ (T ^ (3 / (2 * (2 - σ))) * T ^ η) ^ (1 + (1 - 2 * σ)) :=
          Real.rpow_le_rpow hN0.le hN2 (by linarith)
      _ = T ^ ((3 / (2 * (2 - σ)) + η) * (2 - 2 * σ)) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_mul hT0.le]; ring_nf
      _ ≤ T ^ (a + η) := by
          apply Real.rpow_le_rpow_of_exponent_le hT1
          have e : 3 / (2 * (2 - σ)) * (2 - 2 * σ) = a := by
            rw [ha]; field_simp
          nlinarith
  have hTe : 1 ≤ T ^ ε' := Real.one_le_rpow hT1 hε'.le
  have hsum : (T + N * Real.log (N + 2)) * N ^ (1 - 2 * σ) ≤ (2 + cL) * T ^ ε' * T ^ (a + η) := by
    have hp : 0 ≤ N ^ (1 - 2 * σ) := by positivity
    have e1 : T * N ^ (1 - 2 * σ) ≤ 2 * T ^ (a + η) :=
      (mul_le_mul_of_nonneg_left hNs hT0.le).trans hTa
    have e2 : N * Real.log (N + 2) * N ^ (1 - 2 * σ) ≤ cL * T ^ ε' * T ^ (a + η) := by
      calc N * Real.log (N + 2) * N ^ (1 - 2 * σ) = (N * N ^ (1 - 2 * σ)) * Real.log (N + 2) := by
            ring
        _ ≤ T ^ (a + η) * (cL * T ^ ε') :=
            mul_le_mul hN22 hlog hlog0 (by positivity)
        _ = _ := by ring
    have hTa0 : 0 ≤ T ^ (a + η) := by positivity
    nlinarith
  have hsplit : N ^ (1 - 2 * σ + ε') = N ^ (1 - 2 * σ) * N ^ ε' := Real.rpow_add hN0 _ _
  have hfin : T ^ (6 * ε' + (a + η)) = (T ^ ε') ^ 2 * T ^ ε' * T ^ (3 * ε') * T ^ (a + η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0, ← Real.rpow_add hT0,
      ← Real.rpow_add hT0]; ring_nf
  rw [hsplit, hfin]
  have hl2 : Real.log (N + 2) ^ 2 ≤ (cL * T ^ ε') ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hA : 0 ≤ (T + N * Real.log (N + 2)) * N ^ (1 - 2 * σ) := by positivity
  calc Real.log (N + 2) ^ 2 * (T + N * Real.log (N + 2)) * (N ^ (1 - 2 * σ) * N ^ ε')
      = Real.log (N + 2) ^ 2 * ((T + N * Real.log (N + 2)) * N ^ (1 - 2 * σ)) * N ^ ε' := by ring
    _ ≤ (cL * T ^ ε') ^ 2 * ((2 + cL) * T ^ ε' * T ^ (a + η)) * T ^ (3 * ε') := by
        apply mul_le_mul (mul_le_mul hl2 hsum hA (by positivity)) hNe (by positivity)
          (by positivity)
    _ = cL ^ 2 * (2 + cL) * ((T ^ ε') ^ 2 * T ^ ε' * T ^ (3 * ε') * T ^ (a + η)) := by ring

theorem typeI_points (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ P : Finset ℂ,
      (∀ s ∈ P, σ ≤ s.re ∧ s.re ≤ 1 ∧ T ≤ s.im ∧ s.im ≤ 2 * T ∧ IsTypeI T (Ys σ T) η s) →
      (∀ s ∈ P, ∀ s' ∈ P, s ≠ s' → 1 ≤ |s.im - s'.im|) →
      (P.card : ℝ) ≤ C * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε) := by
  classical
  set ε' := ε / 9 with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨CLV, hCLV0, hLV⟩ := large_values_points
  obtain ⟨Ca, hCa0, haX⟩ := aX_sq_sum ε' hε'
  set cL := (3 : ℝ) ^ (ε' / 3) * (3 / ε') with hcL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set cJ := 1 + 3 / (ε' * Real.log 2) with hcJ
  set K1 := CLV * (Ca * (cL ^ 2 * (2 + cL))) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine ⟨4 * cJ ^ 3 * K1, 1, by positivity, fun T hT P hP hsep => ?_⟩
  have hT0 : 0 < T := by linarith
  obtain ⟨hTY, hYT2⟩ := Ys_bounds σ T hσ.le hσ1.le hT
  have hL1 : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hLT : T ^ η ≤ T := (Real.rpow_le_rpow_of_exponent_le hT hη1).trans_eq (Real.rpow_one T)
  have hY0 : 0 < Ys σ T := by linarith
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℕ, M = ⌊T⌋₊ := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M : ℕ, M = ⌊Ys σ T * T ^ η⌋₊ := ⟨_, rfl⟩
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀]; exact Nat.le_floor (by exact_mod_cast hT)
  have hM₀T : T / 2 ≤ (M₀ : ℝ) := by
    have h1 := Nat.lt_floor_add_one T
    rw [← hM₀] at h1
    have h2 : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀1
    linarith
  have hYL : T ≤ Ys σ T * T ^ η := by nlinarith
  have hM₀M₁ : M₀ ≤ M₁ := by rw [hM₀, hM₁]; exact Nat.floor_le_floor hYL
  have hM₁le : (M₁ : ℝ) ≤ Ys σ T * T ^ η := by rw [hM₁]; exact Nat.floor_le (by positivity)
  have hM₀pos : (0 : ℝ) < M₀ := by exact_mod_cast hM₀1
  set x : ℝ := (M₁ : ℝ) / M₀ with hx
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hM₀pos, one_mul]; exact_mod_cast hM₀M₁
  obtain ⟨hk1, hk2⟩ := pc_floor_logb hx1
  set k := ⌊Real.logb 2 x⌋₊ with hk
  set J := k + 1 with hJ
  have hNk : M₀ * 2 ^ k ≤ M₁ := by
    have : (M₀ : ℝ) * 2 ^ k ≤ M₁ := by
      rw [hx, le_div_iff₀ hM₀pos] at hk1; linarith
    exact_mod_cast this
  have hNJ : M₁ ≤ M₀ * 2 ^ J := by
    have : (M₁ : ℝ) < M₀ * 2 ^ (k + 1) := by
      rw [hx, div_lt_iff₀ hM₀pos] at hk2; linarith
    exact_mod_cast this.le
  set b : ℕ → ℂ := fun n => if n ≤ M₁ then aX T n * (Real.exp (-(n : ℝ) / Ys σ T) : ℂ) else 0
    with hb
  set D : ℕ → ℂ → ℂ := fun j s =>
    ∑ n ∈ Finset.Ioc (M₀ * 2 ^ j) (2 * (M₀ * 2 ^ j)), b n * (n : ℂ) ^ (-s) with hD
  have hSI : ∀ s, SI T (Ys σ T) η s = ∑ j ∈ Finset.range J, D j s := by
    intro s
    simp only [hD]
    rw [← pc_dyadic_sum (fun n => b n * (n : ℂ) ^ (-s)) M₀ J]
    unfold SI
    rw [← hM₀, ← hM₁]
    simp only [hb, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    omega
  have hP' : ∀ s ∈ P, 1 / 2 ≤ ∑ j ∈ Finset.range J, ‖D j s‖ := by
    intro s hs
    obtain ⟨_, _, _, _, h5⟩ := hP s hs
    unfold IsTypeI at h5
    rw [hSI] at h5
    exact h5.trans (norm_sum_le _ _)
  have hPs : ∀ s ∈ P, σ ≤ s.re ∧ s.re ≤ 1 ∧ T ≤ s.im ∧ s.im ≤ 2 * T := fun s hs => by
    obtain ⟨h1, h2, h3, h4, _⟩ := hP s hs
    exact ⟨h1, h2, h3, h4⟩
  have hbn : ∀ n : ℕ, ‖b n‖ ≤ ‖aX T n‖ := by
    intro n
    simp only [hb]
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      have : Real.exp (-(n : ℝ) / Ys σ T) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by simp) hY0.le
      nlinarith [norm_nonneg (aX T n), Real.exp_nonneg (-(n : ℝ) / Ys σ T)]
    · simp
  set V : ℕ → ℝ := fun j => CLV * Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2) ^ 2 *
      (T + ((M₀ * 2 ^ j : ℕ) : ℝ) * Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2)) *
        (Ca * (((M₀ * 2 ^ j : ℕ) : ℝ)) ^ (1 - 2 * σ + ε')) with hV
  have hVj : ∀ j ∈ Finset.range J, ∑ s ∈ P, ‖D j s‖ ^ 2 ≤ V j := by
    intro j _
    have h1 := hLV σ T (by linarith) hT (M₀ * 2 ^ j) b P hPs hsep
    have hN1 : 1 ≤ M₀ * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 := haX T σ (by linarith) (M₀ * 2 ^ j) hN1
    have h3 : ∑ n ∈ Finset.Ioc (M₀ * 2 ^ j) (2 * (M₀ * 2 ^ j)), ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) ≤
        ∑ n ∈ Finset.Ioc (M₀ * 2 ^ j) (2 * (M₀ * 2 ^ j)), ‖aX T n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hbn n) 2) (by positivity)
    have hlog0 : 0 ≤ Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ ((M₀ * 2 ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
    have hpre : 0 ≤ CLV * Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2) ^ 2 *
        (T + ((M₀ * 2 ^ j : ℕ) : ℝ) * Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2)) := by
      have : (0 : ℝ) ≤ ((M₀ * 2 ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 0 ≤ T + ((M₀ * 2 ^ j : ℕ) : ℝ) * Real.log (((M₀ * 2 ^ j : ℕ) : ℝ) + 2) := by
        positivity
      positivity
    exact h1.trans (mul_le_mul_of_nonneg_left (h3.trans h2) hpre)
  have hJ1 : 1 ≤ J := by omega
  have hcount := pc_pigeon P J hJ1 (fun j s => ‖D j s‖) hP' V hVj
  -- each `V j` is at most `K1 * T ^ (6 ε' + (a + η))`
  have hVb : ∀ j ∈ Finset.range J, V j ≤ K1 * T ^ (6 * ε' + (3 / (2 - σ) * (1 - σ) + η)) := by
    intro j hj
    have hjk : j ≤ k := by have := Finset.mem_range.1 hj; omega
    set N : ℝ := ((M₀ * 2 ^ j : ℕ) : ℝ) with hN
    have hN1 : T / 2 ≤ N := by
      have : M₀ ≤ M₀ * 2 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
      have : (M₀ : ℝ) ≤ N := by rw [hN]; exact_mod_cast this
      linarith
    have hN2 : N ≤ T ^ (3 / (2 * (2 - σ))) * T ^ η := by
      have : M₀ * 2 ^ j ≤ M₁ :=
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjk)).trans hNk
      have : N ≤ (M₁ : ℝ) := by rw [hN]; exact_mod_cast this
      exact this.trans hM₁le
    have hbb := pc_block_bound σ η ε' T N hσ hσ1 hη hη1 hε' hT hN1 hN2
    calc V j = CLV * Ca * (Real.log (N + 2) ^ 2 * (T + N * Real.log (N + 2)) *
          N ^ (1 - 2 * σ + ε')) := by simp only [hV, hN]; ring
      _ ≤ CLV * Ca * (cL ^ 2 * (2 + cL) * T ^ (6 * ε' + (3 / (2 - σ) * (1 - σ) + η))) :=
          mul_le_mul_of_nonneg_left hbb (by positivity)
      _ = _ := by rw [hK1]; ring
  -- `J ≤ cJ T^ε'`
  have hJb : (J : ℝ) ≤ cJ * T ^ ε' := by
    have hTe : 1 ≤ T ^ ε' := Real.one_le_rpow hT hε'.le
    have hxT : x ≤ T ^ 3 := by
      have : x ≤ M₁ := by
        rw [hx, div_le_iff₀ hM₀pos]
        have : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀1
        nlinarith [Nat.cast_nonneg (α := ℝ) M₁]
      refine this.trans (hM₁le.trans ?_)
      calc Ys σ T * T ^ η ≤ T ^ 2 * T := mul_le_mul hYT2 hLT (by positivity) (by positivity)
        _ = T ^ 3 := by ring
    have hk' : (k : ℝ) ≤ Real.logb 2 x := Nat.floor_le (Real.logb_nonneg (by norm_num) hx1)
    have hlx : Real.logb 2 x ≤ 3 * (T ^ ε' / ε') / Real.log 2 := by
      rw [Real.logb]
      apply div_le_div_of_nonneg_right _ hl2.le
      calc Real.log x ≤ Real.log (T ^ 3) := Real.log_le_log (by linarith) hxT
        _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
        _ ≤ 3 * (T ^ ε' / ε') := by
            have := Real.log_le_rpow_div hT0.le hε'; linarith
    have hJk : (J : ℝ) = k + 1 := by rw [hJ]; push_cast; ring
    rw [hJk, hcJ]
    have : 3 * (T ^ ε' / ε') / Real.log 2 = 3 / (ε' * Real.log 2) * T ^ ε' := by
      field_simp
    nlinarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  set E := 6 * ε' + (3 / (2 - σ) * (1 - σ) + η) with hE
  have hTE : 0 ≤ T ^ E := by positivity
  calc (P.card : ℝ) ≤ ∑ j ∈ Finset.range J, 4 * (J : ℝ) ^ 2 * V j := hcount
    _ ≤ ∑ j ∈ Finset.range J, 4 * (J : ℝ) ^ 2 * (K1 * T ^ E) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hVb j hj) (by positivity)
    _ = 4 * (J : ℝ) ^ 3 * K1 * T ^ E := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 4 * (cJ * T ^ ε') ^ 3 * K1 * T ^ E := by
        gcongr
    _ = 4 * cJ ^ 3 * K1 * ((T ^ ε') ^ 3 * T ^ E) := by ring
    _ ≤ 4 * cJ ^ 3 * K1 * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
        apply Real.rpow_le_rpow_of_exponent_le hT
        rw [hE, hε'def]; push_cast; linarith

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
theorem typeI_finset (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ F : Finset ℂ,
      (↑F : Set ℂ) ⊆ {ρ | ρ ∈ win σ T ∧ IsTypeI T (Ys σ T) η ρ} →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
        C * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε) := by
  classical
  obtain ⟨C, T₀, hC, hPb⟩ := typeI_points σ hσ hσ1 η hη hη1 (ε / 2) (by linarith)
  obtain ⟨A, hA, hloc⟩ := local_count_finset
  refine ⟨C * (2 * A) * (6 ^ (ε / 2) / (ε / 2)), max T₀ 1, by positivity, fun T hT F hF => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hFz : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => by
    obtain ⟨⟨h1, h2, _, _⟩, _⟩ := hF hρ
    exact ⟨h1, by linarith⟩
  obtain ⟨P, hPF, hsep, hcov⟩ := exists_separated_cover F
  choose! g hgP hg using hcov
  rw [← Finset.sum_fiberwise_of_maps_to hgP]
  set e := 3 / (2 - σ) * (1 - σ) + 2 * η with he
  have hlogb : Real.log (2 * T + 4) ≤ 6 ^ (ε / 2) * T ^ (ε / 2) / (ε / 2) := by
    refine (Real.log_le_log (by linarith) (by linarith : 2 * T + 4 ≤ 6 * T)).trans ?_
    rw [← Real.mul_rpow (by norm_num) hT0.le]
    exact Real.log_le_rpow_div (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  have hfib : ∀ p ∈ P, ∑ ρ ∈ F.filter (fun ρ => g ρ = p),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ 2 * A * Real.log (2 * T + 4) := by
    intro p hp
    have hsub : F.filter (fun ρ => g ρ = p) ⊆ F.filter (fun ρ => |ρ.im - p.im| ≤ 1) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, hρ.2 ▸ hg ρ hρ.1⟩
    obtain ⟨⟨_, _, hp3, hp4⟩, _⟩ := hF (hPF hp)
    have := hloc F hFz p.im 1 zero_le_one
    rw [abs_of_nonneg (by linarith)] at this
    calc ∑ ρ ∈ F.filter (fun ρ => g ρ = p), ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
        ≤ ∑ ρ ∈ F.filter (fun ρ => |ρ.im - p.im| ≤ 1),
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ A * (1 + 1) * Real.log (p.im + 1 + 3) := this
      _ ≤ 2 * A * Real.log (2 * T + 4) := by
          rw [show A * (1 + 1) = 2 * A by ring]
          exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith))
            (by linarith)
  have hcard : (P.card : ℝ) ≤ C * T ^ (e + ε / 2) := by
    refine hPb T ((le_max_left _ _).trans hT) P (fun s hs => ?_) hsep
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hF (hPF hs)
    have : s.re ≤ 1 := by
      by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_le.1 hc).le h1
    exact ⟨h2, this, h3, h4, h5⟩
  have hpow : T ^ (e + ε / 2) * T ^ (ε / 2) = T ^ (e + ε) := by
    rw [← Real.rpow_add hT0]; ring_nf
  calc ∑ p ∈ P, ∑ ρ ∈ F.filter (fun ρ => g ρ = p), ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
      ≤ ∑ p ∈ P, 2 * A * Real.log (2 * T + 4) := Finset.sum_le_sum hfib
    _ = P.card * (2 * A * Real.log (2 * T + 4)) := by simp
    _ ≤ (C * T ^ (e + ε / 2)) * (2 * A * (6 ^ (ε / 2) * T ^ (ε / 2) / (ε / 2))) := by
        apply mul_le_mul hcard _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlogb (by positivity)
    _ = C * (2 * A) * (6 ^ (ε / 2) / (ε / 2)) * (T ^ (e + ε / 2) * T ^ (ε / 2)) := by ring
    _ = C * (2 * A) * (6 ^ (ε / 2) / (ε / 2)) * T ^ (e + ε) := by rw [hpow]

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
alias typeI_finset := GuthMaynard.CitedZeros.Ing.PartC.typeI_finset

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open GuthMaynard.CitedZeros.Ing
namespace GuthMaynard.CitedZeros.Ing.PartC
/-! ## Type II -/
lemma pc_zeta_line_cont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hc : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    hc.continuousAt

lemma pc_molli_line_cont (X : ℝ) : Continuous (fun t : ℝ => molli X (1 / 2 + (t : ℂ) * I)) := by
  unfold molli
  refine continuous_finsetSum _ fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hm).1; exact_mod_cast (by omega : m ≠ 0)
  exact continuous_const.mul
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).neg.const_cpow (Or.inl hm0))

lemma pc_root (R Q T s E : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hT : 0 < T)
    (h : R * T ^ s ≤ Q * T ^ E * R ^ (1 / 4 : ℝ)) :
    R ≤ Q ^ (4 / 3 : ℝ) * T ^ (4 / 3 * (E - s)) := by
  rcases hR.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have hsplit : R = R ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hpos]; norm_num
  have hq : 0 < R ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hTs : 0 < T ^ s := Real.rpow_pos_of_pos hT _
  have h1 : R ^ (3 / 4 : ℝ) ≤ Q * T ^ (E - s) := by
    have h' : R ^ (3 / 4 : ℝ) * T ^ s * R ^ (1 / 4 : ℝ) ≤ Q * T ^ E * R ^ (1 / 4 : ℝ) := by
      have e : R ^ (3 / 4 : ℝ) * T ^ s * R ^ (1 / 4 : ℝ) = R * T ^ s := by
        rw [mul_right_comm, ← hsplit]
      rw [e]; exact h
    have h2 := le_of_mul_le_mul_right h' hq
    rw [Real.rpow_sub hT, mul_div_assoc', le_div_iff₀ hTs]
    exact h2
  calc R = (R ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_mul hpos.le]; norm_num
    _ ≤ (Q * T ^ (E - s)) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = Q ^ (4 / 3 : ℝ) * T ^ (4 / 3 * (E - s)) := by
        rw [Real.mul_rpow hQ (by positivity), ← Real.rpow_mul hT.le, mul_comm (E - s)]

lemma pc_typeII_one (σ T η K : ℝ) (_hσ : 1 / 2 < σ) (hK : ∀ β : ℝ, σ ≤ β → β ≤ 1 →
    ∀ u : ℝ, ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ K)
    (hL : 0 ≤ T ^ η) (hY : 0 < Ys σ T) (ρ : ℂ)
    (hρ : ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ) :
    Ys σ T ^ (σ - 1 / 2) ≤ K * ∫ t in (ρ.im - T ^ η)..(ρ.im + T ^ η),
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ * ‖molli T (1 / 2 + (t : ℂ) * I)‖ := by
  obtain ⟨⟨h1, h2, _, _⟩, h5⟩ := hρ
  have hre1 : ρ.re ≤ 1 := by
    by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_le.1 hc).le h1
  unfold IsTypeII at h5
  have hYp : 0 < Ys σ T ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hY _
  set hfun : ℝ → ℝ := fun t =>
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ * ‖molli T (1 / 2 + (t : ℂ) * I)‖ with hhfun
  have hcont : Continuous hfun := pc_zeta_line_cont.norm.mul (pc_molli_line_cont T).norm
  have hint : IntervalIntegrable (fun u => kII T ρ.re ρ.im u) volume (-(T ^ η)) (T ^ η) := by
    by_contra hc
    rw [intervalIntegral.integral_undef hc] at h5
    linarith
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK ρ.re h2 hre1 0)
  have hpt : ∀ u, kII T ρ.re ρ.im u ≤ K * hfun (ρ.im + u) := by
    intro u
    unfold kII
    rw [norm_mul]
    simp only [hhfun]
    have := hK ρ.re h2 hre1 u
    have e : ((ρ.im + u : ℝ) : ℂ) = ((ρ.im + u : ℝ) : ℂ) := rfl
    calc ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
          (‖molli T (1 / 2 + ((ρ.im + u : ℝ) : ℂ) * I)‖ *
            ‖riemannZeta (1 / 2 + ((ρ.im + u : ℝ) : ℂ) * I)‖)
        ≤ K * (‖molli T (1 / 2 + ((ρ.im + u : ℝ) : ℂ) * I)‖ *
            ‖riemannZeta (1 / 2 + ((ρ.im + u : ℝ) : ℂ) * I)‖) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hc2 : Continuous (fun u => K * hfun (ρ.im + u)) :=
    continuous_const.mul (hcont.comp (continuous_const.add continuous_id))
  have hmono := intervalIntegral.integral_mono_on (f := fun u => kII T ρ.re ρ.im u)
    (g := fun u => K * hfun (ρ.im + u)) (by linarith) hint (hc2.intervalIntegrable _ _)
    (fun u _ => hpt u)
  refine h5.trans (hmono.trans (le_of_eq ?_))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left hfun ρ.im]
  congr 2

lemma pc_exp_arith (σ η ε : ℝ) (hσ1 : σ < 1) (hη : 0 < η) (hε : 0 < ε) :
    4 / 3 * (η + ε / 8 + (1 + ε) / 4 + (1 / 2 + ε / 8) + η / 4 - 3 / (2 * (2 - σ)) * (σ - 1 / 2)) ≤
      3 / (2 - σ) * (1 - σ) + 2 * η + ε := by
  have h2σ : 0 < 2 - σ := by linarith
  have key : 4 / 3 * (η + ε / 8 + (1 + ε) / 4 + (1 / 2 + ε / 8) + η / 4 -
      3 / (2 * (2 - σ)) * (σ - 1 / 2)) =
      3 / (2 - σ) * (1 - σ) + 5 / 3 * η + 2 / 3 * ε := by
    field_simp; ring
  rw [key]; linarith

lemma pc_fac1 (A T η δ : ℝ) (hA : 0 ≤ A) (hT1 : 1 ≤ T) (hη : 0 ≤ η) (hδ0 : 0 < δ) :
    A * (T ^ η + 1) * Real.log (7 * T) ≤ A * 2 * (7 ^ δ / δ) * T ^ (η + δ) := by
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη
  have hlog7 : Real.log (7 * T) ≤ 7 ^ δ * T ^ δ / δ := by
    rw [← Real.mul_rpow (by norm_num) hT0.le]
    exact Real.log_le_rpow_div (by linarith) hδ0
  have : 0 ≤ Real.log (7 * T) := Real.log_nonneg (by linarith)
  calc A * (T ^ η + 1) * Real.log (7 * T)
      ≤ A * (2 * T ^ η) * (7 ^ δ * T ^ δ / δ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA) hlog7 this (by positivity)
    _ = A * 2 * (7 ^ δ / δ) * (T ^ η * T ^ δ) := by ring
    _ = A * 2 * (7 ^ δ / δ) * T ^ (η + δ) := by rw [← Real.rpow_add hT0]

lemma pc_fac2 (C₄ ε T I : ℝ) (hT0 : 0 < T) (hC₄ : 0 ≤ C₄) (h0 : 0 ≤ I)
    (hb : I ≤ C₄ * (3 * T) ^ (1 + ε)) :
    I ^ (1 / 4 : ℝ) ≤ (C₄ * 3 ^ (1 + ε)) ^ (1 / 4 : ℝ) * T ^ ((1 + ε) / 4) := by
  calc I ^ (1 / 4 : ℝ) ≤ (C₄ * (3 * T) ^ (1 + ε)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow h0 hb (by norm_num)
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) hT0.le, ← mul_assoc,
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT0.le]
        congr 2; ring

lemma pc_fac3 (T δ : ℝ) (hT1 : 1 ≤ T) (hδ0 : 0 < δ) :
    (∫ t in (0 : ℝ)..(3 * T), ‖molli T (1 / 2 + (t : ℂ) * I)‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      (7 * (1 + 1 / δ) ^ 2) ^ (1 / 2 : ℝ) * T ^ (1 / 2 + δ) := by
  have hT0 : 0 < T := by linarith
  have hlog1 : 1 + Real.log T ≤ (1 + 1 / δ) * T ^ δ := by
    have e1 := Real.log_le_rpow_div hT0.le hδ0
    have e2 : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ0.le
    have : T ^ δ / δ = (1 / δ) * T ^ δ := by ring
    nlinarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hb := molli_mean_square T (3 * T) hT1 (by linarith)
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..(3 * T), ‖molli T (1 / 2 + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  have hms : (3 * T + 4 * T * (1 + Real.log T)) * (1 + Real.log T) ≤
      7 * (1 + 1 / δ) ^ 2 * T ^ (1 + 2 * δ) := by
    have e1 : (3 * T + 4 * T * (1 + Real.log T)) * (1 + Real.log T) ≤
        7 * T * (1 + Real.log T) ^ 2 := by nlinarith
    have e2 : (1 + Real.log T) ^ 2 ≤ ((1 + 1 / δ) * T ^ δ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlog1 2
    have e3 : T * ((1 + 1 / δ) * T ^ δ) ^ 2 = (1 + 1 / δ) ^ 2 * T ^ (1 + 2 * δ) := by
      rw [mul_pow, ← Real.rpow_natCast (T ^ δ) 2, ← Real.rpow_mul hT0.le,
        Real.rpow_add hT0, Real.rpow_one]; push_cast; ring_nf
    calc _ ≤ 7 * T * (1 + Real.log T) ^ 2 := e1
      _ ≤ 7 * T * ((1 + 1 / δ) * T ^ δ) ^ 2 := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = 7 * (T * ((1 + 1 / δ) * T ^ δ) ^ 2) := by ring
      _ = _ := by rw [e3]; ring
  calc (∫ t in (0 : ℝ)..(3 * T), ‖molli T (1 / 2 + (t : ℂ) * I)‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (7 * (1 + 1 / δ) ^ 2 * T ^ (1 + 2 * δ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow h0 (hb.trans hms) (by norm_num)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT0.le]
        congr 2; ring

lemma pc_fac4 (T η R c : ℝ) (hT0 : 0 < T) (hR0 : 0 ≤ R) (hc : 0 ≤ c) (hcR : c ≤ R) :
    (2 * T ^ η * c) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * T ^ (η / 4) * R ^ (1 / 4 : ℝ) := by
  have hL : 0 ≤ T ^ η := by positivity
  calc (2 * T ^ η * c) ^ (1 / 4 : ℝ) ≤ (2 * T ^ η * R) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hcR (by positivity))
          (by norm_num)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) hR0, Real.mul_rpow (by norm_num) hL,
          ← Real.rpow_mul hT0.le]; congr 3; ring

theorem typeII_finset (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ F : Finset ℂ, (↑F : Set ℂ) ⊆ {ρ | ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ} →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
        C * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε) := by
  classical
  obtain ⟨K, hK0, hK⟩ := gamma_line_bound σ hσ
  obtain ⟨A, hA, hloc⟩ := local_count_finset
  obtain ⟨C₄, T₄, hC₄, h4⟩ := fourth_moment ε hε
  set δ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  set c1 := A * 2 * (7 ^ δ / δ) with hc1
  set c2 := (C₄ * 3 ^ (1 + ε)) ^ (1 / 4 : ℝ) with hc2
  set c3 := (7 * (1 + 1 / δ) ^ 2) ^ (1 / 2 : ℝ) with hc3
  set Q := K * c1 * c2 * c3 * 2 ^ (1 / 4 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨Q ^ (4 / 3 : ℝ), max T₄ 1, by positivity, fun T hT F hF => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  set L := T ^ η with hLdef
  have hL1 : 1 ≤ L := Real.one_le_rpow hT1 hη.le
  have hLT : L ≤ T := by
    calc L = T ^ η := rfl
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hη1
      _ = T := Real.rpow_one T
  set Y := Ys σ T with hYdef
  set cY := 3 / (2 * (2 - σ)) with hcY
  have hYeq : Y = T ^ cY := rfl
  have hY0 : 0 < Y := by rw [hYeq]; exact Real.rpow_pos_of_pos hT0 _
  set R := ∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  set fz : ℝ → ℂ := fun t => riemannZeta (1 / 2 + (t : ℂ) * I) with hfz
  set gm : ℝ → ℂ := fun t => molli T (1 / 2 + (t : ℂ) * I) with hgm
  -- Step 1: detection, summed
  have hstep1 : R * Y ^ (σ - 1 / 2) ≤
      K * ∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        ∫ t in (ρ.im - L)..(ρ.im + L), ‖fz t‖ * ‖gm t‖ := by
    rw [hR, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have := pc_typeII_one σ T η K hσ hK (by positivity) hY0 ρ (hF hρ)
    calc ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * Y ^ (σ - 1 / 2)
        ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (K * ∫ t in (ρ.im - L)..(ρ.im + L),
            ‖fz t‖ * ‖gm t‖) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := by ring
  -- Step 2: overlap + Hölder
  set B := A * (L + 1) * Real.log (7 * T) with hB
  have hFz : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => by
    obtain ⟨⟨h1, h2, _, _⟩, _⟩ := hF hρ
    exact ⟨h1, by linarith⟩
  have hBt : ∀ t : ℝ, ∑ ρ ∈ F.filter (fun ρ => |ρ.im - t| ≤ L),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ B := by
    intro t
    rcases (F.filter (fun ρ => |ρ.im - t| ≤ L)).eq_empty_or_nonempty with he | ⟨ρ, hρ⟩
    · rw [he, Finset.sum_empty]
      have : 0 ≤ Real.log (7 * T) := Real.log_nonneg (by linarith)
      positivity
    rw [Finset.mem_filter] at hρ
    obtain ⟨⟨_, _, h3, h4⟩, _⟩ := hF hρ.1
    have ht : |t| ≤ 3 * T := by
      have := abs_le.1 hρ.2
      rw [abs_le]; constructor <;> linarith
    refine (hloc F hFz t L (by linarith)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)
  have hstep2 : ∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        ∫ t in (ρ.im - L)..(ρ.im + L), ‖fz t‖ * ‖gm t‖ ≤
      B * (∫ t in (0 : ℝ)..(3 * T), ‖fz t‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∫ t in (0 : ℝ)..(3 * T), ‖gm t‖ ^ 2) ^ (1 / 2 : ℝ) *
          (2 * L * F.card) ^ (1 / 4 : ℝ) := overlap_holder fz gm 0 (3 * T) L B pc_zeta_line_cont.continuousOn
    (pc_molli_line_cont T).continuousOn (by linarith) F
    (fun ρ => ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (fun ρ hρ => by
      obtain ⟨⟨_, _, h3, h4⟩, _⟩ := hF hρ
      constructor <;> linarith) hBt
  -- Step 3: the four factors
  have hcardR : (F.card : ℝ) ≤ R := by
    rw [hR, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    obtain ⟨⟨h1, h2, _, _⟩, _⟩ := hF hρ
    have hre1 : ρ.re < 1 := by
      by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h1
    have := Zeta23.zetaSeam.one_le_mult ρ ⟨h1, by linarith, hre1⟩
    exact_mod_cast this
  have fac1 : B ≤ c1 * T ^ (η + δ) := pc_fac1 A T η δ hA hT1 hη.le hδ0
  have fac2 : (∫ t in (0 : ℝ)..(3 * T), ‖fz t‖ ^ 4) ^ (1 / 4 : ℝ) ≤
      c2 * T ^ ((1 + ε) / 4) :=
    pc_fac2 C₄ ε T _ hT0 hC₄ (intervalIntegral.integral_nonneg (by linarith)
      fun _ _ => pow_nonneg (norm_nonneg _) _) (h4 (3 * T) (by linarith [le_max_left T₄ 1]))
  have fac3 : (∫ t in (0 : ℝ)..(3 * T), ‖gm t‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      c3 * T ^ (1 / 2 + δ) := pc_fac3 T δ hT1 hδ0
  have fac4 : (2 * L * F.card) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * T ^ (η / 4) * R ^ (1 / 4 : ℝ) :=
    pc_fac4 T η R (F.card : ℝ) hT0 hR0 (Nat.cast_nonneg _) hcardR
  set E := η + δ + (1 + ε) / 4 + (1 / 2 + δ) + η / 4 with hE
  have hmain : R * T ^ (cY * (σ - 1 / 2)) ≤ Q * T ^ E * R ^ (1 / 4 : ℝ) := by
    have hYp : Y ^ (σ - 1 / 2) = T ^ (cY * (σ - 1 / 2)) := by
      rw [hYeq, ← Real.rpow_mul hT0.le]
    rw [← hYp]
    have hB0 : 0 ≤ B := by
      have : 0 ≤ Real.log (7 * T) := Real.log_nonneg (by linarith)
      positivity
    have i1 : 0 ≤ (∫ t in (0 : ℝ)..(3 * T), ‖fz t‖ ^ 4) ^ (1 / 4 : ℝ) := by
      apply Real.rpow_nonneg
      exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => pow_nonneg (norm_nonneg _) _
    have i2 : 0 ≤ (∫ t in (0 : ℝ)..(3 * T), ‖gm t‖ ^ 2) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_nonneg
      exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => pow_nonneg (norm_nonneg _) _
    have i3 : 0 ≤ (2 * L * F.card) ^ (1 / 4 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg (mul_nonneg zero_le_two (by linarith)) (Nat.cast_nonneg _)) _
    calc R * Y ^ (σ - 1 / 2)
        ≤ K * ∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
            ∫ t in (ρ.im - L)..(ρ.im + L), ‖fz t‖ * ‖gm t‖ := hstep1
      _ ≤ K * (B * (∫ t in (0 : ℝ)..(3 * T), ‖fz t‖ ^ 4) ^ (1 / 4 : ℝ) *
            (∫ t in (0 : ℝ)..(3 * T), ‖gm t‖ ^ 2) ^ (1 / 2 : ℝ) *
              (2 * L * F.card) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hstep2 hK0
      _ ≤ K * (c1 * T ^ (η + δ) * (c2 * T ^ ((1 + ε) / 4)) * (c3 * T ^ (1 / 2 + δ)) *
            (2 ^ (1 / 4 : ℝ) * T ^ (η / 4) * R ^ (1 / 4 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact mul_le_mul (mul_le_mul (mul_le_mul fac1 fac2 i1 (by positivity)) fac3 i2
            (by positivity)) fac4 i3 (by positivity)
      _ = Q * (T ^ (η + δ) * T ^ ((1 + ε) / 4) * T ^ (1 / 2 + δ) * T ^ (η / 4)) *
            R ^ (1 / 4 : ℝ) := by rw [hQ]; ring
      _ = Q * T ^ E * R ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have hfin := pc_root R Q T (cY * (σ - 1 / 2)) E hR0 hQ0 hT0 hmain
  refine hfin.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT1 ?_) (by positivity))
  rw [hE, hcY, hδ]
  exact pc_exp_arith σ η ε hσ1 hη hε

end GuthMaynard.CitedZeros.Ing.PartC
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Ing
alias typeII_finset := GuthMaynard.CitedZeros.Ing.PartC.typeII_finset

/-! ## Assembly (no `sorry` below) -/
theorem typeI_count (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      (zc {ρ | ρ ∈ win σ T ∧ IsTypeI T (Ys σ T) η ρ} : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε)) := by
  obtain ⟨C, T₀, hC, h⟩ := typeI_finset σ hσ hσ1 η hη hη1 ε hε
  exact ⟨C, T₀, hC, fun T hT => count_le_of_finset_bound _ _ (h T hT)⟩

theorem typeII_count (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ε : ℝ) (hε : 0 < ε) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      (zc {ρ | ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ} : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε)) := by
  obtain ⟨C, T₀, hC, h⟩ := typeII_finset σ hσ hσ1 η hη hη1 ε hε
  exact ⟨C, T₀, hC, fun T hT => count_le_of_finset_bound _ _ (h T hT)⟩

/-- The window bound for `1/2 < σ < 1`. -/
theorem window_bound (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      (zc (win σ T) : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + ε)) := by
  set η : ℝ := min (ε / 4) 1 with hηdef
  have hη : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hη4 : η ≤ ε / 4 := min_le_left _ _
  obtain ⟨T₁, hdet⟩ := detect σ hσ hσ1 η hη
  obtain ⟨C₁, T₂, hC₁, h₁⟩ := typeI_count σ hσ hσ1 η hη hη1 (ε / 2) (by linarith)
  obtain ⟨C₂, T₃, hC₂, h₂⟩ := typeII_count σ hσ hσ1 η hη hη1 (ε / 2) (by linarith)
  refine ⟨C₁ + C₂, max (max T₁ T₂) (max T₃ 1), by linarith, fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT4 : (1 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨hY1, hY2⟩ := Ys_bounds σ T hσ.le hσ1.le hT4
  have hsplit : win σ T ⊆ {ρ | ρ ∈ win σ T ∧ IsTypeI T (Ys σ T) η ρ} ∪
      {ρ | ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ} := by
    intro ρ hρ
    rcases hdet T hT1 (Ys σ T) hY1 hY2 ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2 with h | h
    · exact Or.inl ⟨hρ, h⟩
    · exact Or.inr ⟨hρ, h⟩
  have hexp : T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε / 2) ≤
      T ^ (3 / (2 - σ) * (1 - σ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT4 (by linarith)
  have hpow : 0 ≤ T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε / 2) :=
    Real.rpow_nonneg (by linarith) _
  calc (zc (win σ T) : ℝ≥0∞)
      ≤ ((zc {ρ | ρ ∈ win σ T ∧ IsTypeI T (Ys σ T) η ρ} +
          zc {ρ | ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ} : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (count_union _ _ _ hsplit)
    _ = (zc {ρ | ρ ∈ win σ T ∧ IsTypeI T (Ys σ T) η ρ} : ℝ≥0∞) +
          (zc {ρ | ρ ∈ win σ T ∧ IsTypeII σ T (Ys σ T) η ρ} : ℝ≥0∞) := by
        push_cast; rfl
    _ ≤ ENNReal.ofReal (C₁ * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε / 2)) +
          ENNReal.ofReal (C₂ * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε / 2)) :=
        add_le_add (h₁ T hT2) (h₂ T hT3)
    _ = ENNReal.ofReal ((C₁ + C₂) * T ^ (3 / (2 - σ) * (1 - σ) + 2 * η + ε / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ ENNReal.ofReal ((C₁ + C₂) * T ^ (3 / (2 - σ) * (1 - σ) + ε)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by linarith))

/-- **Ingham's density estimate.** -/
theorem ingham_dev (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + ε)) := by
  rcases eq_or_lt_of_le hσ₁ with h1 | h1
  · refine ⟨0, Filter.Eventually.of_forall fun T => ?_⟩
    rw [count_re_ge_one σ T h1.ge]
    simp
  rcases eq_or_lt_of_le hσ₀ with h0 | h0
  · subst h0
    have ha : (3 / (2 - 1 / 2) * (1 - 1 / 2) : ℝ) = 1 := by norm_num
    rw [ha]
    exact dyadic_assembly (1 / 2) 1 le_rfl zero_le_one (fun ε hε => window_bound_half ε hε) ε hε
  · have ha : 0 ≤ 3 / (2 - σ) * (1 - σ) :=
      mul_nonneg (div_nonneg (by norm_num) (by linarith)) (by linarith)
    exact dyadic_assembly σ _ hσ₀ ha (fun ε hε => window_bound σ h0 h1 ε hε) ε hε

end GuthMaynard.CitedZeros.Ing
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros
theorem ingham_dev : type_of% @GuthMaynard.CitedZeros.Ing.ingham_dev :=
  GuthMaynard.CitedZeros.Ing.ingham_dev

end GuthMaynard.CitedZeros
end

open Complex Filter Asymptotics LindelofHypothesis in
open scoped ENNReal in
theorem solution (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + ε)) :=
  GuthMaynard.CitedZeros.ingham_dev σ hσ₀ hσ₁ ε hε
