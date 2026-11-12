-- Prove2me | solution 1 for GuthMaynard.huxley_density_estimate_of_nine_elevenths_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:48:23.137142+00:00
-- url     : https://prove2.me/submissions/6de4dfd2-18b5-4f37-9a50-0e4a10bbf465
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_half_le_thirteen_div_eightyfour
import Theorems.Thm_GuthMaynard_card_le_of_large_values_huxley
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
/-!
# Huxley (1.9) for `9/11 ≤ α ≤ 1 - 32400 log l / l`: blueprint

`N(α, T) ≤ C T^{3(1-α)/(3α-1)} (log T)^{44}` for `T ≥ T₀` and
`9/11 ≤ α ≤ 1 - 32400 log log T / log T`.

Huxley, Invent. Math. 15 (1972), §§3–6, second case (p. 169): with a subconvexity bound
`ζ(1/2+it) ≪ |t|^θ` (Huxley uses Haneke's `θ = 13/80`; here Bourgain's `μ(1/2) ≤ 13/84`,
`LindelofHypothesis.mu_half_le_thirteen_div_eightyfour`, gives `θ = 0.156`), the choice
`X^{-1/2} Y^{α-1/2} = T^{θ''}` ((6.8), `θ'' = 0.157`) makes Type II zeros impossible, and all
zeros are Type I. `Y = T^{3/(12α-4)}` ((6.6)) as in the first range, so
`X = T^{3(2α-1)/(12α-4) - 0.314} ≥ T^{1/72}`.

Zeros are counted directly in `(log T)² ≤ γ ≤ T` (Huxley counts `|γ| ≤ T` with (3.9)), with the
rest by conjugation and a trivial count below `(log T)²`; no dyadic decomposition (which would lose
`1/e(α)`, as large as `l / log l`).
-/
/-! ## Definitions -/
/-- `a_X(n) = ∑_{d ∣ n, d ≤ X} μ(d)` (Huxley's `b(m)`, (3.4)). -/
noncomputable def aX (X : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X), (ArithmeticFunction.moebius d : ℂ)

/-- The mollifier `M_X(s) = ∑_{m ≤ X} μ(m) m^{-s}` ((3.2)). -/
noncomputable def molli (X : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- The target exponent `e(α) = 3(1-α)/(3α-1)`. -/
noncomputable def ex (α : ℝ) : ℝ := 3 * (1 - α) / (3 * α - 1)

/-- `W = T^{1/(3α-1)}`. -/
noncomputable def Wp (α T : ℝ) : ℝ := T ^ (1 / (3 * α - 1))

/-- `X = Y^{2α-1} T^{-0.314}`, i.e. `X^{-1/2} Y^{α-1/2} = T^{0.157}` ((6.8)). -/
noncomputable def Xp (α T : ℝ) : ℝ := T ^ (3 * (2 * α - 1) / (12 * α - 4) - 157 / 500)

/-- `Y = T^{3/(12α-4)}` ((6.6)). -/
noncomputable def Yp (α T : ℝ) : ℝ := T ^ (3 / (12 * α - 4))

/-- Lower end of the Type I range, `⌊X⌋`. -/
noncomputable def N0 (α T : ℝ) : ℕ := ⌊Xp α T⌋₊

/-- Upper end of the Type I range, `⌊Y (log T)²⌋`. -/
noncomputable def Ztop (α T : ℝ) : ℕ := ⌊Yp α T * Real.log T ^ 2⌋₊

/-- The smoothed coefficient `a_X(n) e^{-n/Y}`. -/
noncomputable def coef (α T : ℝ) (n : ℕ) : ℂ :=
  aX (Xp α T) n * (Real.exp (-(n : ℝ) / Yp α T) : ℂ)

/-- The Type I sum `∑_{X < n ≤ Y l²} a_X(n) e^{-n/Y} n^{-s}`. -/
noncomputable def SI (α T : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N0 α T) (Ztop α T), coef α T n * (n : ℂ) ^ (-s)

/-- Number of dyadic blocks: `N0 · 2^j ≤ Ztop` exactly for `j < Jn`. -/
noncomputable def Jn (α T : ℝ) : ℕ := Nat.log 2 (Ztop α T / N0 α T) + 1

/-- The `j`-th dyadic block `(N0 2^j, min(N0 2^{j+1}, Ztop)]`. -/
noncomputable def blk (α T : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Ioc (N0 α T * 2 ^ j) (min (N0 α T * 2 ^ (j + 1)) (Ztop α T))

/-- The block sum `D_j(s)`. -/
noncomputable def Dj (α T : ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ blk α T j, coef α T n * (n : ℂ) ^ (-s)

/-- Type I zero: the Type I sum is large. -/
def IsTypeI (α T : ℝ) (s : ℂ) : Prop := 1 / 2 ≤ ‖SI α T s‖

/-- The Type II kernel `|Γ(1/2-β+iu)| · |M_X ζ(1/2+i(γ+u))|`. -/
noncomputable def kII (X β γ u : ℝ) : ℝ :=
  ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ *
    ‖molli X (1 / 2 + ((γ + u : ℝ) : ℂ) * I) * riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖

/-- Type II zero: the line integral is large (a Bochner integral; `0` if not integrable). -/
def IsTypeII (α T : ℝ) (s : ℂ) : Prop :=
  Yp α T ^ (α - 1 / 2) ≤ ∫ u : ℝ, kII (Xp α T) s.re s.im u

/-- Zeros in a set `S`, counted with multiplicity, in `ℕ∞` (as in `zeroDensityCount`). -/
noncomputable def zc (S : Set ℂ) : ℕ∞ := ∑' s : S, analyticOrderAt riemannZeta (s : ℂ)

/-- Zeros with `Re ≥ σ` and ordinate in `[(log T)², T]`. -/
def win (σ T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ Real.log T ^ 2 ≤ ρ.im ∧ ρ.im ≤ T}

/-- Huxley's range: `9/11 ≤ α ≤ 1 - 32400 log log T / log T`. -/
def InR (α T : ℝ) : Prop :=
  9 / 11 ≤ α ∧ α ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T

/-- The block bound of Huxley's (2.9) for the `a`-th power of a block starting at `U`, threshold
`V` (without the absolute constant), as in the first range. -/
noncomputable def Bfun (α T : ℝ) (a : ℕ) (U V : ℝ) : ℝ :=
  U ^ (2 * (a : ℝ) * (1 - α)) * (1 + Real.log (2 ^ a * U ^ a)) ^ (4 * a ^ 2 - 1) * V ^ (-(2 * (a : ℝ))) +
    U ^ ((a : ℝ) * (4 - 6 * α)) * T * (1 + Real.log (2 ^ a * U ^ a)) ^ (3 * (4 * a ^ 2 - 1)) *
      V ^ (-(6 * (a : ℝ))) * Real.log (2 ^ a * U ^ a * T) ^ 2

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
/-!
# Huxley (1.9), second range `9/11 ≤ α ≤ 1 - 32400 log l / l`: Parts D and L

`count_union`, `count_le_of_finset_bound`, `detect`, `zeta_half_bound`, `no_typeII`,
`SI_eq_sum_blocks`, `N0_pos`, `block_count`, `typeI_points`, `typeI_finset`, `final_assembly`.
Infrastructure copied (renamed `pdl_*`) from `HR1PartD` / `HR1PartL` / `HR1PartB`.
-/
/-- `I(ρ) = ∑ a_X(n) e^{-n/Y} n^{-ρ}`. -/
noncomputable def pdl_Iser (X Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, aX X n * (Real.exp (-(n : ℝ) / Y) : ℂ) * (n : ℂ) ^ (-ρ)

/-- `(1/2π) ∫ Y^s Γ(s) M_X(ρ+s) ζ(ρ+s) du` on `Re s = x`. -/
noncomputable def pdl_lineInt (X Y : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
    (Y : ℂ) ^ ((x : ℂ) + (u : ℂ) * I) * Complex.Gamma ((x : ℂ) + (u : ℂ) * I) *
      molli X (ρ + ((x : ℂ) + (u : ℂ) * I)) * riemannZeta (ρ + ((x : ℂ) + (u : ℂ) * I))

/-- The residue at `s = 1 - ρ`: `Y^{1-ρ} Γ(1-ρ) M_X(1)`. -/
noncomputable def pdl_Res (X Y : ℝ) (ρ : ℂ) : ℂ :=
  (Y : ℂ) ^ (1 - ρ) * Complex.Gamma (1 - ρ) * molli X 1

lemma pdl_enat_summable {β : Type*} (f : β → ℕ∞) : Summable f :=
  ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩

lemma pdl_not_analytic_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hc : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have h2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1)
      (𝓝 ((1 - 1) * riemannZeta 1)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique riemannZeta_residue_one h2
  simp at this

lemma pdl_order_ne_top (ρ : ℂ) : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  by_cases h : ρ = 1
  · subst h; rw [analyticOrderAt_of_not_analyticAt pdl_not_analytic_one]; exact ENat.zero_ne_top
  · exact Zeta23.analyticOrderAt_riemannZeta_ne_top h

lemma pdl_order_eq (ρ : ℂ) : ((analyticOrderAt riemannZeta ρ : ℕ∞) : ℝ≥0∞) =
    ENNReal.ofReal ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (pdl_order_ne_top ρ)
  rw [← hn]; simp

lemma pdl_zc_eq (S : Set ℂ) : (zc S : ℝ≥0∞) =
    ∑' s : S, ENNReal.ofReal ((analyticOrderAt riemannZeta (s : ℂ)).toNat : ℝ) := by
  unfold zc
  rw [show ((∑' s : S, analyticOrderAt riemannZeta (s : ℂ) : ℕ∞) : ℝ≥0∞) =
      ENat.toENNRealRingHom (∑' s : S, analyticOrderAt riemannZeta (s : ℂ)) from rfl,
    (pdl_enat_summable _).map_tsum ENat.toENNRealRingHom ENat.continuous_toENNReal]
  exact tsum_congr fun s => pdl_order_eq s

theorem count_union (S A B : Set ℂ) (h : S ⊆ A ∪ B) : zc S ≤ zc A + zc B := by
  rw [← ENat.toENNReal_le, ENat.toENNReal_add, pdl_zc_eq, pdl_zc_eq, pdl_zc_eq]
  exact (ENNReal.tsum_mono_subtype (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) h).trans
    (ENNReal.tsum_union_le (fun s : ℂ => ENNReal.ofReal ((analyticOrderAt riemannZeta s).toNat : ℝ)) A B)

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
/-! ## Counting primitives -/

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
theorem count_le_of_finset_bound (S : Set ℂ) (K : ℝ)
    (h : ∀ F : Finset ℂ, (↑F : Set ℂ) ⊆ S →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤ K) :
    (zc S : ℝ≥0∞) ≤ ENNReal.ofReal K := by
  rw [pdl_zc_eq, ENNReal.tsum_eq_iSup_sum]
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

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
alias count_le_of_finset_bound := GuthMaynard.CitedZeros.HR2.PartDL.count_le_of_finset_bound

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
lemma pdl_zerosIn_finite (a b : ℝ) : (Zeta23.zerosIn a b).Finite := Zeta23.zetaSeam.finite_window a b

lemma pdl_Ncount_eq (a b : ℝ) : (Zeta23.Ncount a b : ℝ) =
    ∑ ρ ∈ (pdl_zerosIn_finite a b).toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (pdl_zerosIn_finite a b)]
  push_cast; rfl

lemma pdl_window_sum_le (F : Finset ℂ) (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re) (a b : ℝ) :
    ∑ ρ ∈ F.filter (fun ρ => a < ρ.im ∧ ρ.im ≤ b), ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
      Zeta23.Ncount a b := by
  rw [pdl_Ncount_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ.1
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨h1, h2, ?_⟩, hρ.2.1, hρ.2.2⟩
    by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h1
  · intros; positivity

lemma pdl_ceil_sub_one {x : ℝ} (hx : 0 < x) :
    (((⌈x⌉₊ - 1 : ℕ) : ℝ) < x) ∧ x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  rw [Nat.cast_sub h1]
  push_cast
  constructor
  · linarith [Nat.ceil_lt_add_one hx.le]
  · linarith [Nat.le_ceil x]

lemma pdl_log_shift {x : ℝ} (hx : 3 ≤ x) : Real.log (x + 1) ≤ 2 * Real.log x := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by linarith)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith

theorem pdl_local_count_finset : ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Finset ℂ,
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
      obtain ⟨c1, c2⟩ := pdl_ceil_sub_one hx
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
      _ ≤ Zeta23.Ncount (a + j) (a + j + 1) := pdl_window_sum_le F hF _ _
      _ ≤ A₀ * Real.log (|a + j| + 3) := hA (a + j)
      _ ≤ A₀ * (2 * Real.log (|t| + H + 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          refine le_trans (Real.log_le_log (by positivity) (?_ : |a + j| + 3 ≤ (|t| + H + 3) + 1))
            (pdl_log_shift (by linarith [abs_nonneg t]))
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

lemma pdl_zeta_line_cont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hc : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    hc.continuousAt

lemma pdl_norm_Gamma_le_real (z : ℂ) (hz : 0 < z.re) :
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

lemma pdl_real_Gamma_compact_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, Real.Gamma x ≤ C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx => ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

theorem pdl_gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
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

theorem pdl_gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem pdl_gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := pdl_real_Gamma_compact_bound (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Complex.Gamma z‖ :=
      mul_le_mul_of_nonneg_right (pdl_gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Complex.Gamma (z + n)‖ := by rw [pdl_gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := pdl_norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

/-- Polynomial decay of `Γ` in vertical strips. -/
lemma pdl_gamma_decay (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → (1 + |z.im|) ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := pdl_gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := pdl_real_Gamma_compact_bound a b ha
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
      (pdl_norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza, hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

lemma pdl_one_add_sq_le (u : ℝ) : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by
  nlinarith [sq_abs u, abs_nonneg u]

/-- `|Γ(z)| ≤ C / (1 + (Im z)^2)` in the strip `a ≤ Re z ≤ b`, `a > 0`. -/
lemma pdl_gamma_sq_decay (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C, hC, h⟩ := pdl_gamma_decay a b ha 2
  refine ⟨C, hC, fun z hza hzb => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have := h z hza hzb
  have h2 := pdl_one_add_sq_le z.im
  nlinarith [norm_nonneg (Complex.Gamma z)]

/-- Uniform bound for `∫ |Γ|` on the vertical lines we need. -/
lemma pdl_gamma_int_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, (σ = -1 / 2 ∨ σ ∈ Icc (1 / 2 : ℝ) 3) →
    ‖∫ u : ℝ, Complex.Gamma ((σ : ℂ) + (u : ℂ) * I)‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := pdl_gamma_sq_decay (1 / 2) 3 (by norm_num)
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
theorem pdl_horizontal_integral_tendsto_zero
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

theorem pdl_integral_eq_of_strip_decay
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
  have htop : Tendsto H atTop (𝓝 0) := pdl_horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert pdl_horizontal_integral_tendsto_zero g a b C hab hg using 1
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
lemma pdl_strip_bound (φ : ℂ → ℂ) (a b C H : ℝ)
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

lemma pdl_line_integrable (φ : ℂ → ℂ) (x C : ℝ)
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
lemma pdl_line_integrable' (φ : ℂ → ℂ) (x C H : ℝ)
    (hc : ∀ u : ℝ, ContinuousAt φ ((x : ℂ) + (u : ℂ) * I))
    (hd : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
  have hc' : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → ContinuousAt φ z := by
    intro z h1 h2
    have hz : z = (x : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp <;> linarith
    rw [hz]; exact hc _
  obtain ⟨C', hC'⟩ := pdl_strip_bound φ x x C H hc' hd
  refine pdl_line_integrable φ x C' hc (fun u => ?_)
  have := hC' ((x : ℂ) + (u : ℂ) * I) (by simp) (by simp)
  simpa using this

/-- Contour shift across one simple pole, comparing with a reference function `g` of residue 1. -/
lemma pdl_shift_pole (f g : ℂ → ℂ) (a b : ℝ) (s₀ R : ℂ) (ha : a < s₀.re) (hb : s₀.re < b)
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
  obtain ⟨C', hC'⟩ := pdl_strip_bound h' a b _ H (fun z h1 h2 => (hh'd z h1 h2).continuousAt) hh'b
  -- integrability of `f`, `g` on the two lines
  have hne : ∀ x : ℝ, x ≠ s₀.re → ∀ u : ℝ, (x : ℂ) + (u : ℂ) * I ≠ s₀ := by
    intro x hx u he; apply hx; rw [← he]; simp
  have hint : ∀ φ : ℂ → ℂ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ φ z) →
      ∀ C H : ℝ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) →
      ∀ x : ℝ, a ≤ x → x ≤ b → x ≠ s₀.re → Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
    intro φ hφ C H hφb x hx1 hx2 hx3
    refine pdl_line_integrable' φ x C H (fun u => (hφ _ (by simpa using hx1) (by simpa using hx2)
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
  have hmain := pdl_integral_eq_of_strip_decay h' a b C' hab hh'd hh'a hh'bb
    (fun σ (hσ : σ ∈ Icc a b) t => by
      simpa using hC' ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ.1) (by simpa using hσ.2))
  rw [hline a (by linarith), hline b (by linarith), integral_sub hfa (hga.const_mul R),
    integral_sub hfb (hgb.const_mul R), integral_const_mul, integral_const_mul] at hmain
  linear_combination hmain

/-- Terms of the continuation `(w-1) ζ(w) = -1 + ∑ pdl_eT w n`. -/
noncomputable def pdl_eT (w : ℂ) (n : ℕ) : ℂ :=
  (w - 1) * ((n : ℂ) + 1) ^ (-w) - ((n : ℂ) + 1) ^ (1 - w) + ((n : ℂ) + 2) ^ (1 - w)

lemma pdl_cpow_diff_bound (w : ℂ) (hw : 0 < w.re) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : y ∈ Icc x (x + 1)) :
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

lemma pdl_eT_bound (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    ‖pdl_eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx : 0 < x := by positivity
  rcases eq_or_ne w 1 with rfl | hw1
  · simp [pdl_eT]
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
          pdl_cpow_diff_bound w hw x hx t (Ico_subset_Icc_self ht)
      _ ≤ ‖w‖ * x ^ (-w.re - 1) * 1 := by
          gcongr
          linarith [ht.2]
      _ = _ := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb (x + 1) ⟨by linarith, le_rfl⟩
  have he : φ (x + 1) - φ x = pdl_eT w n := by
    simp only [hφ, pdl_eT, hxdef]
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
  calc ‖pdl_eT w n‖ ≤ ‖w - 1‖ * (‖w‖ * x ^ (-w.re - 1)) * (x + 1 - x) := hmvt
    _ = _ := by ring

lemma pdl_summable_rpow_shift {p : ℝ} (hp : 1 < p) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
  have := (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  refine this.congr (fun n => ?_)
  have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos h0, Real.rpow_neg h0.le, one_div]

lemma pdl_eT_bound' (w : ℂ) (hw : 1 / 4 < w.re) (n : ℕ) :
    ‖pdl_eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)) := by
  refine (pdl_eT_bound w (by linarith) n).trans ?_
  gcongr
  · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact this
  · linarith

lemma pdl_eT_differentiable (n : ℕ) : Differentiable ℂ (fun w => pdl_eT w n) := by
  intro w
  have h1 : ((n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  have h2 : ((n : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  unfold pdl_eT
  have d1 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl h1)
  have d2 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h1)
  have d3 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 2) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h2)
  exact (((differentiableAt_id.sub_const 1).mul d1).sub d2).add d3

/-- The continuation sum. -/
noncomputable def pdl_Gz (w : ℂ) : ℂ := ∑' n : ℕ, pdl_eT w n

/-- The domain `1/4 < Re w`, `|w| < R`. -/
def pdl_UR (R : ℝ) : Set ℂ := {w : ℂ | 1 / 4 < w.re} ∩ Metric.ball 0 R

lemma pdl_UR_open (R : ℝ) : IsOpen (pdl_UR R) :=
  (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball

lemma pdl_Gz_diff (R : ℝ) : DifferentiableOn ℂ pdl_Gz (pdl_UR R) := by
  have hs := (pdl_summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left ((R + 1) * R)
  refine differentiableOn_tsum_of_summable_norm hs (fun n => (pdl_eT_differentiable n).differentiableOn)
    (pdl_UR_open R) (fun n w hw => ?_)
  have hwR : ‖w‖ < R := by simpa using hw.2
  refine (pdl_eT_bound' w hw.1 n).trans ?_
  have h1 : ‖w - 1‖ ≤ R + 1 := (norm_sub_le _ _).trans (by simp; linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 hwR.le (norm_nonneg _) (by linarith [norm_nonneg w]))
    (by positivity)

lemma pdl_Gz_eq (w : ℂ) (hw : 1 < w.re) : pdl_Gz w = (w - 1) * riemannZeta w - 1 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcast : ∀ n : ℕ, ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := fun n => by push_cast; ring
  -- summability of `(n+1)^{-w}`
  have hs1 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (-w)) := by
    apply Summable.of_norm
    refine (pdl_summable_rpow_shift (p := w.re) hw).congr (fun n => ?_)
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
    simp
  have hsG : Summable (fun n : ℕ => pdl_eT w n) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
    · exact (pdl_summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left _
    · intro n; exact pdl_eT_bound' w (by linarith) n
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (1 - w) with hf
  have hs2 : Summable (fun n : ℕ => f (n + 1) - f n) := by
    have := hsG.sub (hs1.mul_left (w - 1))
    refine this.congr (fun n => ?_)
    simp only [pdl_eT, hf]; push_cast; ring_nf
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
  have hsplit : (fun n : ℕ => pdl_eT w n) = fun n : ℕ => (w - 1) * ((n : ℂ) + 1) ^ (-w) + (f (n + 1) - f n) := by
    funext n; simp only [pdl_eT, hf]; push_cast; ring_nf
  unfold pdl_Gz
  rw [hsplit, (hs1.mul_left (w - 1)).tsum_add hs2, tsum_mul_left, htel, hz]
  ring

lemma pdl_zeta1_eq (R : ℝ) (hR : 2 < R) : ∀ w ∈ pdl_UR R, riemannZeta₁ w = 1 + pdl_Gz w := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ (pdl_UR R) :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (pdl_UR_open R)
  have hB : AnalyticOnNhd ℂ (fun w => 1 + pdl_Gz w) (pdl_UR R) :=
    ((differentiableOn_const _).add (pdl_Gz_diff R)).analyticOnNhd (pdl_UR_open R)
  have hconv : Convex ℝ (pdl_UR R) := (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have h2 : (2 : ℂ) ∈ pdl_UR R := ⟨by norm_num, by simp; linarith⟩
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] fun w => 1 + pdl_Gz w := by
    have hU : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with w hw
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    rw [pdl_Gz_eq w hw, riemannZeta_eq_inv_sub_mul hw1]
    field_simp
    ring
  intro w hw
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB hconv.isPreconnected h2 hev hw

/-- Polynomial growth of `ζ` for `Re w ≥ 1/2`. -/
lemma pdl_zeta_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → 2 ≤ |w.im| →
    ‖riemannZeta w‖ ≤ C * (1 + ‖w‖) := by
  have hS := pdl_summable_rpow_shift (p := 3 / 2) (by norm_num)
  set S := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨1 + S, by positivity, fun w hw him => ?_⟩
  have hw1 : w ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
  have hwm : 2 ≤ ‖w - 1‖ := by
    refine him.trans ?_
    have := Complex.abs_im_le_norm (w - 1)
    simpa using this
  have hmem : w ∈ pdl_UR (‖w‖ + 3) := ⟨show (1 / 4 : ℝ) < w.re by linarith, by simp⟩
  have heq := pdl_zeta1_eq (‖w‖ + 3) (by linarith [norm_nonneg w]) w hmem
  have hbnd : ∀ n : ℕ, ‖pdl_eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro n
    refine (pdl_eT_bound w (by linarith) n).trans ?_
    gcongr
    · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      exact this
    · linarith
  have hG : ‖pdl_Gz w‖ ≤ ‖w - 1‖ * ‖w‖ * S := by
    unfold pdl_Gz
    rw [hSdef, ← tsum_mul_left]
    exact tsum_of_norm_bounded (hS.mul_left _).hasSum hbnd
  rw [riemannZeta_eq_inv_sub_mul hw1, heq, norm_mul, norm_inv]
  have hpos : 0 < ‖w - 1‖ := by linarith
  rw [inv_mul_le_iff₀ hpos]
  calc ‖1 + pdl_Gz w‖ ≤ 1 + ‖w - 1‖ * ‖w‖ * S := (norm_add_le _ _).trans (by simp [hG])
    _ ≤ ‖w - 1‖ * ((1 + S) * (1 + ‖w‖)) := by
      nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) hS0]

lemma pdl_g_decay {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖Complex.Gamma (z - (1 - ρ))‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₂, hC₂, hΓ⟩ := pdl_gamma_decay (1 / 2) 3 (by norm_num) 2
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

lemma pdl_g_res (s₀ : ℂ) :
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

lemma pdl_g_diff {ρ : ℂ} (z : ℂ) (hz1 : 1 / 2 - ρ.re ≤ z.re) (hz : z ≠ 1 - ρ) :
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
lemma pdl_ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  rw [MeasureTheory.ae_iff]; simp

lemma pdl_g_line (s₀ : ℂ) (x : ℝ) :
    (∫ u : ℝ, Complex.Gamma ((x : ℂ) + (u : ℂ) * I - s₀)) =
      ∫ u : ℝ, Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I) := by
  have := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I)) s₀.im
  rw [← this]
  congr 1
  funext u
  congr 1
  apply Complex.ext <;> simp

lemma pdl_moeb_norm_le (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := m)
  rw [show ((ArithmeticFunction.moebius m : ℤ) : ℂ) = (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
    by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast this

/-- `mellin (e^{-x}) = Γ`. -/
lemma pdl_mellin_exp {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs]
  unfold mellin Complex.GammaIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [smul_eq_mul]
  ring

lemma pdl_gamma_line_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _, h⟩ := pdl_gamma_sq_decay c c hc
  refine pdl_line_integrable Complex.Gamma c C (fun u => ?_) (fun u => ?_)
  · apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · simpa using h ((c : ℂ) + (u : ℂ) * I) (by simp) (by simp)

/-- Cahen–Mellin: `(1/2π) ∫ Γ(c+iu) x^{-(c+iu)} du = e^{-x}`. -/
lemma pdl_cahen_mellin (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, (x : ℂ) ^ (-((c : ℂ) + (u : ℂ) * I)) *
      Complex.Gamma ((c : ℂ) + (u : ℂ) * I) = (Real.exp (-x) : ℂ) := by
  have hconv : MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (c : ℂ) := by
    unfold MellinConvergent
    have := Complex.GammaIntegral_convergent (s := (c : ℂ)) (by simpa using hc)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hvert : VerticalIntegrable (mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ))) c := by
    unfold VerticalIntegrable
    refine (pdl_gamma_line_integrable c hc).congr (ae_of_all _ (fun u => ?_))
    simp only
    rw [pdl_mellin_exp (by simpa using hc)]
  have hcont : ContinuousAt (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) x := by fun_prop
  have := mellinInv_mellin_eq c _ hx hconv hvert hcont
  unfold mellinInv at this
  rw [← this, Complex.real_smul]
  push_cast
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun u => ?_)
  have hm := pdl_mellin_exp (s := (c : ℂ) + (u : ℂ) * I) (by simp [hc])
  push_cast at hm
  simp only [smul_eq_mul]
  rw [hm]

/-- The Mellin kernel `x^{-(2+iu)} Γ(2+iu)`. -/
noncomputable def pdl_Kx (x : ℝ) (u : ℝ) : ℂ :=
  (x : ℂ) ^ (-((2 : ℝ) + (u : ℂ) * I)) * Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)

lemma pdl_Kx_norm {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖pdl_Kx x u‖ = x ^ (-(2 : ℝ)) * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  unfold pdl_Kx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma pdl_Kx_integrable {x : ℝ} (hx : 0 < x) : Integrable (pdl_Kx x) := by
  have hG := pdl_gamma_line_integrable 2 (by norm_num)
  have hc : Continuous (pdl_Kx x) := by
    unfold pdl_Kx
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
  rw [pdl_Kx_norm hx]

lemma pdl_Kx_integral {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, pdl_Kx x u = (Real.exp (-x) : ℂ) := by
  have := pdl_cahen_mellin 2 (by norm_num) hx
  rw [← this]
  rfl

/-- Geometric tail estimate. -/
lemma pdl_tail_est {Y X : ℝ} (hY : 1 ≤ Y) (hX : 0 ≤ X) (k : ℕ) (hk : X ≤ k) :
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
noncomputable def pdl_Ff (X Y : ℝ) (ρ s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma s * molli X (ρ + s) * riemannZeta (ρ + s)

/-- The integrand with the `Γ` pole at `0` cancelled against `ζ(ρ) = 0`. -/
noncomputable def pdl_Ft (X Y : ℝ) (ρ s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma (s + 1) * dslope (fun w => riemannZeta (ρ + w)) 0 s *
    molli X (ρ + s)

lemma pdl_lineInt_eq (X Y : ℝ) (ρ : ℂ) (x : ℝ) :
    pdl_lineInt X Y ρ x = (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, pdl_Ff X Y ρ ((x : ℂ) + (u : ℂ) * I) := rfl

lemma pdl_molli_bound (X : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : ‖molli X w‖ ≤ (⌊X⌋₊ : ℝ) := by
  unfold molli
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊,
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [norm_mul]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := pdl_moeb_norm_le m
    have h2 : ‖(m : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by simp; linarith)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma pdl_molli_diff (X : ℝ) (ρ s : ℂ) : DifferentiableAt ℂ (fun s : ℂ => molli X (ρ + s)) s := by
  unfold molli
  apply DifferentiableAt.fun_sum
  intro m hm
  have hm0 : (m : ℂ) ≠ 0 := by
    have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact_mod_cast (by omega : m ≠ 0)
  exact (differentiableAt_const _).mul
    ((differentiableAt_const ρ |>.add differentiableAt_id).neg.const_cpow (Or.inl hm0))

lemma pdl_Ft_eq {X Y : ℝ} {ρ s : ℂ} (h0 : riemannZeta ρ = 0) (hs : s ≠ 0) :
    pdl_Ft X Y ρ s = pdl_Ff X Y ρ s := by
  unfold pdl_Ft pdl_Ff
  rw [dslope_of_ne _ hs, slope_def_field, Complex.Gamma_add_one s hs]
  simp only [add_zero, h0, sub_zero]
  field_simp

lemma pdl_Ft_diff {X Y : ℝ} (hY : 0 < Y) {ρ s : ℂ} (hρ : ρ ≠ 1) (hs : -1 < s.re)
    (hs1 : s ≠ 1 - ρ) : DifferentiableAt ℂ (pdl_Ft X Y ρ) s := by
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
  exact ((d1.mul d2).mul d3).mul (pdl_molli_diff X ρ s)

lemma pdl_Ft_res {X Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ : ρ.re < 1) :
    Tendsto (fun z => (z - (1 - ρ)) * pdl_Ft X Y ρ z) (𝓝[≠] (1 - ρ)) (𝓝 (pdl_Res X Y ρ)) := by
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
    exact ((d1.mul d2).mul (pdl_molli_diff X ρ s₀)).continuousAt
  have hAlim : Tendsto A (𝓝[≠] s₀) (𝓝 (pdl_Res X Y ρ)) := by
    have := hAc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
    convert this using 2
    have e : ρ + s₀ = 1 := by rw [hs₀]; ring
    simp only [hA, pdl_Res, e]
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
  rw [pdl_Ft_eq h0 hz]
  simp only [hA, pdl_Ff, hs₀]
  ring

lemma pdl_Ft_decay {X Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖pdl_Ft X Y ρ z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₃, hC₃, hΓ⟩ := pdl_gamma_decay (1 / 2) 3 (by norm_num) 3
  obtain ⟨Cz, hCz, hζ⟩ := pdl_zeta_growth
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
  rw [pdl_Ft_eq h0 hz0]
  unfold pdl_Ff
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
  have f3 : ‖molli X (ρ + z)‖ ≤ Mm := pdl_molli_bound X (by simp; linarith)
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

lemma pdl_line_eq (X Y : ℝ) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (x : ℝ) :
    (∫ u : ℝ, pdl_Ff X Y ρ ((x : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, pdl_Ft X Y ρ ((x : ℂ) + (u : ℂ) * I) := by
  apply integral_congr_ae
  filter_upwards [pdl_ae_ne_zero] with u hu
  rw [pdl_Ft_eq h0]
  intro h
  apply hu
  have := congrArg Complex.im h
  simpa using this

/-- The contour shift from `Re s = 2` to `Re s = 1/2 - β`. -/
lemma pdl_contour_shift : ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y : ℝ, 1 ≤ Y → ∀ ρ : ℂ, riemannZeta ρ = 0 →
    0 < ρ.re → ρ.re < 1 →
    ‖pdl_lineInt X Y ρ (1 / 2 - ρ.re) - pdl_lineInt X Y ρ 2‖ ≤ K * ‖pdl_Res X Y ρ‖ := by
  obtain ⟨K₀, hK₀, hK⟩ := pdl_gamma_int_bound
  refine ⟨K₀ / Real.pi, by positivity, fun X Y hY ρ h0 hρ0 hρ1 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hρ1' : ρ ≠ 1 := by intro h; rw [h] at hρ1; simp at hρ1
  have hshift := pdl_shift_pole (pdl_Ft X Y ρ) (fun z => Complex.Gamma (z - (1 - ρ))) (1 / 2 - ρ.re) 2
    (1 - ρ) (pdl_Res X Y ρ) (by simp; linarith) (by simp; linarith)
    (fun z h1 _ h3 => pdl_Ft_diff hY0 hρ1' (by linarith) h3)
    (fun z h1 _ h3 => pdl_g_diff z h1 h3)
    (pdl_Ft_res hY0 h0 hρ1) (pdl_g_res (1 - ρ)) (pdl_Ft_decay hY h0 hρ0 hρ1) (pdl_g_decay hρ0 hρ1)
  rw [pdl_lineInt_eq, pdl_lineInt_eq, pdl_line_eq X Y h0, pdl_line_eq X Y h0, ← mul_sub]
  push_cast at hshift ⊢
  rw [hshift]
  have e1 := pdl_g_line (1 - ρ) (1 / 2 - ρ.re)
  have e2 := pdl_g_line (1 - ρ) 2
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
  have hRn := norm_nonneg (pdl_Res X Y ρ)
  calc 1 / (2 * Real.pi) * (‖pdl_Res X Y ρ‖ * ‖_ - _‖)
      ≤ 1 / (2 * Real.pi) * (‖pdl_Res X Y ρ‖ * (K₀ + K₀)) := by gcongr; linarith
    _ = K₀ / Real.pi * ‖pdl_Res X Y ρ‖ := by field_simp; ring

/-! ### Mellin inversion on `Re s = 2` -/
lemma pdl_aX_norm_le (X : ℝ) (n : ℕ) : ‖aX X n‖ ≤ n := by
  unfold aX
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun m _ => pdl_moeb_norm_le m)).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self n)

/-- The Dirichlet series of `a_X(n)` is `M_X(w) ζ(w)`. -/
lemma pdl_dirichlet_aX {X : ℝ} (hX : 0 ≤ X) {w : ℂ} (hw : 1 < w.re) :
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

lemma pdl_cpow_split {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : 0 < n) (ρ s : ℂ) :
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
lemma pdl_mellin_line {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y) {ρ : ℂ} (hρ : 0 < ρ.re) :
    pdl_lineInt X Y ρ 2 = pdl_Iser X Y ρ := by
  set c : ℕ → ℂ := fun n => aX X n * (n : ℂ) ^ (-ρ) with hc
  set x : ℕ → ℝ := fun n => (n : ℝ) / Y with hx
  have hc0 : c 0 = 0 := by simp [hc, aX]
  have hpt : ∀ u : ℝ, pdl_Ff X Y ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I) = ∑' n : ℕ, c n * pdl_Kx (x n) u := by
    intro u
    set s : ℂ := ((2 : ℝ) : ℂ) + (u : ℂ) * I with hs
    have hre : 1 < (ρ + s).re := by simp [hs]; linarith
    unfold pdl_Ff
    rw [mul_assoc _ (molli X (ρ + s)), ← pdl_dirichlet_aX hX hre, ← tsum_mul_left]
    congr 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, aX]
    simp only [hc, hx, pdl_Kx]
    have := pdl_cpow_split hY hn ρ s
    rw [← hs]
    calc (Y : ℂ) ^ s * Complex.Gamma s * (aX X n * (n : ℂ) ^ (-(ρ + s)))
        = aX X n * Complex.Gamma s * ((Y : ℂ) ^ s * (n : ℂ) ^ (-(ρ + s))) := by ring
      _ = _ := by rw [this]; ring
  have hint : ∀ n : ℕ, Integrable (fun u : ℝ => c n * pdl_Kx (x n) u) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]
    exact (pdl_Kx_integrable (div_pos (by exact_mod_cast hn) hY)).const_mul _
  set G : ℝ := ∫ u : ℝ, ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ with hG
  have hG0 : 0 ≤ G := integral_nonneg (fun _ => norm_nonneg _)
  have hnorm : ∀ n : ℕ, ∫ u : ℝ, ‖c n * pdl_Kx (x n) u‖ ≤ Y ^ 2 * G * (n : ℝ) ^ (-1 - ρ.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hxn : 0 < x n := div_pos hn' hY
    have e : (fun u : ℝ => ‖c n * pdl_Kx (x n) u‖) =
        fun u : ℝ => (‖c n‖ * x n ^ (-(2 : ℝ))) *
          ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
      funext u; rw [norm_mul, pdl_Kx_norm hxn]; ring
    rw [e, integral_const_mul]
    have hcn : ‖c n‖ ≤ (n : ℝ) * (n : ℝ) ^ (-ρ.re) := by
      simp only [hc]
      rw [norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hn']
      simp only [neg_re]
      gcongr
      exact pdl_aX_norm_le X n
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
  have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖c n * pdl_Kx (x n) u‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hfub := integral_tsum_of_summable_integral_norm hint hsum
  rw [pdl_lineInt_eq]
  unfold pdl_Iser
  rw [show (fun u : ℝ => pdl_Ff X Y ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I)) =
    fun u => ∑' n : ℕ, c n * pdl_Kx (x n) u from funext hpt]
  push_cast at hfub ⊢
  rw [← hfub, ← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hc0, aX]
  have hxn : 0 < x n := div_pos (by exact_mod_cast hn) hY
  rw [integral_const_mul]
  calc (1 / (2 * (Real.pi : ℂ))) * (c n * ∫ u : ℝ, pdl_Kx (x n) u)
      = c n * ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, pdl_Kx (x n) u) := by push_cast; ring
    _ = c n * (Real.exp (-x n) : ℂ) := by rw [pdl_Kx_integral hxn]
    _ = _ := by
        simp only [hc, hx, neg_div]
        push_cast
        ring

lemma pdl_aX_one {X : ℝ} (h : 1 ≤ X) : aX X 1 = 1 := by
  unfold aX
  rw [Nat.divisors_one, Finset.filter_singleton, if_pos (by simpa using h)]
  simp

lemma pdl_aX_zero_of {X : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnX : (n : ℝ) ≤ X) : aX X n = 0 := by
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

lemma pdl_gamma_left_decay (σ : ℝ) (hσ : 1 / 2 < σ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, σ ≤ β → β ≤ 1 → ∀ u : ℝ,
      (1 + |u|) ^ n * ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C₀, hC₀, hΓ⟩ := pdl_gamma_decay (1 / 2) 2 (by norm_num) n
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

lemma pdl_lineInt_upper (T Y : ℝ) (hY : 0 < Y) (ρ : ℂ) :
    ‖pdl_lineInt T Y ρ (1 / 2 - ρ.re)‖ ≤
      1 / (2 * Real.pi) * (Y ^ (1 / 2 - ρ.re) * ∫ u : ℝ, kII T ρ.re ρ.im u) := by
  rw [pdl_lineInt_eq, norm_mul]
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
  unfold pdl_Ff kII
  rw [e]
  simp only [norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  ring

lemma pdl_sum_rsqrt (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have e : ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
      exact inv_eq_one_div _
    rw [e]
    have hr := Real.sqrt_nonneg (n : ℝ)
    have hr2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    set r := Real.sqrt n
    set s := Real.sqrt ((n : ℝ) + 1)
    have key : 1 ≤ (2 * s - 2 * r) * s := by nlinarith [sq_nonneg (r - s)]
    have h1 : 1 / s ≤ 2 * s - 2 * r := (div_le_iff₀ hs).mpr key
    linarith

lemma pdl_molli_half (X : ℝ) (hX : 0 ≤ X) (t : ℝ) :
    ‖molli X (1 / 2 + (t : ℂ) * I)‖ ≤ 2 * X ^ (1 / 2 : ℝ) := by
  unfold molli
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊,
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖ ≤
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro m hm
    have hm1 : (0 : ℝ) < m := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast this
    rw [norm_mul, show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hm1]
    have hre : (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    rw [hre]
    calc _ ≤ 1 * (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (pdl_moeb_norm_le m) (by positivity)
      _ = _ := one_mul _
  refine (Finset.sum_le_sum hterm).trans ((pdl_sum_rsqrt _).trans ?_)
  rw [Real.sqrt_eq_rpow]
  gcongr
  exact Nat.floor_le hX

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex Finset
open ArithmeticFunction
open scoped ArithmeticFunction.zeta
/-- `d_k = ζ^k` (Dirichlet power), real-valued. -/
noncomputable abbrev pdl_d (k : ℕ) : ArithmeticFunction ℝ := ((ζ : ArithmeticFunction ℝ)) ^ k

lemma pdl_d_succ_apply (k n : ℕ) : pdl_d (k + 1) n = ∑ i ∈ n.divisors, pdl_d k i := by
  rw [pdl_d, pow_succ, coe_mul_zeta_apply]

lemma pdl_d_nonneg (k n : ℕ) : 0 ≤ pdl_d k n := by
  induction k generalizing n with
  | zero => simp only [pdl_d, pow_zero, one_apply]; split_ifs <;> norm_num
  | succ k ih => rw [pdl_d_succ_apply]; exact sum_nonneg fun i _ => ih i

lemma pdl_d_one (n : ℕ) (hn : n ≠ 0) : pdl_d 1 n = 1 := by
  simp [pdl_d, natCoe_apply, zeta_apply, hn]

/-- Submultiplicativity `d_k(ab) ≤ d_k(a) d_k(b)`. -/
lemma pdl_d_submul (k : ℕ) : ∀ a b : ℕ, pdl_d k (a * b) ≤ pdl_d k a * pdl_d k b := by
  induction k with
  | zero =>
    intro a b
    simp only [pdl_d, pow_zero, one_apply, mul_eq_one]
    by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> simp [ha, hb]
  | succ k ih =>
    intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    rw [pdl_d_succ_apply, pdl_d_succ_apply, pdl_d_succ_apply, sum_mul_sum, ← sum_product']
    have hex : ∀ e ∈ (a * b).divisors, ∃ q : ℕ × ℕ, q ∈ a.divisors ×ˢ b.divisors ∧
        e = q.1 * q.2 := by
      intro e he
      obtain ⟨d₁, d₂, h1, h2, rfl⟩ := dvd_mul.1 (Nat.dvd_of_mem_divisors he)
      exact ⟨(d₁, d₂), by simp [h1, h2, ha.ne', hb.ne'], rfl⟩
    choose! φ hφmem hφeq using hex
    calc ∑ e ∈ (a * b).divisors, pdl_d k e
        ≤ ∑ e ∈ (a * b).divisors, pdl_d k (φ e).1 * pdl_d k (φ e).2 := by
          refine sum_le_sum fun e he => ?_
          conv_lhs => rw [hφeq e he]
          exact ih _ _
      _ = ∑ q ∈ (a * b).divisors.image φ, pdl_d k q.1 * pdl_d k q.2 := by
          rw [sum_image]
          intro x hx y hy hxy
          rw [hφeq x hx, hφeq y hy, hxy]
      _ ≤ ∑ q ∈ a.divisors ×ˢ b.divisors, pdl_d k q.1 * pdl_d k q.2 := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ =>
            mul_nonneg (pdl_d_nonneg _ _) (pdl_d_nonneg _ _)
          intro q hq
          obtain ⟨e, he, rfl⟩ := mem_image.1 hq
          exact hφmem e he

/-- `d_k d_l ≤ d_{kl}`. -/
lemma pdl_d_mul_le (k : ℕ) : ∀ l : ℕ, 1 ≤ l → ∀ m : ℕ, pdl_d k m * pdl_d l m ≤ pdl_d (k * l) m := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [pdl_d_one m hm.ne', mul_one, mul_one]
  | succ l hl ih =>
    intro m
    have hpa : pdl_d (k * (l + 1)) = pdl_d (k * l) * pdl_d k := by
      rw [show k * (l + 1) = k * l + k by ring]; exact pow_add _ _ _
    rw [pdl_d_succ_apply, mul_sum, hpa, mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => pdl_d (k * l) x * pdl_d k y)]
    refine sum_le_sum fun e he => ?_
    have hm : e * (m / e) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    calc pdl_d k m * pdl_d l e ≤ (pdl_d k e * pdl_d k (m / e)) * pdl_d l e := by
          refine mul_le_mul_of_nonneg_right ?_ (pdl_d_nonneg _ _)
          conv_lhs => rw [← hm]
          exact pdl_d_submul k _ _
      _ = (pdl_d k e * pdl_d l e) * pdl_d k (m / e) := by ring
      _ ≤ pdl_d (k * l) e * pdl_d k (m / e) :=
          mul_le_mul_of_nonneg_right (ih e) (pdl_d_nonneg _ _)

/-- Rearrangement: sums over divisor antidiagonals of `n ≤ N` sit inside `[1,N]²`. -/
lemma pdl_antidiag_le (N : ℕ) (F : ℕ × ℕ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p ≤
      ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, F p := by
  rw [← sum_biUnion]
  · refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hF p
    intro p hp
    obtain ⟨n, hn, hp⟩ := mem_biUnion.1 hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨hp1, hn0⟩ := hp
    rw [mem_Icc] at hn
    have h1 : p.1 ≠ 0 := fun h => by simp [h] at hp1; omega
    have h2 : p.2 ≠ 0 := fun h => by simp [h] at hp1; omega
    have : p.1 ≤ n := by rw [← hp1]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h2)
    have : p.2 ≤ n := by rw [← hp1]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h1)
    simp only [mem_product, mem_Icc]
    omega
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hx hy
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    exact hxy (hx.1.symm.trans hy.1)

/-- `∑_{n ≤ N} d_k(n)/n ≤ H_N^k`. -/
lemma pdl_d_div_sum (N : ℕ) : ∀ k : ℕ, ∑ n ∈ Icc 1 N, pdl_d k n / n ≤
    (∑ n ∈ Icc 1 N, (1 : ℝ) / n) ^ k := by
  intro k
  induction k with
  | zero =>
    simp only [pdl_d, pow_zero, one_apply]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [← sum_erase_add _ _ (show 1 ∈ Icc 1 N by simp; omega)]
    rw [sum_eq_zero]
    · simp
    intro n hn
    simp [(mem_erase.1 hn).1]
  | succ k ih =>
    have hH : 0 ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / n := sum_nonneg fun _ _ => by positivity
    calc ∑ n ∈ Icc 1 N, pdl_d (k + 1) n / n
        = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, pdl_d k p.1 / p.1 * (1 / p.2) := by
          refine sum_congr rfl fun n hn => ?_
          rw [pdl_d, pow_succ, mul_apply, sum_div]
          refine sum_congr rfl fun p hp => ?_
          rw [Nat.mem_divisorsAntidiagonal] at hp
          have h2 : p.2 ≠ 0 := fun h => by simp [h] at hp; exact hp.2 hp.1.symm
          rw [natCoe_apply, zeta_apply, if_neg h2, ← hp.1]
          push_cast
          field_simp
      _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, pdl_d k p.1 / p.1 * (1 / p.2) :=
          pdl_antidiag_le N _ fun p => mul_nonneg (div_nonneg (pdl_d_nonneg _ _) (by positivity))
            (by positivity)
      _ = (∑ n ∈ Icc 1 N, pdl_d k n / n) * ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
          rw [sum_mul_sum, sum_product]
      _ ≤ (∑ n ∈ Icc 1 N, (1 : ℝ) / n) ^ k * ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
          mul_le_mul_of_nonneg_right ih hH
      _ = _ := by rw [pow_succ]

lemma pdl_harm_le (N : ℕ) : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  simpa [one_div] using this

/-- `∑_{n ≤ N} d_{k+1}(n) ≤ N (1 + log N)^k`. -/
lemma pdl_d_sum_le (N k : ℕ) : ∑ n ∈ Icc 1 N, pdl_d (k + 1) n ≤
    N * (1 + Real.log N) ^ k := by
  have hIoc : Icc 1 N = Ioc 0 N := by ext n; simp; omega
  rw [hIoc, pdl_d, pow_succ, sum_Ioc_mul_zeta_eq_sum, ← hIoc]
  have hH : 0 ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / n := sum_nonneg fun _ _ => by positivity
  calc ∑ n ∈ Icc 1 N, pdl_d k n * ((N / n : ℕ) : ℝ)
      ≤ ∑ n ∈ Icc 1 N, pdl_d k n * ((N : ℝ) / n) :=
        sum_le_sum fun n _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (pdl_d_nonneg _ _)
    _ = N * ∑ n ∈ Icc 1 N, pdl_d k n / n := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    _ ≤ N * (∑ n ∈ Icc 1 N, (1 : ℝ) / n) ^ k :=
        mul_le_mul_of_nonneg_left (pdl_d_div_sum N k) (Nat.cast_nonneg _)
    _ ≤ N * (1 + Real.log N) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH (pdl_harm_le N) k) (Nat.cast_nonneg _)

lemma pdl_norm_conv_le (f g : ArithmeticFunction ℂ) (F G : ArithmeticFunction ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F n) (hg : ∀ n, ‖g n‖ ≤ G n) (n : ℕ) : ‖(f * g) n‖ ≤ (F * G) n := by
  rw [mul_apply, mul_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) ((norm_nonneg _).trans (hf _))

lemma pdl_norm_pow_le (f : ArithmeticFunction ℂ) (F : ArithmeticFunction ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F n) (a n : ℕ) : ‖(f ^ a) n‖ ≤ (F ^ a) n := by
  induction a generalizing n with
  | zero => simp only [pow_zero, one_apply]; split_ifs <;> simp
  | succ a ih => rw [pow_succ, pow_succ]; exact pdl_norm_conv_le _ _ _ _ ih hf n

lemma pdl_conv_support (f g : ArithmeticFunction ℂ) (A1 B1 A2 B2 : ℕ)
    (hf : ∀ n, f n ≠ 0 → A1 < n ∧ n ≤ B1) (hg : ∀ n, g n ≠ 0 → A2 < n ∧ n ≤ B2) (n : ℕ)
    (h : (f * g) n ≠ 0) : A1 * A2 < n ∧ n ≤ B1 * B2 := by
  rw [mul_apply] at h
  obtain ⟨p, hp, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have h1 := hf p.1 (left_ne_zero_of_mul hne)
  have h2 := hg p.2 (right_ne_zero_of_mul hne)
  rw [← hp.1]
  exact ⟨Nat.mul_lt_mul'' h1.1 h2.1, Nat.mul_le_mul h1.2 h2.2⟩

lemma pdl_pow_support (f : ArithmeticFunction ℂ) (A B : ℕ)
    (hf : ∀ n, f n ≠ 0 → A < n ∧ n ≤ B) (a : ℕ) (ha : 1 ≤ a) :
    ∀ n, (f ^ a) n ≠ 0 → A ^ a < n ∧ n ≤ B ^ a := by
  induction a, ha using Nat.le_induction with
  | base => simpa using hf
  | succ a _ ih =>
    intro n hn
    rw [pow_succ] at hn ⊢
    rw [pow_succ]
    exact pdl_conv_support _ _ _ _ _ _ ih hf n hn

lemma pdl_dirichlet_mul (f g : ArithmeticFunction ℂ) (M1 M2 : ℕ)
    (hf : ∀ n, M1 < n → f n = 0) (hg : ∀ n, M2 < n → g n = 0) (s : ℂ) :
    ∑ n ∈ Icc 1 (M1 * M2), (f * g) n * (n : ℂ) ^ (-s) =
      (∑ n ∈ Icc 1 M1, f n * (n : ℂ) ^ (-s)) * ∑ n ∈ Icc 1 M2, g n * (n : ℂ) ^ (-s) := by
  rw [sum_mul_sum, ← sum_product']
  have h1 : ∀ n ∈ Icc 1 (M1 * M2), (f * g) n * (n : ℂ) ^ (-s) =
      ∑ p ∈ n.divisorsAntidiagonal, f p.1 * (p.1 : ℂ) ^ (-s) * (g p.2 * (p.2 : ℂ) ^ (-s)) := by
    intro n _
    rw [mul_apply, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp
    rw [← hp.1]; push_cast
    rw [natCast_mul_natCast_cpow]; ring
  rw [sum_congr rfl h1, ← sum_biUnion]
  · symm
    apply sum_subset
    · intro p hp
      simp only [mem_product, mem_Icc] at hp
      refine mem_biUnion.2 ⟨p.1 * p.2, ?_, ?_⟩
      · rw [mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
          Nat.mul_le_mul hp.1.2 hp.2.2⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        exact ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
    · intro p hp hpn
      obtain ⟨n, hn, hp⟩ := mem_biUnion.1 hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h1 : p.1 ≠ 0 := fun h => by simp [h] at hp; exact hp.2 hp.1.symm
      have h2 : p.2 ≠ 0 := fun h => by simp [h] at hp; exact hp.2 hp.1.symm
      simp only [mem_product, mem_Icc, not_and_or, not_le] at hpn
      rcases hpn with ((h | h) | (h | h))
      · omega
      · rw [hf _ h]; ring
      · omega
      · rw [hg _ h]; ring
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hx hy
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    exact hxy (hx.1.symm.trans hy.1)

lemma pdl_dirichlet_pow (b : ArithmeticFunction ℂ) (M : ℕ) (hb : ∀ n, M < n → b n = 0) (s : ℂ)
    (a : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Icc 1 (M ^ a), (b ^ a) n * (n : ℂ) ^ (-s) = (∑ n ∈ Icc 1 M, b n * (n : ℂ) ^ (-s)) ^ a ∧
      ∀ n, M ^ a < n → (b ^ a) n = 0 := by
  induction a, ha using Nat.le_induction with
  | base => simpa using hb
  | succ a _ ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ, pow_succ, pow_succ, pdl_dirichlet_mul _ _ _ _ ih.2 hb, ih.1]
    · intro n hn
      by_contra hne
      have := (pdl_conv_support (b ^ a) b 0 (M ^ a) 0 M
        (fun n h => ⟨Nat.pos_of_ne_zero (fun h0 => h (by simp [h0])),
          not_lt.1 fun h' => h (ih.2 n h')⟩)
        (fun n h => ⟨Nat.pos_of_ne_zero (fun h0 => h (by simp [h0])),
          not_lt.1 fun h' => h (hb n h')⟩) n (by rwa [← pow_succ])).2
      rw [← pow_succ] at this
      omega

lemma pdl_norm_aX_le (X : ℝ) (n : ℕ) : ‖aX X n‖ ≤ n.divisors.card := by
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

/-- The block coefficients as an arithmetic function. -/
noncomputable def pdl_b (α T : ℝ) (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ blk α T j then coef α T n else 0, by simp [blk]⟩

lemma pdl_b_apply (α T : ℝ) (j n : ℕ) :
    pdl_b α T j n = if n ∈ blk α T j then coef α T n else 0 := rfl

lemma pdl_b_support (α T : ℝ) (j n : ℕ) (h : pdl_b α T j n ≠ 0) :
    N0 α T * 2 ^ j < n ∧ n ≤ 2 * (N0 α T * 2 ^ j) := by
  rw [pdl_b_apply] at h
  split_ifs at h with hn
  · simp only [blk, mem_Ioc, le_min_iff] at hn
    refine ⟨hn.1, ?_⟩
    calc n ≤ N0 α T * 2 ^ (j + 1) := hn.2.1
      _ = 2 * (N0 α T * 2 ^ j) := by ring
  · exact absurd rfl h

lemma pdl_b_norm (α T : ℝ) (hT : 0 ≤ T) (j n : ℕ) : ‖pdl_b α T j n‖ ≤ pdl_d 2 n := by
  rw [pdl_b_apply]
  split_ifs with hn
  · have hn0 : n ≠ 0 := by
      simp only [blk, mem_Ioc] at hn; omega
    rw [pdl_d_succ_apply]
    have : ∑ i ∈ n.divisors, pdl_d 1 i = n.divisors.card := by
      rw [card_eq_sum_ones]; push_cast
      exact sum_congr rfl fun i hi => pdl_d_one i (Nat.pos_of_mem_divisors hi).ne'
    rw [this, coef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(n : ℝ) / Yp α T) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hT _)
    calc ‖aX (Xp α T) n‖ * Real.exp (-(n : ℝ) / Yp α T) ≤ n.divisors.card * 1 :=
          mul_le_mul (pdl_norm_aX_le _ _) he (Real.exp_pos _).le (Nat.cast_nonneg _)
      _ = _ := mul_one _
  · rw [norm_zero]; exact pdl_d_nonneg _ _

lemma pdl_Dj_eq (α T : ℝ) (j : ℕ) (s : ℂ) :
    Dj α T j s = ∑ n ∈ Icc 1 (2 * (N0 α T * 2 ^ j)), pdl_b α T j n * (n : ℂ) ^ (-s) := by
  rw [Dj]
  simp_rw [pdl_b_apply, ite_mul, zero_mul]
  rw [sum_ite_mem]
  congr 1
  ext n
  simp only [blk, mem_inter, mem_Icc, mem_Ioc, le_min_iff]
  constructor
  · intro h; refine ⟨⟨by omega, ?_⟩, h⟩
    calc n ≤ N0 α T * 2 ^ (j + 1) := h.2.1
      _ = 2 * (N0 α T * 2 ^ j) := by ring
  · exact fun h => h.2

lemma pdl_rpow_aux (U : ℝ) (hU : 0 < U) (a : ℕ) (α : ℝ) (p q : ℕ) :
    ((U ^ a) ^ (-α)) ^ p * (U ^ a) ^ q = U ^ ((a : ℝ) * (q - p * α)) := by
  rw [← Real.rpow_natCast U a, ← Real.rpow_mul hU.le, ← Real.rpow_natCast _ p,
    ← Real.rpow_natCast (U ^ (a : ℝ)) q, ← Real.rpow_mul hU.le, ← Real.rpow_mul hU.le,
    ← Real.rpow_add hU]
  congr 1; ring

lemma pdl_V_aux (V : ℝ) (hV : 0 < V) (a p : ℕ) :
    V ^ (-((p : ℝ) * (a : ℝ))) = ((V ^ a) ^ p)⁻¹ := by
  rw [Real.rpow_neg hV.le, ← pow_mul, ← Real.rpow_natCast]
  push_cast; ring_nf

theorem block_count (A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T → ∀ α : ℝ, 3 / 4 ≤ α → α < 1 →
    1 ≤ N0 α T → ∀ (j a : ℕ), 1 ≤ a → a ≤ A → ∀ V : ℝ, 0 < V → ∀ P : Finset ℂ,
      (∀ s ∈ P, α ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T ∧ V ≤ ‖Dj α T j s‖) →
      (∀ s ∈ P, ∀ s' ∈ P, s ≠ s' → 1 ≤ |s.im - s'.im|) →
      (P.card : ℝ) ≤ C * Bfun α T a ((N0 α T : ℝ) * 2 ^ j) V := by
  obtain ⟨CH, hH⟩ := GuthMaynard.card_le_of_large_values_huxley
  refine ⟨max CH 0 * 16 ^ A, by positivity, ?_⟩
  intro T hT α hα1 hα2 hN0 j a ha1 haA V hV P hP hsep
  set U' : ℕ := N0 α T * 2 ^ j with hU'
  set M : ℕ := 2 * U' with hM
  set N : ℕ := M ^ a with hN
  set c : ArithmeticFunction ℂ := (pdl_b α T j) ^ a with hc
  have hU'1 : 1 ≤ U' := by
    rw [hU']; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hbM : ∀ n, M < n → pdl_b α T j n = 0 := fun n hn => by
    by_contra h; have := (pdl_b_support α T j n h).2; omega
  have hcsupp : ∀ n, c n ≠ 0 → U' ^ a < n ∧ n ≤ M ^ a :=
    pdl_pow_support _ _ _ (pdl_b_support α T j) a ha1
  have hD : ∀ s : ℂ, (Dj α T j s) ^ a = ∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ (-s) := by
    intro s
    rw [pdl_Dj_eq, (pdl_dirichlet_pow _ M hbM s a ha1).1]
  set am : ℕ → ℂ := fun m => c m * (m : ℂ) ^ (-(α : ℂ)) with ham
  have hsum : ∀ s : ℂ, ∑ m ∈ Icc 1 N, am m * (m : ℂ) ^ (-(s - α)) = (Dj α T j s) ^ a := by
    intro s
    rw [hD]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : (m : ℂ) ≠ 0 := by
      have := (mem_Icc.1 hm).1; exact_mod_cast (show m ≠ 0 by omega)
    rw [ham]; dsimp only
    rw [mul_assoc, ← cpow_add _ _ hm0]
    congr 2; ring
  -- the points
  set R := P.card with hR
  set e := P.equivFin
  set pts : Fin R → ℂ := fun r => ((e.symm r : ℂ)) - α with hpts
  have hre : ∀ r, 0 ≤ (pts r).re ∧ (pts r).re ≤ 1 / 4 := by
    intro r
    obtain ⟨h1, h2, -⟩ := hP _ (e.symm r).2
    simp only [hpts, sub_re, ofReal_re]
    constructor <;> linarith
  have hsep' : ∀ r q, r ≠ q → 1 ≤ |(pts r).im - (pts q).im| ∧ |(pts r).im - (pts q).im| ≤ T := by
    intro r q hrq
    have hne : (e.symm r : ℂ) ≠ e.symm q := fun h => hrq (e.symm.injective (Subtype.ext h))
    obtain ⟨-, -, h3, h4, -⟩ := hP _ (e.symm r).2
    obtain ⟨-, -, h3', h4', -⟩ := hP _ (e.symm q).2
    simp only [hpts, sub_im, ofReal_im, sub_zero]
    refine ⟨hsep _ (e.symm r).2 _ (e.symm q).2 hne, ?_⟩
    rw [abs_le]; constructor <;> linarith
  have hlarge : ∀ r, V ^ a ≤ ‖∑ m ∈ Icc 1 N, am m * (m : ℂ) ^ (-pts r)‖ := by
    intro r
    rw [hpts]; dsimp only
    rw [hsum, norm_pow]
    exact pow_le_pow_left₀ hV.le (hP _ (e.symm r).2).2.2.2.2 a
  have key := hH N hN1 T (by linarith) am (V ^ a) (pow_pos hV a) R pts hre hsep' hlarge
  -- the mean square
  set U : ℝ := (N0 α T : ℝ) * 2 ^ j with hU
  have hUU' : (U' : ℝ) = U := by rw [hU', hU]; push_cast; ring
  have hU1 : 1 ≤ U := by rw [← hUU']; exact_mod_cast hU'1
  have hU0 : 0 < U := by linarith
  have hNreal : (N : ℝ) = 2 ^ a * U ^ a := by
    rw [hN, hM]; push_cast; rw [hUU', mul_pow]
  set L := 1 + Real.log (2 ^ a * U ^ a) with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (2 ^ a * U ^ a) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ U ^ a := one_le_pow₀ hU1
      nlinarith)
    linarith
  set w : ℝ := (U ^ a) ^ (-α) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  set k : ℕ := 4 * a ^ 2 - 1 with hk
  have hk1 : 4 * a ^ 2 = k + 1 := by
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha1
    omega
  set G := ∑ m ∈ Icc 1 N, ‖am m‖ ^ 2 with hG
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => by positivity
  have hGle : G ≤ w ^ 2 * (N * L ^ k) := by
    have hterm : ∀ m ∈ Icc 1 N, ‖am m‖ ^ 2 ≤ w ^ 2 * pdl_d (k + 1) m := by
      intro m hm
      have hm1 := (mem_Icc.1 hm).1
      rw [ham]; dsimp only
      by_cases hcm : c m = 0
      · rw [hcm, zero_mul, norm_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (by positivity) (pdl_d_nonneg _ _)
      have hlt := (hcsupp m hcm).1
      rw [norm_mul, norm_natCast_cpow_of_pos (by omega)]
      simp only [neg_re, ofReal_re]
      have hc1 : ‖c m‖ ≤ pdl_d (2 * a) m := by
        rw [hc, pdl_d, pow_mul]
        exact pdl_norm_pow_le _ _ (pdl_b_norm α T (by linarith) j) a m
      have hmw : (m : ℝ) ^ (-α) ≤ w := by
        rw [hw]
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
        rw [← hUU']; exact_mod_cast hlt.le
      have hmw0 : 0 ≤ (m : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc (‖c m‖ * (m : ℝ) ^ (-α)) ^ 2 ≤ (pdl_d (2 * a) m * w) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul hc1 hmw hmw0
              ((norm_nonneg _).trans hc1)) 2
        _ = w ^ 2 * (pdl_d (2 * a) m * pdl_d (2 * a) m) := by ring
        _ ≤ w ^ 2 * pdl_d (2 * a * (2 * a)) m :=
            mul_le_mul_of_nonneg_left (pdl_d_mul_le _ _ (by omega) m) (by positivity)
        _ = w ^ 2 * pdl_d (k + 1) m := by rw [← hk1]; ring_nf
    calc G ≤ ∑ m ∈ Icc 1 N, w ^ 2 * pdl_d (k + 1) m := sum_le_sum hterm
      _ = w ^ 2 * ∑ m ∈ Icc 1 N, pdl_d (k + 1) m := by rw [mul_sum]
      _ ≤ w ^ 2 * (N * (1 + Real.log N) ^ k) :=
          mul_le_mul_of_nonneg_left (pdl_d_sum_le N k) (by positivity)
      _ = w ^ 2 * (N * L ^ k) := by rw [hL, hNreal]
  -- assemble
  have hVa : 0 < V ^ a := pow_pos hV a
  have hT0 : 0 < T := by linarith
  set X := G * N / (V ^ a) ^ 2 + G ^ 3 * N * T / (V ^ a) ^ 6 * Real.log (N * T) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hBfun : Bfun α T a U V = U ^ (2 * (a : ℝ) * (1 - α)) * L ^ k * V ^ (-(2 * (a : ℝ))) +
      U ^ ((a : ℝ) * (4 - 6 * α)) * T * L ^ (3 * k) * V ^ (-(6 * (a : ℝ))) *
        Real.log (2 ^ a * U ^ a * T) ^ 2 := rfl
  have hw2 : w ^ 2 * (U ^ a) ^ 2 = U ^ (2 * (a : ℝ) * (1 - α)) := by
    rw [hw, pdl_rpow_aux U hU0 a α 2 2]; congr 1; push_cast; ring
  have hw6 : w ^ 6 * (U ^ a) ^ 4 = U ^ ((a : ℝ) * (4 - 6 * α)) := by
    rw [hw, pdl_rpow_aux U hU0 a α 6 4]; norm_num
  have hV2 : V ^ (-(2 * (a : ℝ))) = ((V ^ a) ^ 2)⁻¹ := by
    rw [← pdl_V_aux V hV a 2]; push_cast; ring_nf
  have hV6 : V ^ (-(6 * (a : ℝ))) = ((V ^ a) ^ 6)⁻¹ := by
    rw [← pdl_V_aux V hV a 6]; push_cast; ring_nf
  have hB0 : 0 ≤ Bfun α T a U V := by
    rw [hBfun, hV2, hV6]; positivity
  have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hX1 : X ≤ (2 ^ a) ^ 4 * Bfun α T a U V := by
    have t1 : G * N / (V ^ a) ^ 2 ≤ (2 ^ a) ^ 2 *
        (U ^ (2 * (a : ℝ) * (1 - α)) * L ^ k * V ^ (-(2 * (a : ℝ)))) := by
      rw [hV2, ← hw2]
      calc G * N / (V ^ a) ^ 2 ≤ w ^ 2 * (N * L ^ k) * N / (V ^ a) ^ 2 := by gcongr
        _ = (2 ^ a) ^ 2 * (w ^ 2 * (U ^ a) ^ 2 * L ^ k * ((V ^ a) ^ 2)⁻¹) := by
          rw [hNreal]; field_simp
    have t2 : G ^ 3 * N * T / (V ^ a) ^ 6 * Real.log (N * T) ^ 2 ≤ (2 ^ a) ^ 4 *
        (U ^ ((a : ℝ) * (4 - 6 * α)) * T * L ^ (3 * k) * V ^ (-(6 * (a : ℝ))) *
          Real.log (2 ^ a * U ^ a * T) ^ 2) := by
      rw [hV6, ← hw6, ← hNreal]
      calc G ^ 3 * N * T / (V ^ a) ^ 6 * Real.log (N * T) ^ 2
          ≤ (w ^ 2 * (N * L ^ k)) ^ 3 * N * T / (V ^ a) ^ 6 * Real.log (N * T) ^ 2 := by gcongr
        _ = (2 ^ a) ^ 4 * (w ^ 6 * (U ^ a) ^ 4 * T * L ^ (3 * k) * ((V ^ a) ^ 6)⁻¹ *
              Real.log (N * T) ^ 2) := by
          rw [hNreal]; field_simp; ring
    rw [hX, hBfun, mul_add]
    have hT1nn : 0 ≤ U ^ (2 * (a : ℝ) * (1 - α)) * L ^ k * V ^ (-(2 * (a : ℝ))) := by
      rw [hV2]; positivity
    have : (2 ^ a : ℝ) ^ 2 ≤ (2 ^ a) ^ 4 := pow_le_pow_right₀ h2a (by norm_num)
    nlinarith
  have h16 : ((2 : ℝ) ^ a) ^ 4 ≤ 16 ^ A := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact pow_le_pow_right₀ (by norm_num) haA
  calc (P.card : ℝ) = R := rfl
    _ ≤ CH * X := key
    _ ≤ max CH 0 * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ ≤ max CH 0 * ((2 ^ a) ^ 4 * Bfun α T a U V) :=
        mul_le_mul_of_nonneg_left hX1 (le_max_right _ _)
    _ ≤ max CH 0 * (16 ^ A * Bfun α T a U V) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 hB0) (le_max_right _ _)
    _ = max CH 0 * 16 ^ A * Bfun α T a U V := by ring

theorem pdl_exists_separated_cover (F : Finset ℂ) :
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

lemma pdl_blocks_partial (α T : ℝ) (s : ℂ) (J : ℕ) :
    ∑ j ∈ range J, Dj α T j s =
      ∑ n ∈ Ioc (N0 α T) (min (N0 α T * 2 ^ J) (Ztop α T)), coef α T n * (n : ℂ) ^ (-s) := by
  induction J with
  | zero =>
    rw [sum_range_zero, Ioc_eq_empty_of_le (by simp), sum_empty]
  | succ J ih =>
    rw [sum_range_succ, ih, Dj, blk]
    have hmono : N0 α T * 2 ^ J ≤ N0 α T * 2 ^ (J + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (Nat.le_succ _))
    by_cases h : N0 α T * 2 ^ J ≤ Ztop α T
    · rw [min_eq_left h, sum_Ioc_consecutive]
      · exact Nat.le_mul_of_pos_right _ (by positivity)
      · exact le_min hmono h
    · push Not at h
      rw [min_eq_right h.le, min_eq_right (h.le.trans hmono),
        Ioc_eq_empty_of_le (show Ztop α T ≤ N0 α T * 2 ^ J by omega),
        sum_empty, add_zero]

theorem SI_eq_sum_blocks (α T : ℝ) (h : 1 ≤ N0 α T) (s : ℂ) :
    SI α T s = ∑ j ∈ Finset.range (Jn α T), Dj α T j s := by
  rw [pdl_blocks_partial, min_eq_right, SI]
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Ztop α T / N0 α T)
  rw [Nat.div_lt_iff_lt_mul (by omega)] at h1
  rw [Jn, mul_comm]
  exact h1.le

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
/-! ### Parameters -/
lemma pdl_e1_bounds {α : ℝ} (h1 : 9 / 11 ≤ α) (h2 : α ≤ 1) :
    1 / 72 ≤ 3 * (2 * α - 1) / (12 * α - 4) - 157 / 500 ∧
      3 * (2 * α - 1) / (12 * α - 4) - 157 / 500 ≤ 1 / 16 := by
  have hp : 0 < 12 * α - 4 := by linarith
  constructor
  · have : 1 / 72 + 157 / 500 ≤ 3 * (2 * α - 1) / (12 * α - 4) := by
      rw [le_div_iff₀ hp]; nlinarith
    linarith
  · have : 3 * (2 * α - 1) / (12 * α - 4) ≤ 1 / 16 + 157 / 500 := by
      rw [div_le_iff₀ hp]; nlinarith
    linarith

lemma pdl_e2_bounds {α : ℝ} (h1 : 9 / 11 ≤ α) (h2 : α ≤ 1) :
    3 / 8 ≤ 3 / (12 * α - 4) ∧ 3 / (12 * α - 4) ≤ 1 := by
  have hp : 0 < 12 * α - 4 := by linarith
  constructor
  · rw [le_div_iff₀ hp]; linarith
  · rw [div_le_iff₀ hp]; linarith

lemma pdl_X_bounds {α T : ℝ} (h1 : 9 / 11 ≤ α) (h2 : α ≤ 1) (hT : 1 ≤ T) :
    1 ≤ Xp α T ∧ Xp α T ≤ T := by
  obtain ⟨e1, e2⟩ := pdl_e1_bounds h1 h2
  unfold Xp
  constructor
  · exact Real.one_le_rpow hT (by linarith)
  · calc T ^ (3 * (2 * α - 1) / (12 * α - 4) - 157 / 500) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T := Real.rpow_one T

lemma pdl_Y_bounds {α T : ℝ} (h1 : 9 / 11 ≤ α) (h2 : α ≤ 1) (hT : 1 ≤ T) :
    T ^ (1 / 4 : ℝ) ≤ Yp α T ∧ Yp α T ≤ T := by
  obtain ⟨e1, e2⟩ := pdl_e2_bounds h1 h2
  unfold Yp
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · calc T ^ (3 / (12 * α - 4)) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT e2
      _ = T := Real.rpow_one T

lemma pdl_X_le_Y {α T : ℝ} (h1 : 9 / 11 ≤ α) (h2 : α ≤ 1) (hT : 1 ≤ T) :
    Xp α T ≤ Yp α T := by
  obtain ⟨e1, e2⟩ := pdl_e1_bounds h1 h2
  obtain ⟨f1, f2⟩ := pdl_e2_bounds h1 h2
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

lemma pdl_quarter_ge {T : ℝ} (hT : 10 ^ 8 ≤ T) : 100 ≤ T ^ (1 / 4 : ℝ) := by
  have h : (100 : ℝ) = ((100 : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) :=
    (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
  rw [h, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)

/-! ### Exponential decay of `Γ` -/
lemma pdl_gamma_exp (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re ≤ 1) (hγ : 6 ≤ |z.im|) :
    ‖Complex.Gamma z‖ ≤ Real.exp (1 / 2 - |z.im| / 4) := by
  set y := |z.im| with hy
  set n : ℕ := ⌊y / 2⌋₊ with hn
  have hy0 : 0 < y := by linarith
  have hn1 : (n : ℝ) ≤ y / 2 := Nat.floor_le (by linarith)
  have hn2 : y / 2 - 1 < n := by have := Nat.lt_floor_add_one (y / 2); rw [← hn] at this; linarith
  have hn3 : 2 ≤ n := by
    have : (2 : ℝ) < n + 1 := by linarith
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast (show 1 < n by exact_mod_cast this)
  have hzne : z.im ≠ 0 := by intro h; rw [hy, h] at hy0; simp at hy0
  have hzre : 0 < (z + n).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hG1 : y ^ n * ‖Complex.Gamma z‖ ≤ Real.Gamma (z + n).re := by
    calc y ^ n * ‖Complex.Gamma z‖
        ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Complex.Gamma z‖ :=
          mul_le_mul_of_nonneg_right (pdl_gamma_shift_norm_lower z n) (norm_nonneg _)
      _ = ‖Complex.Gamma (z + n)‖ := by rw [pdl_gamma_shift z hzne n, norm_mul, mul_comm]
      _ ≤ Real.Gamma (z + n).re := pdl_norm_Gamma_le_real _ hzre
  have hG2 : Real.Gamma (z + n).re ≤ (n : ℝ) ^ n := by
    have hre : (z + n).re = z.re + n := by simp
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn3
    calc Real.Gamma (z + n).re ≤ Real.Gamma ((n : ℝ) + 1) := by
          rw [hre]
          exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith)
            (by simp; linarith) (by linarith)
      _ = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hyn : 0 < y ^ n := by positivity
  have hG : ‖Complex.Gamma z‖ ≤ ((n : ℝ) / y) ^ n := by
    rw [div_pow, le_div_iff₀ hyn, mul_comm]; linarith
  have hratio : (n : ℝ) / y ≤ 1 / 2 := by rw [div_le_iff₀ hy0]; linarith
  calc ‖Complex.Gamma z‖ ≤ ((n : ℝ) / y) ^ n := hG
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = Real.exp (-(n * Real.log 2)) := by
        rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.rpow_natCast,
          Real.exp_log (by positivity)]; simp
    _ ≤ Real.exp (1 / 2 - y / 4) := by
        apply Real.exp_le_exp.mpr
        have := Real.log_two_gt_d9
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem pdl_res_small (ε : ℝ) (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ X Y : ℝ, 0 ≤ X →
    X ≤ T → 1 ≤ Y → Y ≤ T → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → Real.log T ^ 2 ≤ ρ.im →
      ‖pdl_Res X Y ρ‖ ≤ ε := by
  refine ⟨Real.exp (12 + |Real.log ε|), fun T hT X Y hX0 hXT hY1 hYT ρ hρ0 hρ1 hγ => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  set l := Real.log T with hl
  have hl12 : 12 + |Real.log ε| ≤ l := by
    rw [hl, ← Real.log_exp (12 + |Real.log ε|)]; exact Real.log_le_log (Real.exp_pos _) hT
  have habs := neg_abs_le (Real.log ε)
  have hl0 : 12 ≤ l := by linarith [abs_nonneg (Real.log ε)]
  have hl2 : 12 * l ≤ l ^ 2 := by nlinarith
  have hY0 : 0 < Y := by linarith
  unfold pdl_Res
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0]
  have f1 : Y ^ ((1 - ρ).re) ≤ T := by
    calc Y ^ ((1 - ρ).re) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by simp; linarith)
      _ = Y := Real.rpow_one Y
      _ ≤ T := hYT
  have f3 : ‖molli X 1‖ ≤ T := (pdl_molli_bound X (by simp)).trans ((Nat.floor_le hX0).trans hXT)
  have him : |(1 - ρ).im| = ρ.im := by
    simp only [sub_im, one_im, zero_sub, abs_neg]
    exact abs_of_nonneg (le_trans (sq_nonneg _) hγ)
  have hγ6 : 6 ≤ |(1 - ρ).im| := by rw [him]; linarith
  have f2 := pdl_gamma_exp (1 - ρ) (by simp; linarith) (by simp; linarith) hγ6
  rw [him] at f2
  have f2' : ‖Complex.Gamma (1 - ρ)‖ ≤ Real.exp (1 / 2 - l ^ 2 / 4) :=
    f2.trans (Real.exp_le_exp.mpr (by linarith))
  have hTT : T * T = Real.exp (2 * l) := by
    rw [show 2 * l = l + l by ring, Real.exp_add, hl, Real.exp_log hT0]
  calc Y ^ ((1 - ρ).re) * ‖Complex.Gamma (1 - ρ)‖ * ‖molli X 1‖
      ≤ T * Real.exp (1 / 2 - l ^ 2 / 4) * T := by gcongr
    _ = Real.exp (2 * l + (1 / 2 - l ^ 2 / 4)) := by rw [Real.exp_add, ← hTT]; ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε

/-! ### Detection -/
theorem pdl_detect_shift : ∃ K : ℝ, 0 ≤ K ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y → ∀ ρ : ℂ,
    riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 ≤ ρ.im →
      ‖pdl_lineInt X Y ρ (1 / 2 - ρ.re) - pdl_Iser X Y ρ‖ ≤ K * ‖pdl_Res X Y ρ‖ := by
  obtain ⟨K, hK0, hK⟩ := pdl_contour_shift
  refine ⟨K, hK0, fun X Y hX hY ρ h0 hρ0 hρ1 _ => ?_⟩
  rw [← pdl_mellin_line (by linarith) (by linarith) hρ0]
  exact hK X Y hY ρ h0 hρ0 hρ1

theorem pdl_tail_small : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, 9 / 11 ≤ α → α ≤ 1 →
    ∀ ρ : ℂ, 0 < ρ.re →
      ‖pdl_Iser (Xp α T) (Yp α T) ρ - (Real.exp (-1 / Yp α T) : ℂ) - SI α T ρ‖ ≤ 1 / 100 := by
  refine ⟨Real.exp 8, fun T hT α hα1 hα2 ρ hρ => ?_⟩
  have hT30 : (30 : ℝ) ≤ T := le_trans (by
    have := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 8 by norm_num); linarith) hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set l := Real.log T with hl
  have hl8 : 8 ≤ l := by
    rw [hl, ← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hT
  obtain ⟨hX1, hXT⟩ := pdl_X_bounds hα1 hα2 hT1
  obtain ⟨hY1', hYT⟩ := pdl_Y_bounds hα1 hα2 hT1
  have hXs := pdl_X_le_Y hα1 hα2 hT1
  set X := Xp α T with hXdef
  set Y := Yp α T with hYdef
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow hT1 (by norm_num)) hY1'
  have hY0 : 0 < Y := by linarith
  set b : ℕ → ℂ := fun n => aX X n * (Real.exp (-(n : ℝ) / Y) : ℂ) * (n : ℂ) ^ (-ρ) with hb
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
    have h2 := pdl_aX_norm_le X n
    calc ‖aX X n‖ * Real.exp (-(n : ℝ) / Y) * (n : ℝ) ^ (-ρ).re
        ≤ (n : ℝ) * Real.exp (-(n : ℝ) / Y) * 1 := by gcongr
      _ = _ := by ring
  have hsumm : Summable b := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) / Y))
    · obtain ⟨g, hg, hgb, _⟩ := pdl_tail_est hY1 (le_refl (0 : ℝ)) 0 (by simp)
      refine (hg.of_nonneg_of_le (fun i => by positivity) (fun i => ?_))
      simpa using hgb i
    · exact hbn
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hYX : X ≤ Y * l ^ 2 := by nlinarith
  set M : ℕ := ⌊Y * l ^ 2⌋₊ with hM
  set F : ℕ := ⌊X⌋₊ with hF
  have hF1 : 1 ≤ F := Nat.le_floor (by simpa using hX1)
  have hFM : F ≤ M := Nat.floor_le_floor hYX
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
    have hnT : (n : ℝ) ≤ X := by
      have : n ≤ F := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
    simp [hb, pdl_aX_zero_of hn.1 hnT]
  have hb0 : b 0 = 0 := by simp [hb, aX]
  have hb1 : b 1 = (Real.exp (-1 / Y) : ℂ) := by
    simp [hb, pdl_aX_one hX1]
  have hSI : SI α T ρ = ∑ n ∈ Finset.Ioc F M, b n := by
    unfold SI coef N0 Ztop
    rfl
  have hI : pdl_Iser X Y ρ = ∑' n : ℕ, b n := rfl
  have hid : pdl_Iser X Y ρ - (Real.exp (-1 / Y) : ℂ) - SI α T ρ = ∑' i, b (i + (M + 1)) := by
    rw [hI, ← hsplit, hfin, hmid, hb0, hb1, hSI]
    ring
  rw [hid]
  have hXk : Y * l ^ 2 ≤ ((M + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (Y * l ^ 2)
    push_cast
    linarith
  obtain ⟨g, hg, hgb, hgs⟩ := pdl_tail_est hY1 (by positivity) (M + 1) hXk
  have hnorm : ‖∑' i, b (i + (M + 1))‖ ≤ ∑' i, g i :=
    tsum_of_norm_bounded hg.hasSum (fun i => (hbn (i + (M + 1))).trans (hgb i))
  refine hnorm.trans (hgs.trans ?_)
  have e : -(Y * l ^ 2) / (2 * Y) = -(l ^ 2) / 2 := by field_simp
  rw [e]
  have hexp : Real.exp (-(l ^ 2) / 2) ≤ Real.exp (-(4 * l)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hT4 : Real.exp (-(4 * l)) * T ^ 4 = 1 := by
    have : T ^ 4 = Real.exp (4 * l) := by
      rw [show (4 : ℝ) * l = ((4 : ℕ) : ℝ) * l by norm_num, Real.exp_nat_mul, hl,
        Real.exp_log hT0]
    rw [this, ← Real.exp_add]; simp
  have h9 : (2 * Y + 1) ^ 2 ≤ 9 * T ^ 2 := by nlinarith
  have hT2 : 900 ≤ T ^ 2 := by nlinarith
  calc Real.exp (-(l ^ 2) / 2) * (2 * Y + 1) ^ 2
      ≤ Real.exp (-(4 * l)) * (9 * T ^ 2) := by gcongr
    _ = 9 * (Real.exp (-(4 * l)) * T ^ 4) / T ^ 2 := by field_simp
    _ ≤ 1 / 100 := by
        rw [hT4, div_le_iff₀ (by positivity)]; linarith

lemma pdl_lineInt_upper' (X Y : ℝ) (hY : 0 < Y) (ρ : ℂ) :
    ‖pdl_lineInt X Y ρ (1 / 2 - ρ.re)‖ ≤
      1 / (2 * Real.pi) * (Y ^ (1 / 2 - ρ.re) * ∫ u : ℝ, kII X ρ.re ρ.im u) :=
  pdl_lineInt_upper X Y hY ρ

theorem detect : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, 9 / 11 ≤ α → α < 1 →
    ∀ ρ : ℂ, riemannZeta ρ = 0 → α ≤ ρ.re → Real.log T ^ 2 ≤ ρ.im → ρ.im ≤ T →
      IsTypeI α T ρ ∨ IsTypeII α T ρ := by
  obtain ⟨K, hK0, hK⟩ := pdl_detect_shift
  obtain ⟨T₁, hT₁⟩ := pdl_res_small (1 / 100 / (K + 1)) (by positivity)
  obtain ⟨T₂, hT₂⟩ := pdl_tail_small
  refine ⟨max (max T₁ T₂) (10 ^ 8), fun T hT α hα1 hα2 ρ h0 hβ hγ1 hγ2 => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT100 : (10 ^ 8 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTone : (1 : ℝ) ≤ T := by linarith
  obtain ⟨hX1, hXT⟩ := pdl_X_bounds hα1 hα2.le hTone
  obtain ⟨hY1', hYT⟩ := pdl_Y_bounds hα1 hα2.le hTone
  have hY100 : (100 : ℝ) ≤ Yp α T := le_trans (pdl_quarter_ge hT100) hY1'
  have hY0 : 0 < Yp α T := by linarith
  have hl1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hl2 : 1 ≤ Real.log T ^ 2 := by nlinarith
  have hρ0 : 0 < ρ.re := by linarith
  have hρ1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h h0
  by_cases hI : IsTypeI α T ρ
  · exact Or.inl hI
  right
  unfold IsTypeI at hI
  push Not at hI
  set X := Xp α T with hXdef
  set Y := Yp α T with hYdef
  have hR := hT₁ T hT1 X Y (by linarith) hXT (by linarith) hYT ρ hρ0 hρ1 hγ1
  have hKR : K * ‖pdl_Res X Y ρ‖ ≤ 1 / 100 := by
    calc K * ‖pdl_Res X Y ρ‖ ≤ K * (1 / 100 / (K + 1)) := by gcongr
      _ ≤ 1 / 100 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith
  have hsh := hK X Y hX1 (by linarith) ρ h0 hρ0 hρ1 (by linarith)
  have htail := hT₂ T hT2 α hα1 hα2.le ρ hρ0
  have hexp : 99 / 100 ≤ Real.exp (-1 / Y) := by
    have h1 := Real.add_one_le_exp (-1 / Y)
    have h2 : 1 / Y ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h3 : -1 / Y = -(1 / Y) := by ring
    linarith
  have hIs : 48 / 100 ≤ ‖pdl_Iser X Y ρ‖ := by
    have e1 : (Real.exp (-1 / Y) : ℂ) = pdl_Iser X Y ρ -
        (pdl_Iser X Y ρ - (Real.exp (-1 / Y) : ℂ) - SI α T ρ) - SI α T ρ := by ring
    have e2 : ‖(Real.exp (-1 / Y) : ℂ)‖ = Real.exp (-1 / Y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h3 := norm_sub_le (pdl_Iser X Y ρ -
        (pdl_Iser X Y ρ - (Real.exp (-1 / Y) : ℂ) - SI α T ρ)) (SI α T ρ)
    have h4 := norm_sub_le (pdl_Iser X Y ρ)
        (pdl_Iser X Y ρ - (Real.exp (-1 / Y) : ℂ) - SI α T ρ)
    rw [← e1, e2] at h3
    linarith
  have hL : 47 / 100 ≤ ‖pdl_lineInt X Y ρ (1 / 2 - ρ.re)‖ := by
    have := norm_sub_norm_le (pdl_Iser X Y ρ) (pdl_Iser X Y ρ - pdl_lineInt X Y ρ (1 / 2 - ρ.re))
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hsh
    linarith
  have hU := pdl_lineInt_upper' X Y hY0 ρ
  unfold IsTypeII
  set J := ∫ u : ℝ, kII X ρ.re ρ.im u with hJ
  set a := Y ^ (ρ.re - 1 / 2) with ha
  have hY1 : 1 ≤ Y := by linarith
  have hab : Y ^ (α - 1 / 2) ≤ a := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
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

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
/-! ## Step 1: detection, and no Type II zeros -/
alias detect := GuthMaynard.CitedZeros.HR2.PartDL.detect

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
/-! ### `zeta_half_bound` -/
theorem zeta_half_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (156 / 1000 : ℝ) := by
  have hmu := LindelofHypothesis.mu_half_le_thirteen_div_eightyfour
  unfold LindelofHypothesis.mu at hmu
  have hlt : sInf ((fun a : ℝ => (a : EReal)) ''
      {a : ℝ | (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ a)}) < ((156 / 1000 : ℝ) : EReal) :=
    lt_of_le_of_lt hmu (EReal.coe_lt_coe_iff.mpr (by norm_num))
  obtain ⟨x, hx, hxlt⟩ := sInf_lt_iff.mp hlt
  obtain ⟨a, ha, rfl⟩ := hx
  have ha' : a < 156 / 1000 := EReal.coe_lt_coe_iff.mp hxlt
  obtain ⟨C₁, hC₁⟩ := Asymptotics.IsBigO.bound ha
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hC₁
  set T₂ := max T₁ 1 with hT₂
  have hcont : ContinuousOn (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) (Icc (-T₂) T₂) :=
    pdl_zeta_line_cont.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  have hpos : ∀ t : ℝ, 0 < t → T₂ ≤ t →
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ |C₁| * (|t| + 2) ^ (156 / 1000 : ℝ) := by
    intro t ht0 ht
    have h1 := hT₁ t ((le_max_left _ _).trans ht)
    have e : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by push_cast; ring
    rw [e, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)] at h1
    have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
    have h2 : t ^ a ≤ t ^ (156 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 ha'.le
    have h3 : t ^ (156 / 1000 : ℝ) ≤ (|t| + 2) ^ (156 / 1000 : ℝ) :=
      Real.rpow_le_rpow ht0.le (by rw [abs_of_pos ht0]; linarith) (by norm_num)
    calc ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C₁ * t ^ a := h1
      _ ≤ |C₁| * t ^ a := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * (|t| + 2) ^ (156 / 1000 : ℝ) := by gcongr; exact h2.trans h3
  refine ⟨|C₁| + |B|, by positivity, fun t => ?_⟩
  have hge : 1 ≤ (|t| + 2) ^ (156 / 1000 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  have hP : 0 ≤ (|t| + 2) ^ (156 / 1000 : ℝ) := by positivity
  by_cases ht : T₂ ≤ |t|
  · have hT2pos : 0 < T₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht
      have := hpos t (by linarith) ht
      nlinarith [abs_nonneg B]
    · have hconj : riemannZeta (1 / 2 + (t : ℂ) * I) =
          (starRingEnd ℂ) (riemannZeta (1 / 2 + ((-t : ℝ) : ℂ) * I)) := by
        rw [← riemannZeta_conj]
        congr 1
        apply Complex.ext <;> simp
      rw [abs_of_neg h0] at ht
      have := hpos (-t) (by linarith) ht
      rw [hconj, Complex.norm_conj]
      rw [abs_neg] at this
      nlinarith [abs_nonneg B]
  · push Not at ht
    have hmem : t ∈ Icc (-T₂) T₂ := by
      rw [abs_lt] at ht; exact ⟨by linarith, by linarith⟩
    have := hB t hmem
    have hB' : B ≤ |B| := le_abs_self B
    nlinarith [mul_le_mul_of_nonneg_left hge (abs_nonneg B), mul_nonneg (abs_nonneg C₁) hP]

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set Metric
/-! ### `no_typeII` -/
lemma pdl_Y_exp {α T : ℝ} (hα : 9 / 11 ≤ α) (hT : 0 < T) :
    Yp α T ^ (α - 1 / 2) = Xp α T ^ (1 / 2 : ℝ) * T ^ (157 / 1000 : ℝ) := by
  unfold Yp Xp
  rw [← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_add hT]
  congr 1
  have hp : 12 * α - 4 ≠ 0 := by intro h; linarith
  field_simp
  ring

lemma pdl_kII_le (Cg Cz : ℝ) (hCg : 0 ≤ Cg) (hCz : 0 ≤ Cz)
    (hΓ : ∀ β : ℝ, 3 / 4 ≤ β → β ≤ 1 → ∀ u : ℝ,
      (1 + |u|) ^ 6 * ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Cg)
    (hζ : ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ Cz * (|t| + 2) ^ (156 / 1000 : ℝ))
    (T X β γ : ℝ) (hT : 0 ≤ T) (hX : 0 ≤ X) (hβ1 : 3 / 4 ≤ β) (hβ2 : β ≤ 1) (hγ : |γ| ≤ T)
    (u : ℝ) :
    kII X β γ u ≤ (2 * Cg * Cz * X ^ (1 / 2 : ℝ) * (T + 2) ^ (156 / 1000 : ℝ)) *
      (1 + u ^ 2)⁻¹ := by
  set w := 1 + |u| with hw
  have hw1 : 1 ≤ w := by linarith [abs_nonneg u]
  have hw0 : 0 < w := by linarith
  have h1 : ‖Complex.Gamma (((1 / 2 - β : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Cg / w ^ 6 := by
    rw [le_div_iff₀ (by positivity), mul_comm]; exact hΓ β hβ1 hβ2 u
  have h2 := pdl_molli_half X hX (γ + u)
  have h3 : ‖riemannZeta (1 / 2 + ((γ + u : ℝ) : ℂ) * I)‖ ≤
      Cz * ((T + 2) ^ (156 / 1000 : ℝ) * w) := by
    refine (hζ (γ + u)).trans (mul_le_mul_of_nonneg_left ?_ hCz)
    have hb : |γ + u| + 2 ≤ (T + 2) * w := by
      have := abs_add_le γ u
      rw [hw]; nlinarith [abs_nonneg u]
    calc (|γ + u| + 2) ^ (156 / 1000 : ℝ) ≤ ((T + 2) * w) ^ (156 / 1000 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hb (by norm_num)
      _ = (T + 2) ^ (156 / 1000 : ℝ) * w ^ (156 / 1000 : ℝ) :=
          Real.mul_rpow (by linarith) hw0.le
      _ ≤ (T + 2) ^ (156 / 1000 : ℝ) * w := by
          gcongr
          calc w ^ (156 / 1000 : ℝ) ≤ w ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
            _ = w := Real.rpow_one w
  have hk : kII X β γ u ≤ Cg / w ^ 6 *
      (2 * X ^ (1 / 2 : ℝ) * (Cz * ((T + 2) ^ (156 / 1000 : ℝ) * w))) := by
    unfold kII
    rw [norm_mul]
    exact mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity)
      (by positivity)
  have hw6 : w / w ^ 6 ≤ (1 + u ^ 2)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : 1 + u ^ 2 ≤ w ^ 2 := pdl_one_add_sq_le u
    have h36 : w ^ 3 ≤ w ^ 6 := pow_le_pow_right₀ hw1 (by norm_num)
    nlinarith
  calc kII X β γ u ≤ Cg / w ^ 6 *
        (2 * X ^ (1 / 2 : ℝ) * (Cz * ((T + 2) ^ (156 / 1000 : ℝ) * w))) := hk
    _ = (2 * Cg * Cz * X ^ (1 / 2 : ℝ) * (T + 2) ^ (156 / 1000 : ℝ)) * (w / w ^ 6) := by ring
    _ ≤ _ := by gcongr

theorem no_typeII : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, 9 / 11 ≤ α → α < 1 →
    ∀ ρ : ℂ, α ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T → ¬ IsTypeII α T ρ := by
  obtain ⟨Cg, hCg, hΓ⟩ := pdl_gamma_left_decay (3 / 4) (by norm_num) 6
  obtain ⟨Cz, hCz, hζ⟩ := zeta_half_bound
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * Real.pi * Cg * Cz + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; have := Real.pi_pos; nlinarith [mul_nonneg hCg.le hCz]
  refine ⟨max (K ^ 1000) 2, fun T hT α hα1 hα2 ρ hβ1 hβ2 hγ => ?_⟩
  have hT2 : 2 ≤ T := (le_max_right _ _).trans hT
  have hTK : K ^ 1000 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  obtain ⟨hX1, -⟩ := pdl_X_bounds hα1 hα2.le (by linarith : (1 : ℝ) ≤ T)
  unfold IsTypeII
  refine not_le.2 ?_
  set X := Xp α T with hX
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * Cg * Cz * X ^ (1 / 2 : ℝ) * (T + 2) ^ (156 / 1000 : ℝ) :=
    ⟨_, rfl⟩
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  have hβ0 : 3 / 4 ≤ ρ.re := le_trans (by norm_num) (le_trans hα1 hβ1)
  have hk : ∀ u : ℝ, kII X ρ.re ρ.im u ≤ M * (1 + u ^ 2)⁻¹ := by
    intro u
    have := pdl_kII_le Cg Cz hCg.le hCz hΓ hζ T X ρ.re ρ.im hT0.le hX0 hβ0 hβ2 hγ u
    rw [hM]
    exact this
  have hint : ∫ u : ℝ, kII X ρ.re ρ.im u ≤ M * Real.pi := by
    have := integral_mono_of_nonneg (μ := volume) (f := fun u => kII X ρ.re ρ.im u)
      (ae_of_all _ (fun u => by unfold kII; positivity))
      (integrable_inv_one_add_sq.const_mul M) (ae_of_all _ hk)
    rwa [integral_const_mul, integral_univ_inv_one_add_sq] at this
  have hXh : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hT156 : (T + 2) ^ (156 / 1000 : ℝ) ≤ 2 * T ^ (156 / 1000 : ℝ) := by
    calc (T + 2) ^ (156 / 1000 : ℝ) ≤ (2 * T) ^ (156 / 1000 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (156 / 1000 : ℝ) * T ^ (156 / 1000 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 ^ (1 : ℝ) * T ^ (156 / 1000 : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
            (by positivity)
      _ = 2 * T ^ (156 / 1000 : ℝ) := by rw [Real.rpow_one]
  have hKT : K ≤ T ^ (1 / 1000 : ℝ) := by
    have h : K = (K ^ (1000 : ℕ)) ^ (((1000 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by linarith) (by norm_num)).symm
    rw [h, show (1 / 1000 : ℝ) = ((1000 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_le_rpow (by positivity) hTK (by norm_num)
  have hTsplit : T ^ (157 / 1000 : ℝ) = T ^ (1 / 1000 : ℝ) * T ^ (156 / 1000 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  rw [pdl_Y_exp hα1 hT0, ← hX]
  refine lt_of_le_of_lt hint ?_
  have hT156p : 0 < T ^ (156 / 1000 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hP0 : 0 ≤ Cg * Cz := mul_nonneg hCg.le hCz
  have hpi := Real.pi_pos
  have e1 : M * Real.pi ≤ (4 * Real.pi * Cg * Cz) * (X ^ (1 / 2 : ℝ) * T ^ (156 / 1000 : ℝ)) := by
    rw [hM]
    have := mul_le_mul_of_nonneg_left hT156
      (by positivity : (0 : ℝ) ≤ 2 * Cg * Cz * X ^ (1 / 2 : ℝ) * Real.pi)
    nlinarith
  have e2 : (4 * Real.pi * Cg * Cz) * (X ^ (1 / 2 : ℝ) * T ^ (156 / 1000 : ℝ)) <
      K * (X ^ (1 / 2 : ℝ) * T ^ (156 / 1000 : ℝ)) := by
    apply mul_lt_mul_of_pos_right _ (by positivity); rw [hK]; linarith
  have e3 : K * (X ^ (1 / 2 : ℝ) * T ^ (156 / 1000 : ℝ)) ≤
      T ^ (1 / 1000 : ℝ) * (X ^ (1 / 2 : ℝ) * T ^ (156 / 1000 : ℝ)) :=
    mul_le_mul_of_nonneg_right hKT (by positivity)
  rw [hTsplit]
  nlinarith

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
alias no_typeII := GuthMaynard.CitedZeros.HR2.PartDL.no_typeII

/-! ## Step 2: Type I zeros -/

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex Finset
theorem N0_pos : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, 9 / 11 ≤ α → α ≤ 1 → 1 ≤ N0 α T := by
  refine ⟨1, fun T hT α h1 h2 => ?_⟩
  rw [N0, Nat.one_le_floor_iff]
  exact (pdl_X_bounds h1 h2 hT).1

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2

end GuthMaynard.CitedZeros.HR2
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartB
open GuthMaynard.CitedZeros.HR2
/-!
# Huxley (1.9), second range, Part B: `bookkeeping`

## On paper

Write `l = log T`, `λ = log l`, `x = 1 - α`, `w = log W = l/(3α-1)` (so `l/2 ≤ w ≤ 11 l/16`,
`log T^e = 3 x w`, `log Y = 3w/4`, `log X = (3(2α-1)/4 - 0.314(3α-1)) w ≥ l/72`). Take
`T ≥ exp(exp 200)`, so `l ≥ 10^50`, `λ ≥ 200`, `λ ≤ l/10^10`; the range `InR` gives
`x l ≥ 32400 λ` and `0 < x ≤ 2/11`. As in the first range: `N0 ≥ X/2 ≥ 1`, blocks have
`U_j = N0 2^j ≤ Y l² ≤ T`, so `j ≤ 2l` and `Jn ≤ 3l`.

`U* = W^{1/2} l⁵`, `j*` its block (`N0 2^{j*} ≤ U* < 2 N0 2^{j*}`), `k_j = |j - j*|`;
`ρ = 2^{-x/2}`, `h_j = (1-ρ) ρ^{j*-1-j}` for `j < j*` (else `0`), and
`V_j = 1/(10(1+k_j)²) + h_j/10`, so `∑ V_j ≤ π²/30 + 1/10 < 1/2`. Powers: `a_j = 2` for
`j ≥ j*`; for `j < j*` the least `b ≥ 3` with `U_j^b ≥ W^{17/16}` (cap `100`; `U^{100} ≥ W^{17/16}`
anyway, and `b ≤ 12` when `α > 19/20`, since then `log X ≥ 0.094 w`).
With `Q = 300 l` (bounding `1 + log(2^aU^a)` and `log(2^aU^aT)`), `R = 10(1+k)² ≤ Q²`:
* `a = 2`: as in the first range, `≤ T^e (D l^{43} φ(k) + D l^{42})`, `φ(k) = (1+k)^{24} 2^{-k}`
  (`12α - 8 ≥ 1` and `l⁵ 2^{k-1} ≥ 1`).
* `a = 3`, term 1 (the delicate one): with `m = j*-1-j`, `U 2^{m+1} ≤ U*` gives
  `U^{6x} ρ^{-6m} ≤ T^e l^{30x} ρ^m`; with `V^{-1} ≤ 10/h_j`, the term is
  `≤ T^e Q^{35} 10^6 ρ^m · l^{30x} (1-ρ)^{-6}`. Now `1 - ρ ≥ x/6` and
  `l^{30x} ≤ e^{30} l^8 x^7` (if `xλ ≤ 1`: `30xλ ≤ 30`, `log(1/x) ≤ λ`; if `xλ > 1`:
  `30xλ ≤ (60/11)λ`, `log(1/x) ≤ log λ ≤ λ/5`), so the term is `≤ T^e D l^{43} h_j`, and `∑ h_j ≤ 1`.
* `a ≥ 3`, term 2: `U^a ≥ W^{17/16}` gives `(U^a)^{4-6α} T ≤ T^e T^{-1/240}`, and the losses
  `Q^{3(4a²-1)+2} R^{6a} ≤ Q^{122000} ≤ T^{1/240}`.
* `a ≥ 4`, term 1: `U^a ≤ U · W^{17/16} ≤ W^{17/12}` gives `(U^a)^{2x} ≤ T^e T^{-x/12}`. If
  `α ≤ 19/20`, `T^{-x/12} ≤ T^{-1/240}` absorbs `Q^{122000}`; if `α > 19/20`, `a ≤ 12` and the
  losses are `≤ Q^{700} ≤ T^{x/12}` because `x l/12 ≥ 2700 λ`.
Summing: `≤ T^e D (2 ∑φ · l^{43} + 3l · l^{42} + l^{43})`.
-/
/-! ## Elementary facts -/
lemma pb2_log2 : 1 / 2 < Real.log 2 ∧ Real.log 2 < 1 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

lemma pb2_log300 : Real.log 300 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) (le_trans (by norm_num) h.le) 6]

lemma pb2_exp30 : Real.exp 30 ≤ 3 ^ 30 := by
  have : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 30

/-- `log y ≤ y / c` once `y ≥ (2c)²`. -/
lemma pb2_log_le_div {y c : ℝ} (hc : 0 < c) (hy : (2 * c) ^ 2 ≤ y) : Real.log y ≤ y / c := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have h1 : Real.log y ≤ y ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hy0.le (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : 2 * c ≤ Real.sqrt y := by
    rw [Real.le_sqrt (by positivity) hy0.le]; exact hy
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have h1' : Real.log y ≤ 2 * Real.sqrt y := by linarith
  rw [le_div_iff₀ hc]
  nlinarith [Real.sqrt_nonneg y, mul_le_mul_of_nonneg_right h1' hc.le]

/-! ## Parameters -/
/-- Logarithms of the parameters, with `w = log W = log T / (3α - 1)`. -/
lemma pb2_logs (α T : ℝ) (hα1 : 3 / 4 ≤ α) (hT : 0 < T) :
    Real.log (Wp α T) = Real.log T / (3 * α - 1) ∧
    Real.log (Xp α T) = (3 * (2 * α - 1) / 4 - 157 / 500 * (3 * α - 1)) *
      (Real.log T / (3 * α - 1)) ∧
    Real.log (Yp α T) = 3 / 4 * (Real.log T / (3 * α - 1)) ∧
    Real.log (T ^ ex α) = 3 * (1 - α) * (Real.log T / (3 * α - 1)) ∧
    (3 * α - 1) * (Real.log T / (3 * α - 1)) = Real.log T := by
  have h3 : 3 * α - 1 ≠ 0 := by linarith
  have h12 : 12 * α - 4 ≠ 0 := by linarith
  unfold Wp Xp Yp ex
  simp only [Real.log_rpow hT]
  rw [show 12 * α - 4 = 4 * (3 * α - 1) by ring]
  refine ⟨by ring, ?_, ?_, by ring, by field_simp⟩
  · field_simp
  · field_simp

lemma pb2_pos (α T : ℝ) (hT : 0 < T) :
    0 < Wp α T ∧ 0 < Xp α T ∧ 0 < Yp α T ∧ 0 < T ^ ex α :=
  ⟨Real.rpow_pos_of_pos hT _, Real.rpow_pos_of_pos hT _, Real.rpow_pos_of_pos hT _,
    Real.rpow_pos_of_pos hT _⟩

/-- Standing hypotheses. -/
structure pb2_Hyp (α T : ℝ) : Prop where
  h1 : 9 / 11 ≤ α
  h2 : α ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T
  hl : 10 ^ 50 ≤ Real.log T
  hll : 200 ≤ Real.log (Real.log T)
  hT : 1 < T

lemma pb2_Hyp.x {α T : ℝ} (H : pb2_Hyp α T) :
    32400 * Real.log (Real.log T) ≤ (1 - α) * Real.log T ∧ 0 < 1 - α ∧ 1 - α ≤ 2 / 11 ∧
      α ≤ 1 := by
  have hl0 : 0 < Real.log T := by linarith [H.hl]
  have h2 := H.h2
  have hll := H.hll
  have e : 32400 * Real.log (Real.log T) / Real.log T * Real.log T =
      32400 * Real.log (Real.log T) := div_mul_cancel₀ _ hl0.ne'
  have hd : 0 < 32400 * Real.log (Real.log T) / Real.log T := by positivity
  have hm := mul_le_mul_of_nonneg_right
    (show 32400 * Real.log (Real.log T) / Real.log T ≤ 1 - α by linarith) hl0.le
  rw [e] at hm
  exact ⟨hm, by linarith, by linarith [H.h1], by linarith⟩

lemma pb2_Hyp.llub {α T : ℝ} (H : pb2_Hyp α T) :
    Real.log (Real.log T) ≤ Real.log T / 10 ^ 10 :=
  pb2_log_le_div (by norm_num) (by have := H.hl; norm_num at this ⊢; linarith)

lemma pb2_Hyp.w {α T : ℝ} (H : pb2_Hyp α T) :
    Real.log T / 2 ≤ Real.log T / (3 * α - 1) ∧
      Real.log T / (3 * α - 1) ≤ 11 / 16 * Real.log T := by
  have h1 := H.h1
  have h2 := H.x.2.2.2
  have hl : 0 < Real.log T := by linarith [H.hl]
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma pb2_logX {α T : ℝ} (H : pb2_Hyp α T) :
    Real.log T / 72 ≤ Real.log (Xp α T) ∧
      Real.log (Xp α T) ≤ Real.log T / (3 * α - 1) / 2 := by
  have hT := H.hT
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T (by linarith [H.h1]) (by linarith)
  set w := Real.log T / (3 * α - 1)
  have hw := H.w
  have h1 := H.h1
  have h2 := H.x.2.2.2
  have hw0 : 0 ≤ w := by linarith [hw.1, H.hl]
  rw [lX, ← lw]
  constructor
  · linarith [mul_nonneg hw0 (by linarith : (0:ℝ) ≤ α - 9 / 11)]
  · linarith [mul_nonneg hw0 (by linarith : (0:ℝ) ≤ 1 - α)]

lemma pb2_N0 {α T : ℝ} (H : pb2_Hyp α T) :
    1 ≤ N0 α T ∧ Xp α T / 2 ≤ (N0 α T : ℝ) ∧ (N0 α T : ℝ) ≤ Xp α T := by
  have hT := H.hT
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith)
  have hlX := (pb2_logX H).1
  have h2 : 2 ≤ Xp α T := by
    rw [← Real.exp_log hX]
    have := pb2_log2
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith [H.hl])
  refine ⟨Nat.one_le_floor_iff _ |>.2 (by linarith), ?_, Nat.floor_le hX.le⟩
  have := Nat.lt_floor_add_one (Xp α T)
  unfold N0; linarith

lemma pb2_YT {α T : ℝ} (H : pb2_Hyp α T) :
    Xp α T ≤ Yp α T * Real.log T ^ 2 ∧ Yp α T * Real.log T ^ 2 ≤ T := by
  have hT := H.hT
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith)
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T (by linarith [H.h1]) (by linarith)
  have hlX := (pb2_logX H).2
  set w := Real.log T / (3 * α - 1)
  have hw := H.w
  have hll := H.llub
  have hll0 : 0 ≤ Real.log (Real.log T) := by linarith [H.hll]
  have hl1 : 1 ≤ Real.log T := by linarith [H.hl]
  have hw0 : 0 ≤ w := by linarith [hw.1, H.hl]
  constructor
  · rw [← Real.log_le_log_iff hX (by positivity), Real.log_mul hY.ne' (by positivity),
      Real.log_pow, lY]
    push_cast
    linarith
  · rw [← Real.log_le_log_iff (by positivity) (by linarith), Real.log_mul hY.ne' (by positivity),
      Real.log_pow, lY]
    push_cast
    linarith [H.hl]

/-- `U* = W^{1/2} (log T)^5`. -/
noncomputable def pb2_Ust (α T : ℝ) : ℝ := Wp α T ^ (1 / 2 : ℝ) * Real.log T ^ 5

/-- `j*`: `N0 2^{j*} ≤ U* < 2 N0 2^{j*}`. -/
noncomputable def pb2_jst (α T : ℝ) : ℕ := Nat.log 2 ⌊pb2_Ust α T / N0 α T⌋₊

lemma pb2_Ust_bounds {α T : ℝ} (H : pb2_Hyp α T) :
    (N0 α T : ℝ) ≤ pb2_Ust α T ∧ pb2_Ust α T ≤ T := by
  have hT := H.hT
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith)
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T (by linarith [H.h1]) (by linarith)
  have hlX := (pb2_logX H).2
  set w := Real.log T / (3 * α - 1)
  have hw := H.w
  have hll := H.llub
  have hll0 : 0 ≤ Real.log (Real.log T) := by linarith [H.hll]
  have hl1 : 1 ≤ Real.log T := by linarith [H.hl]
  have hw0 : 0 ≤ w := by linarith [hw.1, H.hl]
  have hU0 : 0 < pb2_Ust α T := by unfold pb2_Ust; positivity
  have lU : Real.log (pb2_Ust α T) = w / 2 + 5 * Real.log (Real.log T) := by
    unfold pb2_Ust
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hW, lW, Real.log_pow]
    push_cast; ring
  constructor
  · refine (pb2_N0 H).2.2.trans ?_
    rw [← Real.log_le_log_iff hX hU0, lU]
    linarith
  · rw [← Real.log_le_log_iff hU0 (by linarith), lU]
    linarith [H.hl]

lemma pb2_jst_spec {α T : ℝ} (H : pb2_Hyp α T) :
    (N0 α T : ℝ) * 2 ^ pb2_jst α T ≤ pb2_Ust α T ∧
      pb2_Ust α T < 2 * ((N0 α T : ℝ) * 2 ^ pb2_jst α T) := by
  obtain ⟨hN1, -, -⟩ := pb2_N0 H
  obtain ⟨hNU, -⟩ := pb2_Ust_bounds H
  have hN0 : (0 : ℝ) < N0 α T := by exact_mod_cast hN1
  set q := ⌊pb2_Ust α T / N0 α T⌋₊ with hq
  have hq1 : 1 ≤ q := Nat.one_le_floor_iff _ |>.2 (by rw [le_div_iff₀ hN0]; linarith)
  have hqne : q ≠ 0 := by omega
  have e1 : 2 ^ pb2_jst α T ≤ q := Nat.pow_log_le_self 2 hqne
  have e2 : q < 2 ^ (pb2_jst α T + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have e1' : ((2 ^ pb2_jst α T : ℕ) : ℝ) ≤ pb2_Ust α T / N0 α T :=
    (Nat.cast_le.2 e1).trans (Nat.floor_le (div_nonneg (by linarith) hN0.le))
  have e2' : pb2_Ust α T / N0 α T < ((2 ^ (pb2_jst α T + 1) : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (pb2_Ust α T / N0 α T)
    rw [← hq] at this
    have : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ (pb2_jst α T + 1) : ℕ) : ℝ) := by exact_mod_cast e2
    linarith
  push_cast at e1' e2'
  rw [le_div_iff₀ hN0] at e1'
  rw [div_lt_iff₀ hN0] at e2'
  constructor
  · linarith
  · rw [pow_succ] at e2'; linarith

lemma pb2_blk_le {α T : ℝ} (H : pb2_Hyp α T) (j : ℕ) (hj : j < Jn α T) :
    (N0 α T : ℝ) * 2 ^ j ≤ Yp α T * Real.log T ^ 2 := by
  obtain ⟨hN1, -, -⟩ := pb2_N0 H
  obtain ⟨hXY, -⟩ := pb2_YT H
  have hZ : N0 α T ≤ Ztop α T := Nat.floor_mono hXY
  have hq : Ztop α T / N0 α T ≠ 0 := by
    have : 1 ≤ Ztop α T / N0 α T := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hZ)
    omega
  have hJ : Jn α T = Nat.log 2 (Ztop α T / N0 α T) + 1 := rfl
  have hj' : j ≤ Nat.log 2 (Ztop α T / N0 α T) := by omega
  have e1 : 2 ^ j ≤ Ztop α T / N0 α T :=
    (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 hq)
  have e2 : N0 α T * 2 ^ j ≤ Ztop α T :=
    (Nat.mul_le_mul_left _ e1).trans (Nat.mul_div_le _ _)
  have e3 : ((N0 α T * 2 ^ j : ℕ) : ℝ) ≤ Ztop α T := by exact_mod_cast e2
  push_cast at e3
  refine e3.trans (Nat.floor_le ?_)
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith [H.hT])
  positivity

lemma pb2_two_pow {T : ℝ} (hT : 0 < T) (n : ℕ) (h : (2 : ℝ) ^ n ≤ T) :
    (n : ℝ) ≤ 2 * Real.log T := by
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at this
  have h2 := pb2_log2
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma pb2_idx {α T : ℝ} (H : pb2_Hyp α T) :
    (Jn α T : ℝ) ≤ 3 * Real.log T ∧ (pb2_jst α T : ℝ) ≤ 2 * Real.log T ∧
      ∀ j < Jn α T, (j : ℝ) ≤ 2 * Real.log T := by
  have hT := H.hT
  obtain ⟨hN1, -, -⟩ := pb2_N0 H
  have hN : (1 : ℝ) ≤ N0 α T := by exact_mod_cast hN1
  have hYT := (pb2_YT H).2
  have hj : ∀ j < Jn α T, (j : ℝ) ≤ 2 * Real.log T := by
    intro j hj
    apply pb2_two_pow (by linarith) j
    have := pb2_blk_le H j hj
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]
  refine ⟨?_, ?_, hj⟩
  · have hJ : Jn α T - 1 < Jn α T := by unfold Jn; omega
    have := hj _ hJ
    have e : ((Jn α T - 1 : ℕ) : ℝ) = (Jn α T : ℝ) - 1 := by
      rw [Nat.cast_sub (by unfold Jn; omega)]; simp
    rw [e] at this
    linarith [H.hl]
  · apply pb2_two_pow (by linarith)
    have := (pb2_jst_spec H).1
    have := (pb2_Ust_bounds H).2
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (pb2_jst α T)]

/-- The cap: `U^{100} ≥ W^{17/16}` for every block. -/
lemma pb2_cap {α T : ℝ} (H : pb2_Hyp α T) (j : ℕ) :
    Wp α T ^ (17 / 16 : ℝ) ≤ ((N0 α T : ℝ) * 2 ^ j) ^ 100 := by
  have hT := H.hT
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith)
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T (by linarith [H.h1]) (by linarith)
  obtain ⟨hN1, hNX, -⟩ := pb2_N0 H
  have hN : (1 : ℝ) ≤ N0 α T := by exact_mod_cast hN1
  have hU : Xp α T / 2 ≤ (N0 α T : ℝ) * 2 ^ j :=
    hNX.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num)))
  have hlU : Real.log (Xp α T) - Real.log 2 ≤ Real.log ((N0 α T : ℝ) * 2 ^ j) := by
    have := Real.log_le_log (by positivity) hU
    rwa [Real.log_div hX.ne' (by norm_num)] at this
  have hw := H.w
  have hlX := (pb2_logX H).1
  have h2 := pb2_log2
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hW, lW, Real.log_pow]
  push_cast
  linarith [H.hl]

/-- For `α > 19/20`, already `U^{12} ≥ W^{17/16}`. -/
lemma pb2_twelve {α T : ℝ} (H : pb2_Hyp α T) (hα : 19 / 20 < α) (j : ℕ) :
    Wp α T ^ (17 / 16 : ℝ) ≤ ((N0 α T : ℝ) * 2 ^ j) ^ 12 := by
  have hT := H.hT
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T (by linarith)
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T (by linarith [H.h1]) (by linarith)
  obtain ⟨hN1, hNX, -⟩ := pb2_N0 H
  have hN : (1 : ℝ) ≤ N0 α T := by exact_mod_cast hN1
  have hU : Xp α T / 2 ≤ (N0 α T : ℝ) * 2 ^ j :=
    hNX.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num)))
  have hlU : Real.log (Xp α T) - Real.log 2 ≤ Real.log ((N0 α T : ℝ) * 2 ^ j) := by
    have := Real.log_le_log (by positivity) hU
    rwa [Real.log_div hX.ne' (by norm_num)] at this
  set w := Real.log T / (3 * α - 1)
  have hw := H.w
  have hw0 : 0 ≤ w := by linarith [hw.1, H.hl]
  have h2 := pb2_log2
  have hX' : 47 / 500 * w ≤ Real.log (Xp α T) := by
    rw [lX]; linarith [mul_nonneg hw0 (by linarith : (0:ℝ) ≤ α - 19 / 20)]
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hW, lW, Real.log_pow]
  push_cast
  linarith [H.hl]

/-! ## The decay parameter `ρ = 2^{-(1-α)/2}` -/
/-- `ρ = 2^{-(1-α)/2}`. -/
noncomputable def pb2_rho (α : ℝ) : ℝ := (2 : ℝ) ^ (-(1 - α) / 2)

lemma pb2_rho_pos {α T : ℝ} (H : pb2_Hyp α T) : 0 < pb2_rho α ∧ pb2_rho α < 1 := by
  have hx := H.x.2.1
  exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

lemma pb2_rho_lb (α : ℝ) (h0 : 0 ≤ 1 - α) (h1 : 1 - α ≤ 1) : (1 - α) / 6 ≤ 1 - pb2_rho α := by
  unfold pb2_rho
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  set y := Real.log 2 * ((1 - α) / 2) with hy
  have e : Real.log 2 * (-(1 - α) / 2) = -y := by rw [hy]; ring
  rw [e]
  have h2 := pb2_log2
  have hy0 : (1 - α) / 4 ≤ y := by rw [hy]; nlinarith
  have hexp : Real.exp (-y) * (1 + y) ≤ 1 := by
    have := Real.add_one_le_exp y
    have hp := Real.exp_pos (-y)
    calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y :=
          mul_le_mul_of_nonneg_left (by linarith) hp.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-y)
  by_cases hρ : 2 / 3 ≤ Real.exp (-y)
  · nlinarith
  · linarith

/-- `l^{30x} ≤ e^{30} l^8 x^7` for `32400 log l ≤ x l`, `x ≤ 2/11`. -/
lemma pb2_Ecore (l x : ℝ) (hl : 10 ^ 50 ≤ l) (hll : 200 ≤ Real.log l)
    (hx : 32400 * Real.log l ≤ x * l) (hx2 : x ≤ 2 / 11) :
    l ^ (30 * x) ≤ Real.exp 30 * l ^ 8 * x ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hx0 : 0 < x := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hl0,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow, Real.log_pow]
  push_cast
  have hxl : 0 ≤ Real.log x + Real.log l := by
    rw [← Real.log_mul hx0.ne' hl0.ne']; apply Real.log_nonneg; nlinarith
  by_cases hc : x * Real.log l ≤ 1
  · nlinarith
  · push Not at hc
    have h1 : 0 ≤ Real.log x + Real.log (Real.log l) := by
      rw [← Real.log_mul hx0.ne' (by positivity)]; exact Real.log_nonneg hc.le
    have h2 : Real.log (Real.log l) ≤ Real.log l / 5 :=
      pb2_log_le_div (by norm_num) (by norm_num; linarith)
    nlinarith [mul_le_mul_of_nonneg_right hx2 (by linarith : (0:ℝ) ≤ Real.log l)]

lemma pb2_E {α T : ℝ} (H : pb2_Hyp α T) :
    Real.log T ^ (30 * (1 - α)) * ((1 - pb2_rho α)⁻¹) ^ 6 ≤
      6 ^ 7 * Real.exp 30 * Real.log T ^ 8 * (1 - pb2_rho α) := by
  obtain ⟨hx, hx0, hx2, hα1⟩ := H.x
  have hr := pb2_rho_lb α hx0.le (by linarith)
  set r := 1 - pb2_rho α with hrdef
  have hr0 : 0 < r := by linarith
  have hc := pb2_Ecore (Real.log T) (1 - α) H.hl H.hll (by linarith) hx2
  have h7 : (1 - α) ^ 7 ≤ 6 ^ 7 * r ^ 7 := by
    calc (1 - α) ^ 7 = 6 ^ 7 * ((1 - α) / 6) ^ 7 := by ring
      _ ≤ 6 ^ 7 * r ^ 7 := by
          gcongr
  have hl0 : 0 < Real.log T := by linarith [H.hl]
  calc Real.log T ^ (30 * (1 - α)) * (r⁻¹) ^ 6
      ≤ (6 ^ 7 * Real.exp 30 * Real.log T ^ 8 * r ^ 7) * (r⁻¹) ^ 6 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc _ ≤ Real.exp 30 * Real.log T ^ 8 * (1 - α) ^ 7 := hc
          _ ≤ Real.exp 30 * Real.log T ^ 8 * (6 ^ 7 * r ^ 7) := by gcongr
          _ = _ := by ring
    _ = _ := by field_simp

/-! ## The single-term estimates -/
/-- `a = 2`, first term. -/
lemma pb2_k1 (α T U : ℝ) (hα1 : 3 / 4 ≤ α) (hα2 : α ≤ 1) (hT : 1 < T)
    (hl : 1 ≤ Real.log T) (hU : 0 < U) (hUY : U ≤ Yp α T * Real.log T ^ 2) :
    (U ^ 2) ^ (2 * (1 - α)) ≤ T ^ ex α * Real.log T ^ 2 := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T hT0
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T hα1 hT0
  set w := Real.log T / (3 * α - 1)
  have hl0 : 0 < Real.log T := by linarith
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hl
  have hu : Real.log U ≤ 3 / 4 * w + 2 * Real.log (Real.log T) := by
    have := Real.log_le_log hU hUY
    rwa [Real.log_mul hY.ne' (by positivity), Real.log_pow, lY] at this
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_mul hE.ne' (by positivity), Real.log_pow, Real.log_pow, lE]
  push_cast
  linarith [mul_le_mul_of_nonneg_left hu (by linarith : (0:ℝ) ≤ 1 - α),
    mul_nonneg (by linarith : (0:ℝ) ≤ α - 3 / 4) hll]

/-- `a = 2`, second term (critical): `U ≥ U* 2^k / 2`. -/
lemma pb2_k2 (α T U : ℝ) (k : ℕ) (hα1 : 3 / 4 ≤ α) (hα2 : α ≤ 1) (hT : 1 < T)
    (hl : 1 ≤ Real.log T) (hll1 : 1 ≤ Real.log (Real.log T)) (hU : 0 < U)
    (hUs : Wp α T ^ (1 / 2 : ℝ) * Real.log T ^ 5 * 2 ^ k ≤ 2 * U) :
    (U ^ 2) ^ (4 - 6 * α) * T ≤ 4 * T ^ ex α * (Real.log T ^ 5)⁻¹ * (1 / 2) ^ k := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T hT0
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T hα1 hT0
  set w := Real.log T / (3 * α - 1)
  have hl0 : 0 < Real.log T := by linarith
  set ll := Real.log (Real.log T) with hlldef
  obtain ⟨h2a, h2b⟩ := pb2_log2
  have hu : w / 2 + 5 * ll + k * Real.log 2 ≤ Real.log 2 + Real.log U := by
    have := Real.log_le_log (by positivity) hUs
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hW, lW, Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hU.ne'] at this
    push_cast at this; linarith
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) hT0.ne', Real.log_rpow (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hE.ne', Real.log_inv, Real.log_pow, Real.log_pow, lE,
    one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  set s := 5 * ll + ((k : ℝ) - 1) * Real.log 2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : 0 ≤ s := by linarith [mul_nonneg hk0 (by linarith : (0:ℝ) ≤ Real.log 2)]
  have key : (8 - 12 * α) * s ≤ Real.log 2 - s := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ α - 3 / 4) hs]
  have hu' : (4 - 6 * α) * (2 * Real.log U) ≤ (4 - 6 * α) * (w + 2 * s) :=
    mul_le_mul_of_nonpos_left (by linarith) (by linarith)
  linarith

/-- `a = 3`, first term (critical): `U 2^{m+1} ≤ U*` gives `U^{6x} ρ^{-6m} ≤ T^e l^{30x} ρ^m`. -/
lemma pb2_k3 (α T U : ℝ) (m : ℕ) (hα1 : 3 / 4 ≤ α) (hα2 : α ≤ 1) (hT : 1 < T)
    (hl : 1 ≤ Real.log T) (hU : 0 < U) (hUs : U * 2 ^ (m + 1) ≤ pb2_Ust α T) :
    (U ^ 3) ^ (2 * (1 - α)) * ((pb2_rho α ^ m)⁻¹) ^ 6 ≤
      T ^ ex α * Real.log T ^ (30 * (1 - α)) * pb2_rho α ^ m := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T hT0
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T hα1 hT0
  set w := Real.log T / (3 * α - 1)
  have hl0 : 0 < Real.log T := by linarith
  set ll := Real.log (Real.log T) with hlldef
  obtain ⟨h2a, h2b⟩ := pb2_log2
  have hρ : 0 < pb2_rho α := Real.rpow_pos_of_pos (by norm_num) _
  have hρm : 0 < pb2_rho α ^ m := pow_pos hρ m
  have lρ : Real.log (pb2_rho α) = (-(1 - α) / 2) * Real.log 2 := Real.log_rpow (by norm_num) _
  have hu : Real.log U + ((m : ℝ) + 1) * Real.log 2 ≤ w / 2 + 5 * ll := by
    have := Real.log_le_log (by positivity) hUs
    unfold pb2_Ust at this
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hW, lW, Real.log_pow, Real.log_pow] at this
    push_cast at this; linarith
  have L1 : Real.log ((U ^ 3) ^ (2 * (1 - α)) * ((pb2_rho α ^ m)⁻¹) ^ 6) =
      2 * (1 - α) * (3 * Real.log U) + 6 * (-((m : ℝ) * Real.log (pb2_rho α))) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity), Real.log_pow,
      Real.log_pow, Real.log_inv, Real.log_pow]
    push_cast; ring
  have L2 : Real.log (T ^ ex α * Real.log T ^ (30 * (1 - α)) * pb2_rho α ^ m) =
      3 * (1 - α) * w + 30 * (1 - α) * ll + (m : ℝ) * Real.log (pb2_rho α) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      lE, Real.log_rpow hl0, Real.log_pow]
  rw [← Real.log_le_log_iff (by positivity) (by positivity), L1, L2, lρ]
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hx : 0 ≤ 1 - α := by linarith
  linarith [mul_le_mul_of_nonneg_left hu (by linarith : (0:ℝ) ≤ 6 * (1 - α)),
    mul_nonneg (mul_nonneg hx hm0) (by linarith : (0:ℝ) ≤ Real.log 2),
    mul_nonneg hx (by linarith : (0:ℝ) ≤ Real.log 2)]

/-- `a ≥ 4`, first term: `U³ ≤ W^{17/16}`, `U^{n-1} ≤ W^{17/16}` give `(U^n)^{2x} ≤ T^e T^{-x/12}`. -/
lemma pb2_k4 (α T U : ℝ) (n : ℕ) (hα1 : 3 / 4 ≤ α) (hα2 : α ≤ 1) (hT : 1 < T)
    (hU : 1 ≤ U) (hn : 1 ≤ n)
    (h3 : U ^ 3 ≤ Wp α T ^ (17 / 16 : ℝ)) (hn1 : U ^ (n - 1) ≤ Wp α T ^ (17 / 16 : ℝ)) :
    (U ^ n) ^ (2 * (1 - α)) ≤ T ^ ex α * (T ^ ((1 - α) / 12))⁻¹ := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T hT0
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T hα1 hT0
  set w := Real.log T / (3 * α - 1)
  have hl0 : 0 < Real.log T := Real.log_pos hT
  have hw0 : 0 < w := div_pos hl0 (by linarith)
  have hU0 : 0 < U := by linarith
  have hlU : 0 ≤ Real.log U := Real.log_nonneg hU
  have e3 : 3 * Real.log U ≤ 17 / 16 * w := by
    have := Real.log_le_log (by positivity) h3
    rwa [Real.log_pow, Real.log_rpow hW, lW] at this
  have en : ((n : ℝ) - 1) * Real.log U ≤ 17 / 16 * w := by
    have := Real.log_le_log (by positivity) hn1
    rwa [Real.log_pow, Real.log_rpow hW, lW, Nat.cast_sub hn, Nat.cast_one] at this
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_pow,
    Real.log_mul hE.ne' (by positivity), Real.log_inv, lE, Real.log_rpow hT0]
  have hm : (n : ℝ) * Real.log U ≤ 17 / 12 * w := by linarith
  rw [← lw]
  linarith [mul_le_mul_of_nonneg_left hm (by linarith : (0:ℝ) ≤ 2 * (1 - α)),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) (by linarith : (0:ℝ) ≤ 1 - α)) hw0.le]

/-- Power saving, second term, `a ≥ 3`: `U^a ≥ W^{17/16}`. -/
lemma pb2_k5 (α T M : ℝ) (hα1 : 3 / 4 ≤ α) (hT : 1 < T)
    (hM : Wp α T ^ (17 / 16 : ℝ) ≤ M) :
    M ^ (4 - 6 * α) * T ≤ T ^ ex α * (T ^ (1 / 240 : ℝ))⁻¹ := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hW, hX, hY, hE⟩ := pb2_pos α T hT0
  obtain ⟨lW, lX, lY, lE, lw⟩ := pb2_logs α T hα1 hT0
  set w := Real.log T / (3 * α - 1)
  have hl0 : 0 < Real.log T := Real.log_pos hT
  have hw0 : 0 < w := div_pos hl0 (by linarith)
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have em : 17 / 16 * w ≤ Real.log M := by
    have := Real.log_le_log (by positivity) hM
    rwa [Real.log_rpow hW, lW] at this
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) hT0.ne', Real.log_rpow hM0,
    Real.log_mul hE.ne' (by positivity), Real.log_inv, lE, Real.log_rpow hT0]
  rw [← lw]
  linarith [mul_le_mul_of_nonpos_left em (by linarith : (4 - 6 * α : ℝ) ≤ 0),
    mul_nonneg (by linarith : (0:ℝ) ≤ α - 3 / 4) hw0.le]

/-! ## Logarithmic losses -/
/-- Generic form of `Bfun`, with logarithms bounded by `Q` and `1/V` by `R₁`, `R₂`. -/
lemma pb2_bfun_le (α T : ℝ) (a : ℕ) (U V Q R1 R2 : ℝ) (hU : 1 ≤ U) (hV : 0 < V) (hT : 1 ≤ T)
    (hQ : 1 + Real.log (2 ^ a * U ^ a) ≤ Q) (hQ' : Real.log (2 ^ a * U ^ a * T) ≤ Q)
    (hR1 : V⁻¹ ≤ R1) (hR2 : V⁻¹ ≤ R2) :
    Bfun α T a U V ≤ (U ^ a) ^ (2 * (1 - α)) * Q ^ (4 * a ^ 2 - 1) * R1 ^ (2 * a) +
      (U ^ a) ^ (4 - 6 * α) * T * Q ^ (3 * (4 * a ^ 2 - 1)) * R2 ^ (6 * a) * Q ^ 2 := by
  have hU0 : 0 ≤ U := by linarith
  have h2U : 1 ≤ 2 ^ a * U ^ a := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ hU)
  have hL0 : 0 ≤ 1 + Real.log (2 ^ a * U ^ a) := by linarith [Real.log_nonneg h2U]
  have hL1 : 0 ≤ Real.log (2 ^ a * U ^ a * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le h2U hT)
  have e1 : U ^ (2 * (a : ℝ) * (1 - α)) = (U ^ a) ^ (2 * (1 - α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; ring_nf
  have e2 : U ^ ((a : ℝ) * (4 - 6 * α)) = (U ^ a) ^ (4 - 6 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]
  have e3 : V ^ (-(2 * (a : ℝ))) = (V⁻¹) ^ (2 * a) := by
    rw [Real.rpow_neg hV.le, show (2 * (a : ℝ)) = ((2 * a : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, inv_pow]
  have e4 : V ^ (-(6 * (a : ℝ))) = (V⁻¹) ^ (6 * a) := by
    rw [Real.rpow_neg hV.le, show (6 * (a : ℝ)) = ((6 * a : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, inv_pow]
  have hQ0 : 0 ≤ Q := by linarith
  have hVi : 0 ≤ V⁻¹ := inv_nonneg.2 hV.le
  have hR10 : 0 ≤ R1 := hVi.trans hR1
  have hR20 : 0 ≤ R2 := hVi.trans hR2
  have hUa : 0 ≤ (U ^ a) ^ (4 - 6 * α) := Real.rpow_nonneg (by positivity) _
  unfold Bfun
  rw [e1, e2, e3, e4]
  gcongr

/-- Log bounds: `Q = 300 log T`. -/
lemma pb2_Q (T U : ℝ) (a : ℕ) (ha : a ≤ 100) (hU : 1 ≤ U) (hUT : U ≤ T) (hl : 1 ≤ Real.log T) :
    1 + Real.log (2 ^ a * U ^ a) ≤ 300 * Real.log T ∧
      Real.log (2 ^ a * U ^ a * T) ≤ 300 * Real.log T := by
  have hT : 0 < T := by linarith
  have hlu : Real.log U ≤ Real.log T := Real.log_le_log (by linarith) hUT
  have hlu0 : 0 ≤ Real.log U := Real.log_nonneg hU
  have h2 := pb2_log2
  have e : Real.log (2 ^ a * U ^ a) = a * (Real.log 2 + Real.log U) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; ring
  have ha' : (a : ℝ) ≤ 100 := by exact_mod_cast ha
  have hb : Real.log (2 ^ a * U ^ a) ≤ 200 * Real.log T := by
    rw [e]
    have : Real.log 2 + Real.log U ≤ 2 * Real.log T := by linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) a]
  constructor
  · linarith
  · rw [Real.log_mul (by positivity) hT.ne']
    linarith

/-- The powers of `Q` and `R` in the blocks with a power saving. -/
lemma pb2_save_exp (n : ℕ) (hn : n ≤ 100) (Q R : ℝ) (hQ : 1 ≤ Q) (hR0 : 0 ≤ R) (hR : R ≤ Q ^ 2) :
    Q ^ (4 * n ^ 2 - 1) * R ^ (2 * n) ≤ Q ^ 122000 ∧
      Q ^ (3 * (4 * n ^ 2 - 1)) * R ^ (6 * n) * Q ^ 2 ≤ Q ^ 122000 := by
  have hn2 : n ^ 2 ≤ 10000 := by
    calc n ^ 2 ≤ 100 ^ 2 := Nat.pow_le_pow_left hn 2
      _ = 10000 := by norm_num
  have hR1 : R ^ (2 * n) ≤ Q ^ (4 * n) := by
    calc R ^ (2 * n) ≤ (Q ^ 2) ^ (2 * n) := pow_le_pow_left₀ hR0 hR _
      _ = Q ^ (4 * n) := by rw [← pow_mul]; ring_nf
  have hR2 : R ^ (6 * n) ≤ Q ^ (12 * n) := by
    calc R ^ (6 * n) ≤ (Q ^ 2) ^ (6 * n) := pow_le_pow_left₀ hR0 hR _
      _ = Q ^ (12 * n) := by rw [← pow_mul]; ring_nf
  constructor
  · calc Q ^ (4 * n ^ 2 - 1) * R ^ (2 * n) ≤ Q ^ (4 * n ^ 2 - 1) * Q ^ (4 * n) :=
          mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ = Q ^ (4 * n ^ 2 - 1 + 4 * n) := by rw [pow_add]
      _ ≤ Q ^ 122000 := pow_le_pow_right₀ hQ (by omega)
  · calc Q ^ (3 * (4 * n ^ 2 - 1)) * R ^ (6 * n) * Q ^ 2
          ≤ Q ^ (3 * (4 * n ^ 2 - 1)) * Q ^ (12 * n) * Q ^ 2 := by gcongr
      _ = Q ^ (3 * (4 * n ^ 2 - 1) + 12 * n + 2) := by rw [pow_add, pow_add]
      _ ≤ Q ^ 122000 := pow_le_pow_right₀ hQ (by omega)

lemma pb2_save_exp12 (n : ℕ) (hn : n ≤ 12) (Q R : ℝ) (hQ : 1 ≤ Q) (hR0 : 0 ≤ R)
    (hR : R ≤ Q ^ 2) : Q ^ (4 * n ^ 2 - 1) * R ^ (2 * n) ≤ Q ^ 700 := by
  have hn2 : n ^ 2 ≤ 144 := by
    calc n ^ 2 ≤ 12 ^ 2 := Nat.pow_le_pow_left hn 2
      _ = 144 := by norm_num
  have hR1 : R ^ (2 * n) ≤ Q ^ (4 * n) := by
    calc R ^ (2 * n) ≤ (Q ^ 2) ^ (2 * n) := pow_le_pow_left₀ hR0 hR _
      _ = Q ^ (4 * n) := by rw [← pow_mul]; ring_nf
  calc Q ^ (4 * n ^ 2 - 1) * R ^ (2 * n) ≤ Q ^ (4 * n ^ 2 - 1) * Q ^ (4 * n) :=
        mul_le_mul_of_nonneg_left hR1 (by positivity)
    _ = Q ^ (4 * n ^ 2 - 1 + 4 * n) := by rw [pow_add]
    _ ≤ Q ^ 700 := pow_le_pow_right₀ hQ (by omega)

lemma pb2_absorb {α T : ℝ} (H : pb2_Hyp α T) :
    (300 * Real.log T) ^ 122000 ≤ T ^ (1 / 240 : ℝ) := by
  have hT := H.hT
  have hl0 : 0 < Real.log T := by linarith [H.hl]
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) hl0.ne', Real.log_rpow (by linarith)]
  have := pb2_log300
  have := H.llub
  push_cast
  linarith [H.hl]

lemma pb2_absorb2 {α T : ℝ} (H : pb2_Hyp α T) :
    (300 * Real.log T) ^ 700 ≤ T ^ ((1 - α) / 12) := by
  have hT := H.hT
  have hl0 : 0 < Real.log T := by linarith [H.hl]
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) hl0.ne', Real.log_rpow (by linarith)]
  have := pb2_log300
  have := H.x.1
  have := H.hll
  push_cast
  linarith

lemma pb2_save_term {E X P S : ℝ} (hE : 0 ≤ E) (hS : 0 < S) (hX0 : 0 ≤ X) (hX : X ≤ E * S⁻¹)
    (hP0 : 0 ≤ P) (hP : P ≤ S) : X * P ≤ E := by
  calc X * P ≤ (E * S⁻¹) * S := mul_le_mul hX hP hP0 (by positivity)
    _ = E := by field_simp

lemma pb2_R_le {T : ℝ} (k : ℕ) (hl : 1 ≤ Real.log T) (hk : (k : ℝ) + 1 ≤ 5 * Real.log T) :
    0 ≤ 10 * (1 + (k : ℝ)) ^ 2 ∧ 10 * (1 + (k : ℝ)) ^ 2 ≤ (300 * Real.log T) ^ 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨by positivity, ?_⟩
  nlinarith

lemma pb2_term2_save {α T : ℝ} (H : pb2_Hyp α T) (n : ℕ) (hn : n ≤ 100) (U R : ℝ) (hU : 1 ≤ U)
    (hM : Wp α T ^ (17 / 16 : ℝ) ≤ U ^ n) (hR0 : 0 ≤ R) (hR : R ≤ (300 * Real.log T) ^ 2) :
    (U ^ n) ^ (4 - 6 * α) * T * (300 * Real.log T) ^ (3 * (4 * n ^ 2 - 1)) *
      R ^ (6 * n) * (300 * Real.log T) ^ 2 ≤ T ^ ex α := by
  have hT := H.hT
  have hl : 1 ≤ Real.log T := by linarith [H.hl]
  have hU0 : 0 < U := by linarith
  have hP := (pb2_save_exp n hn (300 * Real.log T) _ (by linarith) hR0 hR).2
  have hX := pb2_k5 α T (U ^ n) (by linarith [H.h1]) hT hM
  have hT0 : 0 < T := by linarith
  calc _ = ((U ^ n) ^ (4 - 6 * α) * T) * ((300 * Real.log T) ^ (3 * (4 * n ^ 2 - 1)) *
        R ^ (6 * n) * (300 * Real.log T) ^ 2) := by ring
    _ ≤ T ^ ex α := pb2_save_term (Real.rpow_pos_of_pos hT0 _).le
        (Real.rpow_pos_of_pos hT0 _) (by positivity) hX (by positivity) (hP.trans (pb2_absorb H))

/-! ## Sums over blocks -/
def pb2_k (m j : ℕ) : ℕ := if m ≤ j then j - m else m - j

lemma pb2_sum_k_le (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k) (hs : Summable f) (n m : ℕ) :
    ∑ j ∈ Finset.range n, f (pb2_k m j) ≤ 2 * ∑' k, f k := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun j => m ≤ j)]
  have h1 : ∑ j ∈ (Finset.range n).filter (fun j => m ≤ j), f (pb2_k m j) ≤ ∑' k, f k := by
    have : ∑ j ∈ (Finset.range n).filter (fun j => m ≤ j), f (pb2_k m j) =
        ∑ k ∈ ((Finset.range n).filter (fun j => m ≤ j)).image (fun j => j - m), f k := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_filter] at hj
        simp [pb2_k, hj.2]
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
        simp only at hxy
        omega
    rw [this]
    exact hs.sum_le_tsum _ (fun k _ => hf0 k)
  have h2 : ∑ j ∈ (Finset.range n).filter (fun j => ¬ m ≤ j), f (pb2_k m j) ≤ ∑' k, f k := by
    have : ∑ j ∈ (Finset.range n).filter (fun j => ¬ m ≤ j), f (pb2_k m j) =
        ∑ k ∈ ((Finset.range n).filter (fun j => ¬ m ≤ j)).image (fun j => m - j), f k := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_filter] at hj
        simp [pb2_k, hj.2]
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
        simp only at hxy
        omega
    rw [this]
    exact hs.sum_le_tsum _ (fun k _ => hf0 k)
  linarith

/-- The weight `φ(k) = (k+1)^{24} 2^{-k}`. -/
noncomputable def pb2_phi (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 24 * (1 / 2 : ℝ) ^ k

lemma pb2_phi_nonneg (k : ℕ) : 0 ≤ pb2_phi k := by unfold pb2_phi; positivity

lemma pb2_phi_summable : Summable pb2_phi := by
  have h : Summable (fun n : ℕ => ((n : ℝ)) ^ 24 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 24 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  have h2 := h1.mul_left 2
  refine h2.congr fun n => ?_
  unfold pb2_phi
  push_cast
  ring

lemma pb2_inv_sq_tsum : ∑' k : ℕ, 1 / (10 * (1 + (k : ℝ)) ^ 2) = Real.pi ^ 2 / 60 := by
  have h := hasSum_zeta_two
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h1
  norm_num at h1
  have h2 := h1.mul_left (1 / 10)
  have : (fun k : ℕ => 1 / (10 * (1 + (k : ℝ)) ^ 2)) =
      fun k : ℕ => 1 / 10 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    funext k; field_simp; ring
  rw [this, h2.tsum_eq]; ring

lemma pb2_inv_sq_summable : Summable (fun k : ℕ => 1 / (10 * (1 + (k : ℝ)) ^ 2)) := by
  by_contra h
  have := tsum_eq_zero_of_not_summable h
  rw [pb2_inv_sq_tsum] at this
  have : 0 < Real.pi ^ 2 / 60 := by positivity
  linarith

lemma pb2_inv_sq_sum (n m : ℕ) :
    ∑ j ∈ Finset.range n, 1 / (10 * (1 + (pb2_k m j : ℝ)) ^ 2) ≤ 34 / 100 := by
  have h := pb2_sum_k_le (fun k : ℕ => 1 / (10 * (1 + (k : ℝ)) ^ 2)) (fun k => by positivity)
    pb2_inv_sq_summable n m
  rw [pb2_inv_sq_tsum] at h
  have hpi := Real.pi_lt_d2
  have : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith [Real.pi_pos]
  linarith

lemma pb2_geom (ρ : ℝ) (h0 : 0 ≤ ρ) (N : ℕ) : ∑ i ∈ Finset.range N, (1 - ρ) * ρ ^ i ≤ 1 := by
  rw [← Finset.mul_sum]
  have := geom_sum_mul ρ N
  have hp : 0 ≤ ρ ^ N := pow_nonneg h0 N
  nlinarith

lemma pb2_h_sum (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (js n : ℕ) :
    ∑ j ∈ Finset.range n, (if j < js then (1 - ρ) * ρ ^ (js - 1 - j) else 0) ≤ 1 := by
  set g : ℕ → ℝ := fun j => if j < js then (1 - ρ) * ρ ^ (js - 1 - j) else 0 with hg
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    simp only [hg]
    split_ifs
    · exact mul_nonneg (by linarith) (pow_nonneg h0 _)
    · exact le_rfl
  calc ∑ j ∈ Finset.range n, g j ≤ ∑ j ∈ Finset.range (js + n), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun j _ _ => hg0 j)
    _ = ∑ j ∈ Finset.range js, g j + ∑ i ∈ Finset.range n, g (js + i) := Finset.sum_range_add _ _ _
    _ = ∑ j ∈ Finset.range js, (1 - ρ) * ρ ^ (js - 1 - j) + 0 := by
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          simp [hg, Finset.mem_range.1 hj]
        · apply Finset.sum_eq_zero
          intro i _
          simp [hg]
    _ = ∑ j ∈ Finset.range js, (1 - ρ) * ρ ^ j := by
        rw [add_zero]; exact Finset.sum_range_reflect (fun j => (1 - ρ) * ρ ^ j) js
    _ ≤ 1 := pb2_geom ρ h0 js

/-! ## One block -/
/-- The absolute constant `D = 10^200`. -/
noncomputable def pb2_D : ℝ := 10 ^ 200

lemma pb2_D_eq : pb2_D = 10 ^ 200 := rfl

lemma pb2_D_pos : 0 < pb2_D := by rw [pb2_D_eq]; norm_num

attribute [irreducible] pb2_D
/-- Blocks with `a = 2` (`j ≥ j*`). -/
lemma pb2_caseA {α T : ℝ} (H : pb2_Hyp α T) (U V : ℝ) (k : ℕ) (hU1 : 1 ≤ U) (hUT : U ≤ T)
    (hV : 0 < V) (hUY : U ≤ Yp α T * Real.log T ^ 2) (hUs : pb2_Ust α T * 2 ^ k ≤ 2 * U)
    (hk : (k : ℝ) + 1 ≤ 5 * Real.log T) (hVR : V⁻¹ ≤ 10 * (1 + (k : ℝ)) ^ 2) :
    Bfun α T 2 U V ≤
      T ^ ex α * (pb2_D * Real.log T ^ 43 * pb2_phi k + pb2_D * Real.log T ^ 42) := by
  have hT := H.hT
  have hl : 1 ≤ Real.log T := by linarith [H.hl]
  have hl0 : 0 < Real.log T := by linarith
  have hE : 0 < T ^ ex α := Real.rpow_pos_of_pos (by linarith) _
  have hD := pb2_D_pos
  obtain ⟨hQ, hQ'⟩ := pb2_Q T U 2 (by norm_num) hU1 hUT hl
  have hB := pb2_bfun_le α T 2 U V (300 * Real.log T) _ _ hU1 hV hT.le hQ hQ' hVR hVR
  rw [show (4 * 2 ^ 2 - 1 : ℕ) = 15 from rfl, show (2 * 2 : ℕ) = 4 from rfl,
    show (6 * 2 : ℕ) = 12 from rfl, show (3 * 15 : ℕ) = 45 from rfl] at hB
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK1 := pb2_k1 α T U (by linarith [H.h1]) H.x.2.2.2 hT hl (by linarith) hUY
  have hK2 := pb2_k2 α T U k (by linarith [H.h1]) H.x.2.2.2 hT hl (by linarith [H.hll])
    (by linarith) (by unfold pb2_Ust at hUs; exact hUs)
  have t1 : (U ^ 2) ^ (2 * (1 - α)) * (300 * Real.log T) ^ 15 * (10 * (1 + (k : ℝ)) ^ 2) ^ 4 ≤
      T ^ ex α * ((300 ^ 15 * 10 ^ 4 * 5 ^ 8) * Real.log T ^ 25) := by
    calc _ ≤ (T ^ ex α * Real.log T ^ 2) * (300 * Real.log T) ^ 15 *
          (10 * (5 * Real.log T) ^ 2) ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have t2 : (U ^ 2) ^ (4 - 6 * α) * T * (300 * Real.log T) ^ 45 * (10 * (1 + (k : ℝ)) ^ 2) ^ 12 *
      (300 * Real.log T) ^ 2 ≤
      T ^ ex α * ((4 * 300 ^ 47 * 10 ^ 12) * Real.log T ^ 43 * ((k : ℝ) + 1) ^ 24 *
        (1 / 2) ^ k) := by
    have hl5 : 0 < Real.log T ^ 5 := by positivity
    calc _ = ((U ^ 2) ^ (4 - 6 * α) * T) *
          ((300 * Real.log T) ^ 47 * (10 * (1 + (k : ℝ)) ^ 2) ^ 12) := by ring
      _ ≤ (4 * T ^ ex α * (Real.log T ^ 5)⁻¹ * (1 / 2) ^ k) *
          ((300 * Real.log T) ^ 47 * (10 * (1 + (k : ℝ)) ^ 2) ^ 12) :=
          mul_le_mul_of_nonneg_right hK2 (by positivity)
      _ = T ^ ex α * ((4 * 300 ^ 47 * 10 ^ 12) * Real.log T ^ 42 * ((k : ℝ) + 1) ^ 24 *
          (1 / 2) ^ k) := by
          field_simp; ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hE.le
          have h4243 : Real.log T ^ 42 ≤ Real.log T ^ 43 := pow_le_pow_right₀ hl (by norm_num)
          have hA : 0 ≤ (4 * 300 ^ 47 * 10 ^ 12 : ℝ) * (((k : ℝ) + 1) ^ 24 * (1 / 2) ^ k) := by
            positivity
          calc (4 * 300 ^ 47 * 10 ^ 12 : ℝ) * Real.log T ^ 42 * ((k : ℝ) + 1) ^ 24 * (1 / 2) ^ k
              = (4 * 300 ^ 47 * 10 ^ 12 : ℝ) * (((k : ℝ) + 1) ^ 24 * (1 / 2) ^ k) *
                  Real.log T ^ 42 := by ring
            _ ≤ (4 * 300 ^ 47 * 10 ^ 12 : ℝ) * (((k : ℝ) + 1) ^ 24 * (1 / 2) ^ k) *
                  Real.log T ^ 43 := mul_le_mul_of_nonneg_left h4243 hA
            _ = _ := by ring
  have u1' : T ^ ex α * ((300 ^ 15 * 10 ^ 4 * 5 ^ 8) * Real.log T ^ 25) ≤
      T ^ ex α * (pb2_D * Real.log T ^ 42) := by
    apply mul_le_mul_of_nonneg_left _ hE.le
    exact mul_le_mul (by rw [pb2_D_eq]; norm_num) (pow_le_pow_right₀ hl (by norm_num))
      (by positivity) pb2_D_pos.le
  have u2' : T ^ ex α * ((4 * 300 ^ 47 * 10 ^ 12) * Real.log T ^ 43 * ((k : ℝ) + 1) ^ 24 *
      (1 / 2) ^ k) ≤ T ^ ex α * (pb2_D * Real.log T ^ 43 * pb2_phi k) := by
    apply mul_le_mul_of_nonneg_left _ hE.le
    unfold pb2_phi
    calc _ ≤ pb2_D * Real.log T ^ 43 * ((k : ℝ) + 1) ^ 24 * (1 / 2) ^ k := by
          gcongr; rw [pb2_D_eq]; norm_num
      _ = _ := by ring
  calc Bfun α T 2 U V ≤ _ := hB
    _ ≤ T ^ ex α * ((300 ^ 15 * 10 ^ 4 * 5 ^ 8) * Real.log T ^ 25) +
        T ^ ex α * ((4 * 300 ^ 47 * 10 ^ 12) * Real.log T ^ 43 * ((k : ℝ) + 1) ^ 24 *
          (1 / 2) ^ k) :=
        add_le_add t1 t2
    _ ≤ T ^ ex α * (pb2_D * Real.log T ^ 42) + T ^ ex α * (pb2_D * Real.log T ^ 43 * pb2_phi k) :=
        add_le_add u1' u2'
    _ = _ := by ring

/-- Blocks with `a = 3` (`j = j* - 1 - m`). -/
lemma pb2_caseB {α T : ℝ} (H : pb2_Hyp α T) (U V : ℝ) (m : ℕ) (hU1 : 1 ≤ U) (hUT : U ≤ T)
    (hV : 0 < V) (hUs : U * 2 ^ (m + 1) ≤ pb2_Ust α T) (hM : Wp α T ^ (17 / 16 : ℝ) ≤ U ^ 3)
    (hk : ((m + 1 : ℕ) : ℝ) + 1 ≤ 5 * Real.log T)
    (hV1 : V⁻¹ ≤ 10 * (1 + ((m + 1 : ℕ) : ℝ)) ^ 2)
    (hV2 : V⁻¹ ≤ 10 / ((1 - pb2_rho α) * pb2_rho α ^ m)) :
    Bfun α T 3 U V ≤ T ^ ex α * (pb2_D * Real.log T ^ 43 * ((1 - pb2_rho α) * pb2_rho α ^ m) +
      pb2_D * Real.log T ^ 42) := by
  have hT := H.hT
  have hl : 1 ≤ Real.log T := by linarith [H.hl]
  have hl0 : 0 < Real.log T := by linarith
  have hE : 0 < T ^ ex α := Real.rpow_pos_of_pos (by linarith) _
  have hD := pb2_D_pos
  obtain ⟨hρ0, hρ1⟩ := pb2_rho_pos H
  have hr0 : 0 < 1 - pb2_rho α := by linarith
  have hρm : 0 < pb2_rho α ^ m := pow_pos hρ0 m
  have hh : 0 < (1 - pb2_rho α) * pb2_rho α ^ m := mul_pos hr0 hρm
  obtain ⟨hQ, hQ'⟩ := pb2_Q T U 3 (by norm_num) hU1 hUT hl
  have hB := pb2_bfun_le α T 3 U V (300 * Real.log T) _ _ hU1 hV hT.le hQ hQ' hV2 hV1
  obtain ⟨hR0, hR⟩ := pb2_R_le (m + 1) hl hk
  have t2 := pb2_term2_save H 3 (by norm_num) U _ hU1 hM hR0 hR
  have hK3 := pb2_k3 α T U m (by linarith [H.h1]) H.x.2.2.2 hT hl (by linarith) hUs
  have hEE := pb2_E H
  have hcoef : (300 ^ 35 * 10 ^ 6 * 6 ^ 7 * Real.exp 30 : ℝ) ≤ pb2_D := by
    rw [pb2_D_eq]
    calc (300 ^ 35 * 10 ^ 6 * 6 ^ 7 * Real.exp 30 : ℝ) ≤ 300 ^ 35 * 10 ^ 6 * 6 ^ 7 * 3 ^ 30 := by
          gcongr; exact pb2_exp30
      _ ≤ 10 ^ 200 := by norm_num
  have t1 : (U ^ 3) ^ (2 * (1 - α)) * (300 * Real.log T) ^ (4 * 3 ^ 2 - 1) *
      (10 / ((1 - pb2_rho α) * pb2_rho α ^ m)) ^ (2 * 3) ≤
      T ^ ex α * (pb2_D * Real.log T ^ 43 * ((1 - pb2_rho α) * pb2_rho α ^ m)) := by
    rw [show (4 * 3 ^ 2 - 1 : ℕ) = 35 from rfl, show (2 * 3 : ℕ) = 6 from rfl]
    have hi : 0 < (1 - pb2_rho α)⁻¹ := inv_pos.2 hr0
    calc _ = (300 * Real.log T) ^ 35 * 10 ^ 6 * ((1 - pb2_rho α)⁻¹) ^ 6 *
          ((U ^ 3) ^ (2 * (1 - α)) * ((pb2_rho α ^ m)⁻¹) ^ 6) := by
          rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ (300 * Real.log T) ^ 35 * 10 ^ 6 * ((1 - pb2_rho α)⁻¹) ^ 6 *
          (T ^ ex α * Real.log T ^ (30 * (1 - α)) * pb2_rho α ^ m) :=
          mul_le_mul_of_nonneg_left hK3 (by positivity)
      _ = T ^ ex α * (300 * Real.log T) ^ 35 * 10 ^ 6 * pb2_rho α ^ m *
          (Real.log T ^ (30 * (1 - α)) * ((1 - pb2_rho α)⁻¹) ^ 6) := by ring
      _ ≤ T ^ ex α * (300 * Real.log T) ^ 35 * 10 ^ 6 * pb2_rho α ^ m *
          (6 ^ 7 * Real.exp 30 * Real.log T ^ 8 * (1 - pb2_rho α)) :=
          mul_le_mul_of_nonneg_left hEE (by positivity)
      _ = T ^ ex α * ((300 ^ 35 * 10 ^ 6 * 6 ^ 7 * Real.exp 30) * Real.log T ^ 43 *
          ((1 - pb2_rho α) * pb2_rho α ^ m)) := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hE.le
          apply mul_le_mul_of_nonneg_right _ hh.le
          exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have u : T ^ ex α ≤ T ^ ex α * (pb2_D * Real.log T ^ 42) :=
    le_mul_of_one_le_right hE.le (one_le_mul_of_one_le_of_one_le
      (by rw [pb2_D_eq]; norm_num) (one_le_pow₀ hl))
  calc Bfun α T 3 U V ≤ _ := hB
    _ ≤ T ^ ex α * (pb2_D * Real.log T ^ 43 * ((1 - pb2_rho α) * pb2_rho α ^ m)) +
        T ^ ex α * (pb2_D * Real.log T ^ 42) := add_le_add t1 (t2.trans u)
    _ = _ := by ring

/-- Blocks with `a ≥ 4`: both terms have a saving. -/
lemma pb2_caseC {α T : ℝ} (H : pb2_Hyp α T) (U V : ℝ) (k n : ℕ) (hn4 : 4 ≤ n) (hn : n ≤ 100)
    (hn12 : 19 / 20 < α → n ≤ 12) (hU1 : 1 ≤ U) (hUT : U ≤ T) (hV : 0 < V)
    (h3 : U ^ 3 ≤ Wp α T ^ (17 / 16 : ℝ)) (hn' : U ^ (n - 1) ≤ Wp α T ^ (17 / 16 : ℝ))
    (hM : Wp α T ^ (17 / 16 : ℝ) ≤ U ^ n)
    (hk : (k : ℝ) + 1 ≤ 5 * Real.log T) (hVR : V⁻¹ ≤ 10 * (1 + (k : ℝ)) ^ 2) :
    Bfun α T n U V ≤ T ^ ex α * (pb2_D * Real.log T ^ 42) := by
  have hT := H.hT
  have hT0 : 0 < T := by linarith
  have hl : 1 ≤ Real.log T := by linarith [H.hl]
  have hl0 : 0 < Real.log T := by linarith
  have hE : 0 < T ^ ex α := Real.rpow_pos_of_pos hT0 _
  obtain ⟨hQ, hQ'⟩ := pb2_Q T U n hn hU1 hUT hl
  have hB := pb2_bfun_le α T n U V (300 * Real.log T) _ _ hU1 hV hT.le hQ hQ' hVR hVR
  obtain ⟨hR0, hR⟩ := pb2_R_le k hl hk
  have t2 := pb2_term2_save H n hn U _ hU1 hM hR0 hR
  have hX := pb2_k4 α T U n (by linarith [H.h1]) H.x.2.2.2 hT hU1 (by omega) h3 hn'
  have hQ1 : 1 ≤ 300 * Real.log T := by linarith
  have hP0 : 0 ≤ (300 * Real.log T) ^ (4 * n ^ 2 - 1) * (10 * (1 + (k : ℝ)) ^ 2) ^ (2 * n) := by
    positivity
  have hX0 : 0 ≤ (U ^ n) ^ (2 * (1 - α)) := Real.rpow_nonneg (by positivity) _
  have t1 : (U ^ n) ^ (2 * (1 - α)) * (300 * Real.log T) ^ (4 * n ^ 2 - 1) *
      (10 * (1 + (k : ℝ)) ^ 2) ^ (2 * n) ≤ T ^ ex α := by
    rw [mul_assoc]
    by_cases hα : α ≤ 19 / 20
    · have hS : T ^ (1 / 240 : ℝ) ≤ T ^ ((1 - α) / 12) :=
        Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
      have hX' : (U ^ n) ^ (2 * (1 - α)) ≤ T ^ ex α * (T ^ (1 / 240 : ℝ))⁻¹ :=
        hX.trans (mul_le_mul_of_nonneg_left
          (inv_anti₀ (Real.rpow_pos_of_pos hT0 _) hS) hE.le)
      exact pb2_save_term hE.le (Real.rpow_pos_of_pos hT0 _) hX0 hX' hP0
        (((pb2_save_exp n hn _ _ hQ1 hR0 hR).1).trans (pb2_absorb H))
    · have h12 := hn12 (by linarith)
      exact pb2_save_term hE.le (Real.rpow_pos_of_pos hT0 _) hX0 hX hP0
        ((pb2_save_exp12 n h12 _ _ hQ1 hR0 hR).trans (pb2_absorb2 H))
  have h2D : 2 ≤ pb2_D * Real.log T ^ 42 := by
    have : 2 * 1 ≤ pb2_D * Real.log T ^ 42 :=
      mul_le_mul (by rw [pb2_D_eq]; norm_num) (one_le_pow₀ hl) zero_le_one pb2_D_pos.le
    linarith
  calc Bfun α T n U V ≤ _ := hB
    _ ≤ T ^ ex α + T ^ ex α := add_le_add t1 t2
    _ = T ^ ex α * 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2D hE.le

/-! ## The choice of thresholds and powers -/
/-- `h_j = (1-ρ) ρ^{j*-1-j}` below `j*`, else `0`. -/
noncomputable def pb2_h (α T : ℝ) (j : ℕ) : ℝ :=
  if j < pb2_jst α T then (1 - pb2_rho α) * pb2_rho α ^ (pb2_jst α T - 1 - j) else 0

/-- `V_j = (1/10) (1 + |j - j*|)^{-2} + h_j / 10`. -/
noncomputable def pb2_V (α T : ℝ) (j : ℕ) : ℝ :=
  1 / (10 * (1 + (pb2_k (pb2_jst α T) j : ℝ)) ^ 2) + pb2_h α T j / 10

lemma pb2_h_nonneg {α T : ℝ} (H : pb2_Hyp α T) (j : ℕ) : 0 ≤ pb2_h α T j := by
  obtain ⟨hρ0, hρ1⟩ := pb2_rho_pos H
  unfold pb2_h
  split_ifs
  · exact mul_nonneg (by linarith) (pow_nonneg hρ0.le _)
  · exact le_rfl

lemma pb2_V_pos {α T : ℝ} (H : pb2_Hyp α T) (j : ℕ) : 0 < pb2_V α T j := by
  unfold pb2_V
  have := pb2_h_nonneg H j
  have : 0 < 1 / (10 * (1 + (pb2_k (pb2_jst α T) j : ℝ)) ^ 2) := by positivity
  linarith [div_nonneg (pb2_h_nonneg H j) (by norm_num : (0:ℝ) ≤ 10)]

lemma pb2_V_sum {α T : ℝ} (H : pb2_Hyp α T) (n : ℕ) :
    ∑ j ∈ Finset.range n, pb2_V α T j ≤ 1 / 2 := by
  obtain ⟨hρ0, hρ1⟩ := pb2_rho_pos H
  unfold pb2_V
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have h1 := pb2_inv_sq_sum n (pb2_jst α T)
  have h2 := pb2_h_sum (pb2_rho α) hρ0.le hρ1.le (pb2_jst α T) n
  have h2' : ∑ j ∈ Finset.range n, pb2_h α T j ≤ 1 := h2
  linarith

/-- Admissible powers below `j*`: `b ≥ 3` and `U_j^b ≥ W^{17/16}` (or the cap `b = 100`). -/
def pb2_P (α T : ℝ) (j b : ℕ) : Prop :=
  3 ≤ b ∧ (Wp α T ^ (17 / 16 : ℝ) ≤ ((N0 α T : ℝ) * 2 ^ j) ^ b ∨ b = 100)

lemma pb2_P_ex (α T : ℝ) (j : ℕ) : ∃ b, pb2_P α T j b := ⟨100, by norm_num, Or.inr rfl⟩

open Classical in
/-- `a_j = 2` for `j ≥ j*`, else the least admissible `b`. -/
noncomputable def pb2_a (α T : ℝ) (j : ℕ) : ℕ :=
  if pb2_jst α T ≤ j then 2 else Nat.find (pb2_P_ex α T j)

lemma pb2_a_range (α T : ℝ) (j : ℕ) : 1 ≤ pb2_a α T j ∧ pb2_a α T j ≤ 100 := by
  classical
  unfold pb2_a
  split_ifs
  · norm_num
  · refine ⟨?_, Nat.find_min' _ ⟨by norm_num, Or.inr rfl⟩⟩
    have := (Nat.find_spec (pb2_P_ex α T j)).1
    convert (show 1 ≤ 3 by norm_num).trans this

lemma pb2_block {α T : ℝ} (H : pb2_Hyp α T) (j : ℕ) (hj : j < Jn α T) :
    Bfun α T (pb2_a α T j) ((N0 α T : ℝ) * 2 ^ j) (pb2_V α T j) ≤
      T ^ ex α * (pb2_D * Real.log T ^ 43 * pb2_phi (pb2_k (pb2_jst α T) j) +
        pb2_D * Real.log T ^ 42 + pb2_D * Real.log T ^ 43 * pb2_h α T j) := by
  classical
  have hT := H.hT
  obtain ⟨hN1, -, -⟩ := pb2_N0 H
  have hN : (1 : ℝ) ≤ N0 α T := by exact_mod_cast hN1
  set U := (N0 α T : ℝ) * 2 ^ j with hUdef
  have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ (by norm_num))
  have hUY := pb2_blk_le H j hj
  have hUT : U ≤ T := hUY.trans (pb2_YT H).2
  obtain ⟨-, hjst, hjJ⟩ := pb2_idx H
  have hjl := hjJ j hj
  obtain ⟨hs1, hs2⟩ := pb2_jst_spec H
  have hl : 1 ≤ Real.log T := by linarith [H.hl]
  have hl0 : 0 < Real.log T := by linarith
  have hE : 0 < T ^ ex α := Real.rpow_pos_of_pos (by linarith) _
  have hD := pb2_D_pos
  obtain ⟨hρ0, hρ1⟩ := pb2_rho_pos H
  have hh0 := pb2_h_nonneg H j
  have hφ := pb2_phi_nonneg (pb2_k (pb2_jst α T) j)
  have hA0 : 0 ≤ pb2_D * Real.log T ^ 43 * pb2_phi (pb2_k (pb2_jst α T) j) := by positivity
  have hB0 : 0 ≤ pb2_D * Real.log T ^ 43 * pb2_h α T j := by positivity
  set k := pb2_k (pb2_jst α T) j with hkdef
  have hV1 : 0 < 1 / (10 * (1 + (k : ℝ)) ^ 2) := by positivity
  have hVge : 1 / (10 * (1 + (k : ℝ)) ^ 2) ≤ pb2_V α T j := by
    unfold pb2_V; rw [← hkdef]
    linarith [div_nonneg hh0 (by norm_num : (0:ℝ) ≤ 10)]
  have hVpos : 0 < pb2_V α T j := lt_of_lt_of_le hV1 hVge
  have hVR : (pb2_V α T j)⁻¹ ≤ 10 * (1 + (k : ℝ)) ^ 2 := by
    have := inv_anti₀ hV1 hVge
    rwa [one_div, inv_inv] at this
  have hkl : (k : ℝ) + 1 ≤ 5 * Real.log T := by
    have hk' : k ≤ j + pb2_jst α T := by
      rw [hkdef]; unfold pb2_k; split_ifs <;> omega
    have : (k : ℝ) ≤ j + pb2_jst α T := by exact_mod_cast hk'
    linarith
  by_cases hjs : pb2_jst α T ≤ j
  · have hk : k = j - pb2_jst α T := by rw [hkdef]; unfold pb2_k; rw [if_pos hjs]
    have ha : pb2_a α T j = 2 := if_pos hjs
    rw [ha]
    have hUs : pb2_Ust α T * 2 ^ k ≤ 2 * U := by
      have e : (2 : ℝ) ^ pb2_jst α T * 2 ^ (j - pb2_jst α T) = 2 ^ j := by
        rw [← pow_add, Nat.add_sub_cancel' hjs]
      rw [hk]
      calc pb2_Ust α T * 2 ^ (j - pb2_jst α T)
          ≤ 2 * ((N0 α T : ℝ) * 2 ^ pb2_jst α T) * 2 ^ (j - pb2_jst α T) :=
            mul_le_mul_of_nonneg_right hs2.le (by positivity)
        _ = 2 * U := by rw [hUdef, ← e]; ring
    have := pb2_caseA H U (pb2_V α T j) k hU1 hUT hVpos hUY hUs hkl hVR
    calc _ ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hE.le
  · set m := pb2_jst α T - 1 - j with hmdef
    have hkm : k = m + 1 := by rw [hkdef, hmdef]; unfold pb2_k; rw [if_neg hjs]; omega
    have hh : pb2_h α T j = (1 - pb2_rho α) * pb2_rho α ^ m := by
      unfold pb2_h; rw [if_pos (by omega)]
    have hhpos : 0 < (1 - pb2_rho α) * pb2_rho α ^ m :=
      mul_pos (by linarith) (pow_pos hρ0 m)
    have hVge2 : (1 - pb2_rho α) * pb2_rho α ^ m / 10 ≤ pb2_V α T j := by
      unfold pb2_V; rw [← hh]; linarith
    have hV2 : (pb2_V α T j)⁻¹ ≤ 10 / ((1 - pb2_rho α) * pb2_rho α ^ m) := by
      have := inv_anti₀ (by positivity) hVge2
      rwa [inv_div] at this
    have hUs : U * 2 ^ (m + 1) ≤ pb2_Ust α T := by
      have e : (2 : ℝ) ^ j * 2 ^ (m + 1) = 2 ^ pb2_jst α T := by
        rw [← pow_add]; congr 1; omega
      calc U * 2 ^ (m + 1) = (N0 α T : ℝ) * 2 ^ pb2_jst α T := by
            rw [hUdef, ← e]; ring
        _ ≤ _ := hs1
    have ha : pb2_a α T j = Nat.find (pb2_P_ex α T j) := if_neg hjs
    rw [ha]
    have hspec := Nat.find_spec (pb2_P_ex α T j)
    have h100 : Nat.find (pb2_P_ex α T j) ≤ 100 := Nat.find_min' _ ⟨by norm_num, Or.inr rfl⟩
    have hM : Wp α T ^ (17 / 16 : ℝ) ≤ U ^ Nat.find (pb2_P_ex α T j) := by
      rcases hspec.2 with h | h
      · exact h
      · rw [h]; exact pb2_cap H j
    rcases Nat.eq_or_lt_of_le hspec.1 with h3 | h4
    · rw [← h3] at hM ⊢
      have hk' : ((m + 1 : ℕ) : ℝ) + 1 ≤ 5 * Real.log T := by rw [← hkm]; exact hkl
      have hV1' : (pb2_V α T j)⁻¹ ≤ 10 * (1 + ((m + 1 : ℕ) : ℝ)) ^ 2 := by rw [← hkm]; exact hVR
      have := pb2_caseB H U (pb2_V α T j) m hU1 hUT hVpos hUs hM hk' hV1' hV2
      rw [← hh] at this
      calc _ ≤ _ := this
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hE.le
    · have hn3 : ¬ pb2_P α T j 3 := Nat.find_min _ h4
      have hn1 : ¬ pb2_P α T j (Nat.find (pb2_P_ex α T j) - 1) := Nat.find_min _ (by omega)
      have h3' : U ^ 3 ≤ Wp α T ^ (17 / 16 : ℝ) := by
        by_contra hc
        exact hn3 ⟨le_rfl, Or.inl (not_le.1 hc).le⟩
      have hn' : U ^ (Nat.find (pb2_P_ex α T j) - 1) ≤ Wp α T ^ (17 / 16 : ℝ) := by
        by_contra hc
        exact hn1 ⟨by omega, Or.inl (not_le.1 hc).le⟩
      have hn12 : 19 / 20 < α → Nat.find (pb2_P_ex α T j) ≤ 12 := fun hα =>
        Nat.find_min' _ ⟨by norm_num, Or.inl (pb2_twelve H hα j)⟩
      have := pb2_caseC H U (pb2_V α T j) k _ h4 h100 hn12 hU1 hUT hVpos h3' hn' hM hkl hVR
      calc _ ≤ _ := this
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hE.le

/-! ## The theorem -/
theorem bookkeeping : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T →
    ∃ (V : ℕ → ℝ) (a : ℕ → ℕ), (∀ j, 0 < V j) ∧ (∑ j ∈ Finset.range (Jn α T), V j ≤ 1 / 2) ∧
      (∀ j, 1 ≤ a j ∧ a j ≤ 100) ∧
      ∑ j ∈ Finset.range (Jn α T), Bfun α T (a j) ((N0 α T : ℝ) * 2 ^ j) (V j) ≤
        C * T ^ ex α * Real.log T ^ 43 := by
  set S := ∑' k, pb2_phi k with hS
  have hS0 : 0 ≤ S := tsum_nonneg pb2_phi_nonneg
  refine ⟨pb2_D * (2 * S + 4), Real.exp (Real.exp 200),
    mul_nonneg pb2_D_pos.le (by linarith), fun T hT α hα => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hl : Real.exp 200 ≤ Real.log T := by rw [Real.le_log_iff_exp_le hT0]; exact hT
  have he : (10 : ℝ) ^ 50 ≤ Real.exp 200 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (10 : ℝ) ^ 50 ≤ 2 ^ 200 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 200
  have hll : 200 ≤ Real.log (Real.log T) := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 200])]; exact hl
  have hT1 : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hT
  have H : pb2_Hyp α T := ⟨hα.1, hα.2, by linarith, hll, hT1⟩
  refine ⟨pb2_V α T, pb2_a α T, fun j => pb2_V_pos H j, pb2_V_sum H _, pb2_a_range α T, ?_⟩
  have hl1 : 1 ≤ Real.log T := by linarith
  have hl0 : 0 < Real.log T := by linarith
  have hE : 0 < T ^ ex α := Real.rpow_pos_of_pos hT0 _
  obtain ⟨hJ, -, -⟩ := pb2_idx H
  have hsum := pb2_sum_k_le pb2_phi pb2_phi_nonneg pb2_phi_summable (Jn α T) (pb2_jst α T)
  rw [← hS] at hsum
  obtain ⟨hρ0, hρ1⟩ := pb2_rho_pos H
  have hhs : ∑ j ∈ Finset.range (Jn α T), pb2_h α T j ≤ 1 :=
    pb2_h_sum (pb2_rho α) hρ0.le hρ1.le (pb2_jst α T) (Jn α T)
  have hD := pb2_D_pos
  set A := T ^ ex α * (pb2_D * Real.log T ^ 43) with hA
  set B := T ^ ex α * (pb2_D * Real.log T ^ 42) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have e : ∀ j, T ^ ex α * (pb2_D * Real.log T ^ 43 * pb2_phi (pb2_k (pb2_jst α T) j) +
      pb2_D * Real.log T ^ 42 + pb2_D * Real.log T ^ 43 * pb2_h α T j) =
      A * pb2_phi (pb2_k (pb2_jst α T) j) + B + A * pb2_h α T j := by
    intro j; rw [hA, hB]; ring
  calc ∑ j ∈ Finset.range (Jn α T), Bfun α T (pb2_a α T j) ((N0 α T : ℝ) * 2 ^ j) (pb2_V α T j)
      ≤ ∑ j ∈ Finset.range (Jn α T), T ^ ex α * (pb2_D * Real.log T ^ 43 *
          pb2_phi (pb2_k (pb2_jst α T) j) + pb2_D * Real.log T ^ 42 +
          pb2_D * Real.log T ^ 43 * pb2_h α T j) :=
        Finset.sum_le_sum fun j hj => pb2_block H j (Finset.mem_range.1 hj)
    _ = A * ∑ j ∈ Finset.range (Jn α T), pb2_phi (pb2_k (pb2_jst α T) j) + (Jn α T : ℝ) * B +
          A * ∑ j ∈ Finset.range (Jn α T), pb2_h α T j := by
        rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * (2 * S) + (3 * Real.log T) * B + A * 1 := by gcongr
    _ = pb2_D * (2 * S + 4) * T ^ ex α * Real.log T ^ 43 := by rw [hA, hB]; ring

end GuthMaynard.CitedZeros.HR2.PartB
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
alias bookkeeping := GuthMaynard.CitedZeros.HR2.PartB.bookkeeping

/-! ## Assembly (no `sorry` below) -/
theorem InR_lt_one : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T → α < 1 := by
  refine ⟨Real.exp (Real.exp 1), fun T hT α hα => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hl : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hT
  have hl0 : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos 1) hl
  have hll : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hl
  have : 0 < 32400 * Real.log (Real.log T) / Real.log T := by positivity
  linarith [hα.2]

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex Finset
theorem typeI_points : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T →
    ∀ P : Finset ℂ, (∀ s ∈ P, α ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T ∧ IsTypeI α T s) →
      (∀ s ∈ P, ∀ s' ∈ P, s ≠ s' → 1 ≤ |s.im - s'.im|) →
      (P.card : ℝ) ≤ C * T ^ ex α * Real.log T ^ 43 := by
  classical
  obtain ⟨Cb, Tb, hCb, hbk⟩ := GuthMaynard.CitedZeros.HR2.bookkeeping
  obtain ⟨C60, hC60, hblk⟩ := block_count 100
  obtain ⟨Tn, hTn⟩ := N0_pos
  obtain ⟨Tl, hTl⟩ := InR_lt_one
  refine ⟨C60 * Cb, max (max Tb Tn) (max 3 Tl), mul_nonneg hC60 hCb, ?_⟩
  intro T hT α hα P hP hsep
  have hTl' : Tl ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hlt : α < 1 := hTl T hTl' α hα
  have hTb : Tb ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTn' : Tn ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : 3 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hN0 := hTn T hTn' α hα.1 hlt.le
  obtain ⟨V, a, hV, hVsum, ha, hB⟩ := hbk T hTb α hα
  have hcover : P ⊆ (range (Jn α T)).biUnion
      (fun j => P.filter (fun s => V j ≤ ‖Dj α T j s‖)) := by
    intro s hs
    rw [mem_biUnion]
    by_contra hcon
    push Not at hcon
    have hlt : ∀ j ∈ range (Jn α T), ‖Dj α T j s‖ < V j := fun j hj => by
      have := hcon j hj
      rw [mem_filter] at this
      push Not at this
      exact this hs
    have hI := (hP s hs).2.2.2.2
    rw [IsTypeI, SI_eq_sum_blocks α T hN0] at hI
    rcases (range (Jn α T)).eq_empty_or_nonempty with he | hne
    · rw [he, sum_empty, norm_zero] at hI; norm_num at hI
    · have := (norm_sum_le _ _).trans_lt (sum_lt_sum_of_nonempty hne hlt)
      linarith
  calc (P.card : ℝ)
      ≤ ∑ j ∈ range (Jn α T), ((P.filter (fun s => V j ≤ ‖Dj α T j s‖)).card : ℝ) := by
        exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ j ∈ range (Jn α T), C60 * Bfun α T (a j) ((N0 α T : ℝ) * 2 ^ j) (V j) := by
        refine sum_le_sum fun j _ => hblk T hT3 α (by linarith [hα.1]) hlt hN0 j (a j) (ha j).1 (ha j).2
          (V j) (hV j) _ (fun s hs => ?_)
          (fun s hs s' hs' => hsep s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1)
        obtain ⟨hs1, hs2⟩ := mem_filter.1 hs
        obtain ⟨a1, a2, a3, a4, -⟩ := hP s hs1
        exact ⟨a1, a2, a3, a4, hs2⟩
    _ = C60 * ∑ j ∈ range (Jn α T), Bfun α T (a j) ((N0 α T : ℝ) * 2 ^ j) (V j) := by
        rw [mul_sum]
    _ ≤ C60 * (Cb * T ^ ex α * Real.log T ^ 43) := mul_le_mul_of_nonneg_left hB hC60
    _ = C60 * Cb * T ^ ex α * Real.log T ^ 43 := by ring

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex Finset
theorem typeI_finset : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T →
    ∀ F : Finset ℂ, (↑F : Set ℂ) ⊆ {ρ | ρ ∈ win α T ∧ IsTypeI α T ρ} →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤
        C * T ^ ex α * Real.log T ^ 44 := by
  classical
  obtain ⟨C, T₀, hC, hPb⟩ := typeI_points
  obtain ⟨A, hA, hloc⟩ := pdl_local_count_finset
  refine ⟨C * (4 * A), max T₀ 4, by positivity, fun T hT α hα F hF => ?_⟩
  have hT4 : 4 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hFz : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => by
    obtain ⟨⟨h1, h2, _, _⟩, _⟩ := hF hρ
    exact ⟨h1, by linarith [hα.1]⟩
  obtain ⟨P, hPF, hsep, hcov⟩ := pdl_exists_separated_cover F
  choose! g hgP hg using hcov
  rw [← Finset.sum_fiberwise_of_maps_to hgP]
  have hlogb : Real.log (T + 4) ≤ 2 * Real.log T := by
    have : 2 * Real.log T = Real.log (T ^ 2) := by rw [Real.log_pow]; norm_num
    rw [this]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hl0 : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hfib : ∀ p ∈ P, ∑ ρ ∈ F.filter (fun ρ => g ρ = p),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ 2 * A * Real.log (T + 4) := by
    intro p hp
    have hsub : F.filter (fun ρ => g ρ = p) ⊆ F.filter (fun ρ => |ρ.im - p.im| ≤ 1) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, hρ.2 ▸ hg ρ hρ.1⟩
    obtain ⟨⟨_, _, hp3, hp4⟩, _⟩ := hF (hPF hp)
    have hp0 : 0 ≤ p.im := le_trans (sq_nonneg _) hp3
    have := hloc F hFz p.im 1 zero_le_one
    rw [abs_of_nonneg (by linarith)] at this
    calc ∑ ρ ∈ F.filter (fun ρ => g ρ = p), ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
        ≤ ∑ ρ ∈ F.filter (fun ρ => |ρ.im - p.im| ≤ 1),
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ A * (1 + 1) * Real.log (p.im + 1 + 3) := this
      _ ≤ 2 * A * Real.log (T + 4) := by
          rw [show A * (1 + 1) = 2 * A by ring]
          exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith))
            (by linarith)
  have hcard : (P.card : ℝ) ≤ C * T ^ ex α * Real.log T ^ 43 := by
    refine hPb T ((le_max_left _ _).trans hT) α hα P (fun s hs => ?_) hsep
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hF (hPF hs)
    have : s.re ≤ 1 := by
      by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_le.1 hc).le h1
    exact ⟨h2, this, le_trans (sq_nonneg _) h3, h4, h5⟩
  have hTe : 0 ≤ T ^ ex α := Real.rpow_nonneg hT0.le _
  calc ∑ p ∈ P, ∑ ρ ∈ F.filter (fun ρ => g ρ = p), ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
      ≤ ∑ p ∈ P, 2 * A * Real.log (T + 4) := Finset.sum_le_sum hfib
    _ = P.card * (2 * A * Real.log (T + 4)) := by simp
    _ ≤ (C * T ^ ex α * Real.log T ^ 43) * (2 * A * (2 * Real.log T)) := by
        apply mul_le_mul hcard _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlogb (by positivity)
    _ = C * (4 * A) * T ^ ex α * Real.log T ^ 44 := by ring

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
alias typeI_finset := GuthMaynard.CitedZeros.HR2.PartDL.typeI_finset

end GuthMaynard.CitedZeros.HR2
end

section
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2.PartDL
open GuthMaynard.CitedZeros.HR2
open Complex MeasureTheory Filter Topology Set
lemma pdl_zeta_conj_iff (ρ : ℂ) : riemannZeta ((starRingEnd ℂ) ρ) = 0 ↔ riemannZeta ρ = 0 := by
  by_cases h : ρ = 1
  · subst h; simp
  · rw [Zeta23.riemannZeta_conj h]; simp

lemma pdl_order_conj (ρ : ℂ) :
    analyticOrderAt riemannZeta ((starRingEnd ℂ) ρ) = analyticOrderAt riemannZeta ρ := by
  by_cases h : ρ = 1
  · subst h; simp
  · exact Zeta23.analyticOrderAt_zeta_conj h

lemma pdl_conj_win (σ T : ℝ) :
    zc {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -T ≤ ρ.im ∧ ρ.im ≤ -(Real.log T ^ 2)} =
      zc (win σ T) := by
  unfold zc
  let e : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -T ≤ ρ.im ∧ ρ.im ≤ -(Real.log T ^ 2)} ≃
      win σ T :=
    { toFun := fun x => ⟨(starRingEnd ℂ) x.1, by
        obtain ⟨h1, h2, h3, h4⟩ := x.2
        refine ⟨(pdl_zeta_conj_iff _).2 h1, ?_, ?_, ?_⟩ <;> simp <;> linarith⟩
      invFun := fun x => ⟨(starRingEnd ℂ) x.1, by
        obtain ⟨h1, h2, h3, h4⟩ := x.2
        refine ⟨(pdl_zeta_conj_iff _).2 h1, ?_, ?_, ?_⟩ <;> simp <;> linarith⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← e.tsum_eq]
  exact tsum_congr fun x => (pdl_order_conj x.1).symm

theorem final_assembly
    (h : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T →
      (zc (win α T) : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ ex α * Real.log T ^ 44)) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 9 / 11 ≤ σ →
      σ ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  obtain ⟨C, T₀, hC, hb⟩ := h
  obtain ⟨A, hA, hloc⟩ := pdl_local_count_finset
  refine ⟨2 * C + 8 * A, max T₀ 16, fun T hT σ hσ1 hσ2 => ?_⟩
  have hT16 : 16 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  set l := Real.log T with hl
  have hl1 : 1 ≤ l := by
    rw [hl, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hll : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hσ1' : σ ≤ 1 := by
    have : 0 ≤ 32400 * Real.log l / l := by positivity
    linarith
  have he0 : 0 ≤ ex σ := by
    unfold ex; apply div_nonneg <;> linarith
  have hTe : 1 ≤ T ^ ex σ := Real.one_le_rpow (by linarith) he0
  have hbk := hb T (le_trans (le_max_left _ _) hT) σ ⟨hσ1, hσ2⟩
  set Wn : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ -T ≤ ρ.im ∧ ρ.im ≤ -(l ^ 2)} with hWn
  set Lo : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ l ^ 2} with hLo
  have hcover : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} ⊆
      win σ T ∪ (Wn ∪ Lo) := by
    rintro s ⟨h1, h2, h3⟩
    obtain ⟨h3a, h3b⟩ := abs_le.1 h3
    by_cases hp : l ^ 2 ≤ s.im
    · exact Or.inl ⟨h1, h2, hp, h3b⟩
    by_cases hn : s.im ≤ -(l ^ 2)
    · exact Or.inr (Or.inl ⟨h1, h2, h3a, hn⟩)
    push Not at hp hn
    exact Or.inr (Or.inr ⟨h1, h2, abs_le.2 ⟨hn.le, hp.le⟩⟩)
  have hlow : (zc Lo : ℝ≥0∞) ≤ ENNReal.ofReal (8 * A * T ^ ex σ * l ^ 44) := by
    refine count_le_of_finset_bound _ _ (fun F hF => ?_)
    have hFz : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ 0 < ρ.re := fun ρ hρ => by
      obtain ⟨h1, h2, _⟩ := hF hρ
      exact ⟨h1, by linarith⟩
    have h1 := hloc F hFz 0 (l ^ 2) (by positivity)
    rw [Finset.filter_true_of_mem (fun ρ hρ => by
      obtain ⟨_, _, h3⟩ := hF hρ
      simpa using h3)] at h1
    have hlog : Real.log (|0| + l ^ 2 + 3) ≤ 3 * l ^ 2 := by
      rw [abs_zero, zero_add]
      have := Real.log_le_sub_one_of_pos (show 0 < l ^ 2 + 3 by positivity)
      nlinarith
    have hl4 : l ^ 4 ≤ l ^ 44 := pow_le_pow_right₀ hl1 (by norm_num)
    have hl44 : 0 ≤ l ^ 44 := by positivity
    calc ∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)
        ≤ A * (l ^ 2 + 1) * Real.log (|0| + l ^ 2 + 3) := h1
      _ ≤ A * (2 * l ^ 2) * (3 * l ^ 2) := by
          have hlog0 : 0 ≤ Real.log (|0| + l ^ 2 + 3) :=
            Real.log_nonneg (by rw [abs_zero]; nlinarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (by nlinarith) hA) hlog hlog0
            (by positivity)
      _ = 6 * A * l ^ 4 := by ring
      _ ≤ 8 * A * (T ^ ex σ * l ^ 44) := by
          have h4 : l ^ 4 ≤ T ^ ex σ * l ^ 44 := by nlinarith
          have h40 : 0 ≤ l ^ 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h4 hA, mul_nonneg hA h40]
      _ = 8 * A * T ^ ex σ * l ^ 44 := by ring
  have hc : zc Wn = zc (win σ T) := pdl_conj_win σ T
  have hP : 0 ≤ C * T ^ ex σ * l ^ 44 := by positivity
  calc (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞)
      = (zc {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} : ℝ≥0∞) := rfl
    _ ≤ ((zc (win σ T) + zc (Wn ∪ Lo) : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (count_union _ _ _ hcover)
    _ ≤ ((zc (win σ T) + (zc Wn + zc Lo) : ℕ∞) : ℝ≥0∞) := by
        gcongr; exact count_union _ _ _ le_rfl
    _ = 2 * (zc (win σ T) : ℝ≥0∞) + (zc Lo : ℝ≥0∞) := by
        rw [hc]; push_cast; ring
    _ ≤ 2 * ENNReal.ofReal (C * T ^ ex σ * l ^ 44) +
          ENNReal.ofReal (8 * A * T ^ ex σ * l ^ 44) := by gcongr
    _ = ENNReal.ofReal ((2 * C + 8 * A) * T ^ (3 * (1 - σ) / (3 * σ - 1)) * l ^ 44) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        change _ = (2 * C + 8 * A) * T ^ ex σ * l ^ 44
        ring

end GuthMaynard.CitedZeros.HR2.PartDL
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.HR2
/-! ## Step 3: from the window to `N(α, T)` -/
alias final_assembly := GuthMaynard.CitedZeros.HR2.PartDL.final_assembly

theorem window_bound : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, InR α T →
    (zc (win α T) : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ ex α * Real.log T ^ 44) := by
  obtain ⟨T₁, hdet⟩ := detect
  obtain ⟨T₂, hno⟩ := no_typeII
  obtain ⟨C, T₃, hC, h₁⟩ := typeI_finset
  obtain ⟨T₄, hlt⟩ := InR_lt_one
  refine ⟨C, max (max T₁ T₂) (max T₃ T₄), hC, fun T hT α hα => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT4 : T₄ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hα1 : α < 1 := hlt T hT4 α hα
  refine count_le_of_finset_bound _ _ (fun F hF => h₁ T hT3 α hα F ?_)
  intro ρ hρ
  have hw := hF hρ
  refine ⟨hw, ?_⟩
  obtain ⟨hz, hre, him1, him2⟩ := hw
  rcases hdet T hT1 α hα.1 hα1 ρ hz hre him1 him2 with h | h
  · exact h
  · exfalso
    have hre1 : ρ.re ≤ 1 := by
      by_contra hc
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.1 hc)) hz
    have himabs : |ρ.im| ≤ T := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.log T)]
    exact hno T hT2 α hα.1 hα1 ρ hre hre1 himabs h

/-- **Huxley (1.9) for `9/11 ≤ α ≤ 1 - 32400 log l / l`.** -/
theorem huxley_density_estimate_of_nine_elevenths_le_dev :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 9 / 11 ≤ σ →
      σ ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) :=
  final_assembly window_bound

end GuthMaynard.CitedZeros.HR2
end

section
open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open GuthMaynard
open GuthMaynard.CitedZeros
open GuthMaynard.CitedZeros.HR2
theorem solution :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 9 / 11 ≤ σ →
      σ ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  exact GuthMaynard.CitedZeros.HR2.huxley_density_estimate_of_nine_elevenths_le_dev
end
