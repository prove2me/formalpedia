-- Prove2me | solution 1 for JMMS.isExtensivelyAmenable_of_isRecurrentAction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:42:12.780603+00:00
-- url     : https://prove2.me/submissions/59f71023-4c50-46ec-bbb8-5c2b8dddfc80

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isExtensivelyAmenable_tfae

section

/-! # JMMS Theorem 4.2 (= JNdlS Theorem 1.2), direct proof

Recurrent actions are extensively amenable, without Lemma 4.3 or Proposition 4.1. By Lemma 2.2
((iii) ⇒ (i), `JMMS.isExtensivelyAmenable_tfae`) it suffices, for a finitely generated `H ≤ G`
and `x₀`, to find an `H`-invariant mean on the finite subsets of the orbit `Y = H x₀` charging
the sets containing `x₀`. Take `μ` uniform on a finite symmetric generating set `T` and write
`P f (y) = c ∑_{h ∈ T} f (h y)` for the transition operator.

1. The first-return decomposition `P^n δ = A^n δ + ∑_j f_j P^{n-1-j} δ` (`A` = `P` killed at
   `x₀`) identifies `firstReturnProb` with `f_j = (P A^j δ)(x₀)`; the renewal equation and
   `∑ f_j = 1` force the Green function `∑_{n ≤ N} P^n δ (x₀)` to be unbounded.
2. The truncated Green function `G_N` has Dirichlet energy `≤ 2 G_N(x₀)` (since
   `P G_N = G_N - δ + P^{N+1} δ`), so `b = min 1 (G_N / G_N(x₀))` has `b(x₀) = 1`, finite
   support and `∑_y (b(hy) - b(y))^2 ≤ 2|T| / G_N(x₀)` for `h ∈ T`.
3. Ozawa's product mean (Juschenko–de la Salle, Remark 2.4): `p_b(E) ∝ ∏_{x ∈ E} b(x)^2`
   gives weight `1/2` to the sets containing `x₀`, and by Cauchy–Schwarz and
   `(1+s²)(1+t²) ≤ (1+st)²(1+(s-t)²)`, `(p_b(hS) - p_b(S))^2 ≤ 4 ∑_y (b(hy) - b(y))^2`.
4. An ultrafilter limit of these means is invariant under `T`, hence under `H`. -/

open IntervalExchange

namespace JMMS.IETP42D

open Finset

/-! ## The renewal equation forces divergence of the Green function -/

section Renewal

theorem sum_range_rec (f u : ℕ → ℝ) (h0 : u 0 = 1)
    (hrec : ∀ n, u (n + 1) = ∑ j ∈ range (n + 1), f j * u (n - j)) (N : ℕ) :
    ∑ n ∈ range (N + 1), u n = 1 + ∑ j ∈ range N, f j * ∑ m ∈ range (N - j), u m := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hrec N]
    have : ∀ j ∈ range (N + 1), f j * ∑ m ∈ range (N + 1 - j), u m =
        f j * ∑ m ∈ range (N - j), u m + f j * u (N - j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show N + 1 - j = (N - j) + 1 by omega, Finset.sum_range_succ, mul_add]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_range_succ (n := N)
      (f := fun j => f j * ∑ m ∈ range (N - j), u m)]
    simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    ring

theorem unbounded_of_renewal (f u : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (hu : ∀ n, 0 ≤ u n)
    (h0 : u 0 = 1) (hrec : ∀ n, u (n + 1) = ∑ j ∈ range (n + 1), f j * u (n - j))
    (hsum : HasSum f 1) (M : ℝ) : ∃ N, M ≤ ∑ n ∈ range N, u n := by
  by_contra hcon
  push Not at hcon
  set V : ℕ → ℝ := fun N => ∑ n ∈ range N, u n with hV
  have hmono : Monotone V := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun i _ _ => hu i)
  have hbdd : BddAbove (Set.range V) := ⟨M, by rintro _ ⟨N, rfl⟩; exact (hcon N).le⟩
  have hT : Filter.Tendsto V Filter.atTop (nhds (⨆ N, V N)) := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ N, V N
  have hrel : ∀ K n, 1 + (∑ j ∈ range K, f j) * V (n + 1) ≤ V (n + K + 1) := by
    intro K n
    simp only [hV]
    rw [sum_range_rec f u h0 hrec (n + K)]
    gcongr
    calc (∑ j ∈ range K, f j) * ∑ m ∈ range (n + 1), u m
        = ∑ j ∈ range K, f j * ∑ m ∈ range (n + 1), u m := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ range K, f j * ∑ m ∈ range (n + K - j), u m := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          exact mul_le_mul_of_nonneg_left (hmono (by omega : n + 1 ≤ n + K - j)) (hf j)
      _ ≤ ∑ j ∈ range (n + K), f j * ∑ m ∈ range (n + K - j), u m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun j _ _ => mul_nonneg (hf j) (Finset.sum_nonneg fun m _ => hu m))
  have hK : ∀ K, 1 + (∑ j ∈ range K, f j) * L ≤ L := by
    intro K
    have h1 : Filter.Tendsto (fun n => 1 + (∑ j ∈ range K, f j) * V (n + 1)) Filter.atTop
        (nhds (1 + (∑ j ∈ range K, f j) * L)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (hT.comp (Filter.tendsto_add_atTop_nat 1)))
    have h2 : Filter.Tendsto (fun n => V (n + K + 1)) Filter.atTop (nhds L) :=
      hT.comp (Filter.tendsto_add_atTop_nat (K + 1))
    exact le_of_tendsto_of_tendsto' h1 h2 (hrel K)
  have hF : Filter.Tendsto (fun K => 1 + (∑ j ∈ range K, f j) * L) Filter.atTop
      (nhds (1 + 1 * L)) :=
    tendsto_const_nhds.add (hsum.tendsto_sum_nat.mul tendsto_const_nhds)
  have := le_of_tendsto' hF hK
  linarith

end Renewal

/-! ## The transition operator and the first-return decomposition -/

section Op

open Classical

variable {H Y : Type*} [Group H] [MulAction H Y] (T : Finset H) (c : ℝ) (y₀ : Y)

/-- `(P f)(y) = c ∑_{h ∈ T} f (h • y)`. -/
noncomputable def Pop : (Y → ℝ) →ₗ[ℝ] (Y → ℝ) where
  toFun f y := c * ∑ h ∈ T, f (h • y)
  map_add' f g := by funext y; simp [Finset.sum_add_distrib, mul_add]
  map_smul' r f := by funext y; simp [Finset.mul_sum]; ring_nf

/-- Killing the value at `y₀`. -/
noncomputable def Kill : (Y → ℝ) →ₗ[ℝ] (Y → ℝ) where
  toFun f y := if y = y₀ then 0 else f y
  map_add' f g := by funext y; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := by funext y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- The taboo operator `A = Kill ∘ P`. -/
noncomputable def Aop : (Y → ℝ) →ₗ[ℝ] (Y → ℝ) := Kill y₀ ∘ₗ Pop T c

/-- The indicator of `y₀`. -/
noncomputable def dlt : Y → ℝ := fun y => if y = y₀ then 1 else 0

theorem Pop_apply (f : Y → ℝ) (y : Y) : Pop T c f y = c * ∑ h ∈ T, f (h • y) := rfl

theorem Aop_apply (f : Y → ℝ) (y : Y) :
    Aop T c y₀ f y = if y = y₀ then 0 else Pop T c f y := rfl

theorem renewal (n : ℕ) :
    (Pop T c ^ n) (dlt y₀) = (Aop T c y₀ ^ n) (dlt y₀) +
      ∑ j ∈ range n, (Pop T c ((Aop T c y₀ ^ j) (dlt y₀))) y₀ • (Pop T c ^ (n - 1 - j)) (dlt y₀) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : Pop T c ((Aop T c y₀ ^ n) (dlt y₀)) = (Aop T c y₀ ^ (n + 1)) (dlt y₀) +
        (Pop T c ((Aop T c y₀ ^ n) (dlt y₀))) y₀ • (Pop T c ^ 0) (dlt y₀) := by
      funext y
      rw [pow_succ', Module.End.mul_apply, pow_zero, Module.End.one_apply]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Aop_apply, dlt]
      split_ifs with hy
      · subst hy; simp
      · simp
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_sum, key, Finset.sum_range_succ,
      Nat.add_sub_cancel, Nat.sub_self, add_assoc]
    rw [add_comm (∑ x ∈ range n, _) _]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← pow_succ', show n - 1 - j + 1 = n - j by omega]

variable {T c}

theorem Pop_nonneg (hc : 0 ≤ c) {f : Y → ℝ} (hf : ∀ y, 0 ≤ f y) (y : Y) : 0 ≤ Pop T c f y :=
  mul_nonneg hc (Finset.sum_nonneg fun _ _ => hf _)

theorem Aop_nonneg (hc : 0 ≤ c) {f : Y → ℝ} (hf : ∀ y, 0 ≤ f y) (y : Y) :
    0 ≤ Aop T c y₀ f y := by
  rw [Aop_apply]; split_ifs
  · exact le_rfl
  · exact Pop_nonneg hc hf y

theorem dlt_nonneg (y : Y) : 0 ≤ dlt y₀ y := by unfold dlt; split_ifs <;> norm_num

theorem Pop_pow_nonneg (hc : 0 ≤ c) (n : ℕ) (y : Y) : 0 ≤ (Pop T c ^ n) (dlt y₀) y := by
  induction n generalizing y with
  | zero => exact dlt_nonneg y₀ y
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact Pop_nonneg hc ih y

theorem Aop_pow_nonneg (hc : 0 ≤ c) (n : ℕ) (y : Y) : 0 ≤ (Aop T c y₀ ^ n) (dlt y₀) y := by
  induction n generalizing y with
  | zero => exact dlt_nonneg y₀ y
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact Aop_nonneg y₀ hc ih y

theorem return_rec (n : ℕ) :
    (Pop T c ^ (n + 1)) (dlt y₀) y₀ = ∑ j ∈ range (n + 1),
      (Pop T c ((Aop T c y₀ ^ j) (dlt y₀))) y₀ * (Pop T c ^ (n - j)) (dlt y₀) y₀ := by
  rw [renewal, pow_succ', Module.End.mul_apply, Pi.add_apply, Aop_apply, if_pos rfl, zero_add,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel]

end Op

/-! ## The chain of the definitions is the operator `P` -/

section Chain

open Classical

variable {H Y : Type*} [Group H] [MulAction H Y] {T : Finset H} (hT : ∀ g, g⁻¹ ∈ T ↔ g ∈ T)
  {μ : H → ℝ} {c : ℝ} (hμ : ∀ g, μ g = if g ∈ T then c else 0) (y₀ : Y)
include hT hμ

omit hT in
theorem walkKernel_eq (z y : Y) :
    walkKernel μ z y = ∑ g ∈ T, if g • z = y then c else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum (s := T)]
  · refine Finset.sum_congr rfl fun g hg => ?_
    rw [hμ, if_pos hg]
  · intro g hg
    rw [hμ, if_neg hg]; simp

theorem tsum_mul_walkKernel (f : Y → ℝ) (y : Y) :
    ∑' z, f z * walkKernel μ z y = Pop T c f y := by
  simp only [walkKernel_eq hμ, Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · rw [Pop_apply, Finset.mul_sum]
    refine Finset.sum_equiv (Equiv.inv H) (fun g => by simp [hT]) fun g _ => ?_
    have : ∀ z, f z * (if g • z = y then c else 0) = if z = g⁻¹ • y then c * f z else 0 := by
      intro z
      rw [eq_inv_smul_iff]
      split_ifs <;> ring
    simp only [this]
    rw [tsum_ite_eq]
    rfl
  · intro g _
    refine summable_of_ne_finset_zero (s := {g⁻¹ • y}) fun z hz => ?_
    rw [Finset.mem_singleton, eq_inv_smul_iff] at hz
    simp [hz]

theorem walkKernel_eq_Pop (y : Y) : walkKernel μ y₀ y = Pop T c (dlt y₀) y := by
  rw [← tsum_mul_walkKernel hT hμ]
  have : ∀ z, dlt y₀ z * walkKernel μ z y = if z = y₀ then walkKernel μ z y else 0 := by
    intro z; unfold dlt; split_ifs <;> simp
  simp only [this]
  rw [tsum_ite_eq]

theorem avoidProb_eq (k : ℕ) :
    avoidProb (walkKernel μ) y₀ (k + 1) = (Aop T c y₀ ^ (k + 1)) (dlt y₀) := by
  induction k with
  | zero =>
    funext y
    rw [zero_add, pow_one, Aop_apply, ← walkKernel_eq_Pop hT hμ]
    rfl
  | succ k ih =>
    funext y
    rw [pow_succ', Module.End.mul_apply, Aop_apply, ← ih, ← tsum_mul_walkKernel hT hμ]
    rfl

theorem firstReturnProb_eq (k : ℕ) :
    firstReturnProb (walkKernel μ) y₀ k = Pop T c ((Aop T c y₀ ^ k) (dlt y₀)) y₀ := by
  cases k with
  | zero => rw [pow_zero, Module.End.one_apply, ← walkKernel_eq_Pop hT hμ]; rfl
  | succ k =>
    rw [← avoidProb_eq hT hμ, ← tsum_mul_walkKernel hT hμ]
    rfl

theorem green_unbounded (hc : 0 ≤ c) (hrec : IsRecurrentChain (walkKernel μ) y₀) (M : ℝ) :
    ∃ N, M ≤ ∑ n ∈ range N, (Pop T c ^ n) (dlt y₀) y₀ := by
  refine unbounded_of_renewal (fun j => Pop T c ((Aop T c y₀ ^ j) (dlt y₀)) y₀)
    (fun n => (Pop T c ^ n) (dlt y₀) y₀) (fun j => Pop_nonneg hc (Aop_pow_nonneg y₀ hc j) _)
    (fun n => Pop_pow_nonneg y₀ hc n _) (by simp [dlt]) (return_rec y₀) ?_ M
  unfold IsRecurrentChain at hrec
  rwa [show firstReturnProb (walkKernel μ) y₀ = _ from funext (firstReturnProb_eq hT hμ y₀)]
    at hrec

end Chain

/-! ## The energy of the truncated Green function -/

section Energy

open Classical Function

variable {H Y : Type*} [Group H] [MulAction H Y]

theorem fs_summable {f : Y → ℝ} {s : Set Y} (hs : s.Finite) (h : support f ⊆ s) : Summable f :=
  summable_of_ne_finset_zero (s := hs.toFinset) fun y hy => by
    by_contra hne
    exact hy (hs.mem_toFinset.mpr (h hne))

theorem support_smul_finite {f : Y → ℝ} (hf : (support f).Finite) (h : H) :
    (support fun y => f (h • y)).Finite := by
  have : (support fun y => f (h • y)) = (fun y => h • y) ⁻¹' support f := rfl
  rw [this]
  exact hf.preimage (fun a _ b _ hab => MulAction.injective h hab)

variable (T : Finset H) (c : ℝ)

theorem Pop_finite {f : Y → ℝ} (hf : (support f).Finite) : (support (Pop T c f)).Finite := by
  refine (Set.Finite.biUnion (s := (T : Set H)) T.finite_toSet
    fun h _ => support_smul_finite hf h).subset ?_
  intro y hy
  rw [mem_support, Pop_apply] at hy
  obtain ⟨h, hh, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
  exact Set.mem_biUnion (Finset.mem_coe.mpr hh) hne

theorem dlt_finite (y₀ : Y) : (support (dlt y₀)).Finite :=
  (Set.finite_singleton y₀).subset fun y hy => by
    by_contra h; exact hy (by simp [dlt, show y ≠ y₀ from h])

theorem Pop_pow_finite (y₀ : Y) (n : ℕ) : (support ((Pop T c ^ n) (dlt y₀))).Finite := by
  induction n with
  | zero => exact dlt_finite y₀
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact Pop_finite T c ih

/-- The truncated Green function `G_N = ∑_{n ≤ N} P^n δ`. -/
noncomputable def green (y₀ : Y) (N : ℕ) : Y → ℝ := ∑ n ∈ range (N + 1), (Pop T c ^ n) (dlt y₀)

theorem green_finite (y₀ : Y) (N : ℕ) : (support (green T c y₀ N)).Finite := by
  unfold green
  induction N with
  | zero => simpa using Pop_pow_finite T c y₀ 0
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (ih.union (Pop_pow_finite T c y₀ (N + 1))).subset (Function.support_add _ _)

theorem green_apply (y₀ : Y) (N : ℕ) (y : Y) :
    green T c y₀ N y = ∑ n ∈ range (N + 1), (Pop T c ^ n) (dlt y₀) y := by
  simp [green, Finset.sum_apply]

theorem Pop_green (y₀ : Y) (N : ℕ) :
    Pop T c (green T c y₀ N) + dlt y₀ = green T c y₀ N + (Pop T c ^ (N + 1)) (dlt y₀) := by
  unfold green
  rw [map_sum]
  have : ∀ n ∈ range (N + 1), Pop T c ((Pop T c ^ n) (dlt y₀)) = (Pop T c ^ (n + 1)) (dlt y₀) :=
    fun n _ => by rw [pow_succ', Module.End.mul_apply]
  rw [Finset.sum_congr rfl this, Finset.sum_range_succ' (fun n => (Pop T c ^ n) (dlt y₀)),
    Finset.sum_range_succ (fun n => (Pop T c ^ (n + 1)) (dlt y₀))]
  simp only [pow_zero, Module.End.one_apply]
  abel

variable {T c} (hT : ∀ g, g⁻¹ ∈ T ↔ g ∈ T) (hcT : c * T.card = 1)
include hcT

theorem energy_eq {a : Y → ℝ} (ha : (support a).Finite) :
    c * ∑ h ∈ T, ∑' y, (a (h • y) - a y) ^ 2 =
      2 * (∑' y, a y ^ 2 - ∑' y, a y * Pop T c a y) := by
  have hsq : ∀ h : H, ∑' y, a (h • y) ^ 2 = ∑' y, a y ^ 2 := fun h =>
    Equiv.tsum_eq (MulAction.toPerm h) (fun y => a y ^ 2)
  have s1 : Summable fun y => a y ^ 2 := fs_summable ha fun y hy => by
    simp only [mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true] at hy
    exact hy
  have s2 : ∀ h : H, Summable fun y => a (h • y) ^ 2 := fun h =>
    fs_summable (support_smul_finite ha h) fun y hy => by
      simp only [mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true] at hy
      exact hy
  have s3 : ∀ h : H, Summable fun y => a y * a (h • y) := fun h =>
    fs_summable ha fun y hy => left_ne_zero_of_mul hy
  have hterm : ∀ h : H, ∑' y, (a (h • y) - a y) ^ 2 =
      2 * ∑' y, a y ^ 2 - 2 * ∑' y, a y * a (h • y) := by
    intro h
    have : ∀ y, (a (h • y) - a y) ^ 2 = (a (h • y) ^ 2 + a y ^ 2) - 2 * (a y * a (h • y)) :=
      fun y => by ring
    simp only [this]
    rw [Summable.tsum_sub ((s2 h).add s1) ((s3 h).mul_left 2), Summable.tsum_add (s2 h) s1,
      tsum_mul_left, hsq]
    ring
  have hP : ∑' y, a y * Pop T c a y = c * ∑ h ∈ T, ∑' y, a y * a (h • y) := by
    have : ∀ y, a y * Pop T c a y = ∑ h ∈ T, c * (a y * a (h • y)) := by
      intro y
      rw [Pop_apply, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [tsum_congr this, Summable.tsum_finsetSum fun h _ => ((s3 h).mul_left c), Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => tsum_mul_left
  simp only [hterm, hP, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  linear_combination (2 * ∑' y, a y ^ 2) * hcT

theorem energy_green_le (hc : 0 ≤ c) (y₀ : Y) (N : ℕ) :
    c * ∑ h ∈ T, ∑' y, (green T c y₀ N (h • y) - green T c y₀ N y) ^ 2 ≤
      2 * green T c y₀ N y₀ := by
  set G := green T c y₀ N
  have hG := green_finite T c y₀ N
  have hGnn : ∀ y, 0 ≤ G y := fun y => by
    show 0 ≤ green T c y₀ N y
    rw [green_apply]; exact Finset.sum_nonneg fun n _ => Pop_pow_nonneg y₀ hc n y
  rw [energy_eq hcT hG]
  have hPG : ∀ y, Pop T c G y = G y - dlt y₀ y + (Pop T c ^ (N + 1)) (dlt y₀) y := by
    intro y
    have := congrFun (Pop_green T c y₀ N) y
    simp only [Pi.add_apply] at this
    linarith
  have s1 : Summable fun y => G y * G y := fs_summable hG fun y hy => left_ne_zero_of_mul hy
  have s2 : Summable fun y => G y * dlt y₀ y := fs_summable hG fun y hy => left_ne_zero_of_mul hy
  have s3 : Summable fun y => G y * Pop T c G y := fs_summable hG fun y hy => left_ne_zero_of_mul hy
  have hle : ∑' y, (G y * G y - G y * dlt y₀ y) ≤ ∑' y, G y * Pop T c G y := by
    refine Summable.tsum_le_tsum (fun y => ?_) (s1.sub s2) s3
    rw [hPG]
    nlinarith [hGnn y, Pop_pow_nonneg (T := T) y₀ hc (N + 1) y]
  have hd : ∑' y, G y * dlt y₀ y = G y₀ := by
    have : ∀ y, G y * dlt y₀ y = if y = y₀ then G y else 0 := by
      intro y; unfold dlt; split_ifs <;> simp
    simp only [this]
    rw [tsum_ite_eq]
  rw [Summable.tsum_sub s1 s2, hd] at hle
  have : ∑' y, G y ^ 2 = ∑' y, G y * G y := tsum_congr fun y => sq (G y)
  rw [this]
  linarith

end Energy

/-! ## Recurrence gives functions of small energy -/

section Small

open Classical Function

variable {H Y : Type*} [Group H] [MulAction H Y] {T : Finset H} (hT : ∀ g, g⁻¹ ∈ T ↔ g ∈ T)
  {μ : H → ℝ} {c : ℝ} (hμ : ∀ g, μ g = if g ∈ T then c else 0) (hcT : c * T.card = 1) (y₀ : Y)
include hT hμ hcT

theorem exists_small_energy (hrec : IsRecurrentChain (walkKernel μ) y₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : Y → ℝ, (support b).Finite ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ b y₀ = 1 ∧
      ∀ h ∈ T, ∑' y, (b (h • y) - b y) ^ 2 ≤ ε := by
  have hcard : (0 : ℝ) < T.card := by
    rcases (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcT; exact absurd hcT zero_ne_one
  have hc : 0 < c := by
    by_contra hc; push Not at hc; nlinarith
  obtain ⟨N, hN⟩ := green_unbounded hT hμ y₀ hc.le hrec (max 1 (2 * T.card / ε))
  set G := green T c y₀ N with hGdef
  set s := G y₀
  have hGnn : ∀ y, 0 ≤ G y := fun y => by
    show 0 ≤ green T c y₀ N y
    rw [green_apply]; exact Finset.sum_nonneg fun n _ => Pop_pow_nonneg y₀ hc.le n y
  have hsN : ∑ n ∈ range N, (Pop T c ^ n) (dlt y₀) y₀ ≤ s := by
    show _ ≤ green T c y₀ N y₀
    rw [green_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
      fun n _ _ => Pop_pow_nonneg y₀ hc.le n y₀
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) (hN.trans hsN)
  have hs2 : 2 * T.card / ε ≤ s := le_trans (le_max_right _ _) (hN.trans hsN)
  have hspos : 0 < s := by linarith
  have hE := energy_green_le hcT hc.le y₀ N
  refine ⟨fun y => min 1 (G y / s), ?_, fun y => ⟨?_, min_le_left _ _⟩, ?_, fun h hh => ?_⟩
  · refine (green_finite T c y₀ N).subset fun y hy => ?_
    intro hG0
    apply hy
    simp only [hGdef, hG0, zero_div, min_eq_right zero_le_one]
  · exact le_min zero_le_one (div_nonneg (hGnn y) hspos.le)
  · show min 1 (s / s) = 1
    rw [div_self hspos.ne', min_self]
  · have hfin : (support fun y => (G (h • y) - G y) ^ 2).Finite :=
      ((support_smul_finite (green_finite T c y₀ N) h).union (green_finite T c y₀ N)).subset
        fun y hy => by
          by_contra hn
          simp only [Set.mem_union, mem_support, not_or, not_not] at hn
          apply hy
          simp only [hGdef] at hn ⊢
          rw [hn.1, hn.2]; ring
    have hsum1 : Summable fun y => (G (h • y) - G y) ^ 2 := fs_summable hfin subset_rfl
    have hsum2 : Summable fun y => (min 1 (G (h • y) / s) - min 1 (G y / s)) ^ 2 :=
      fs_summable hfin fun y hy => by
        by_contra hn
        simp only [mem_support, not_not, sq_eq_zero_iff, sub_eq_zero] at hn
        apply hy
        simp only [hn]; ring
    have hpt : ∀ y, (min 1 (G (h • y) / s) - min 1 (G y / s)) ^ 2 ≤
        (G (h • y) - G y) ^ 2 / s ^ 2 := by
      intro y
      have h1 := abs_min_sub_min_le_max (1 : ℝ) (G (h • y) / s) 1 (G y / s)
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), ← sub_div, abs_div,
        abs_of_pos hspos] at h1
      rw [← sq_abs (G (h • y) - G y), ← sq_abs (min _ _ - _)]
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right h1 hspos.le
      rw [div_mul_cancel₀ _ hspos.ne'] at this
      calc |min 1 (G (h • y) / s) - min 1 (G y / s)| ^ 2 * s ^ 2
          = (|min 1 (G (h • y) / s) - min 1 (G y / s)| * s) ^ 2 := by ring
        _ ≤ |G (h • y) - G y| ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    have hsingle : c * ∑' y, (G (h • y) - G y) ^ 2 ≤ 2 * s := by
      refine le_trans ?_ hE
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      exact Finset.single_le_sum (f := fun h => ∑' y, (G (h • y) - G y) ^ 2)
        (fun h _ => tsum_nonneg fun y => sq_nonneg _) hh
    calc ∑' y, (min 1 (G (h • y) / s) - min 1 (G y / s)) ^ 2
        ≤ ∑' y, (G (h • y) - G y) ^ 2 / s ^ 2 := Summable.tsum_le_tsum hpt hsum2 (hsum1.div_const _)
      _ = (∑' y, (G (h • y) - G y) ^ 2) / s ^ 2 := tsum_div_const
      _ ≤ (2 * s * T.card) / s ^ 2 := by
          gcongr
          have : c = (T.card : ℝ)⁻¹ := by field_simp; linarith
          rw [this] at hsingle
          rw [inv_mul_le_iff₀ hcard] at hsingle
          linarith
      _ = 2 * T.card / s := by field_simp
      _ ≤ ε := by
          rw [div_le_iff₀ hspos]
          rw [div_le_iff₀ hε] at hs2
          linarith

end Small

/-! ## Ozawa's product means -/

section Ozawa

open Classical Function

variable {Y : Type*}

/-- `ξ_b(E) = ∏_{x ∈ E} b x`. -/
noncomputable def xi (b : Y → ℝ) (E : Finset Y) : ℝ := ∏ x ∈ E, b x

/-- The normalising constant `Z_b = ∑_E ξ_b(E)^2`. -/
noncomputable def Zb (b : Y → ℝ) : ℝ := ∑' E : Finset Y, xi b E ^ 2

/-- The probability `p_b(S) = ∑_{E ∈ S} ξ_b(E)^2 / Z_b`. -/
noncomputable def pm (b : Y → ℝ) (S : Set (Finset Y)) : ℝ :=
  (∑' E, S.indicator (fun E => xi b E ^ 2) E) / Zb b

theorem xi_eq_zero {b : Y → ℝ} {W : Finset Y} (hW : ∀ y, b y ≠ 0 → y ∈ W) {E : Finset Y}
    (hE : E ∉ W.powerset) : xi b E = 0 := by
  rw [Finset.mem_powerset, Finset.not_subset] at hE
  obtain ⟨x, hx, hxW⟩ := hE
  exact Finset.prod_eq_zero hx (by by_contra h; exact hxW (hW x h))

theorem xi_nonneg {b : Y → ℝ} (hb : ∀ y, 0 ≤ b y) (E : Finset Y) : 0 ≤ xi b E :=
  Finset.prod_nonneg fun x _ => hb x

theorem sum_xi_mul (b b' : Y → ℝ) (W : Finset Y) :
    ∑ E ∈ W.powerset, xi b E * xi b' E = ∏ x ∈ W, (1 + b x * b' x) := by
  have := Finset.prod_add (fun x => b x * b' x) (fun _ => (1 : ℝ)) W
  simp only [Finset.prod_const_one, mul_one] at this
  rw [Finset.prod_congr rfl (fun x _ => add_comm 1 (b x * b' x)), this]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp [xi, Finset.prod_mul_distrib]

variable {b : Y → ℝ} {W : Finset Y} (hW : ∀ y, b y ≠ 0 → y ∈ W)
include hW

theorem Zb_eq : Zb b = ∑ E ∈ W.powerset, xi b E ^ 2 :=
  tsum_eq_sum fun E hE => by rw [xi_eq_zero hW hE]; ring

theorem one_le_Zb : 1 ≤ Zb b := by
  rw [Zb_eq hW]
  have := Finset.single_le_sum (f := fun E => xi b E ^ 2) (fun E _ => sq_nonneg _)
    (Finset.empty_mem_powerset W)
  simpa [xi] using this

theorem summable_ind (S : Set (Finset Y)) :
    Summable fun E => S.indicator (fun E => xi b E ^ 2) E :=
  summable_of_ne_finset_zero (s := W.powerset) fun E hE => by
    simp [Set.indicator, xi_eq_zero hW hE]

theorem pm_union {S S' : Set (Finset Y)} (hd : Disjoint S S') :
    pm b (S ∪ S') = pm b S + pm b S' := by
  unfold pm
  rw [Set.indicator_union_of_disjoint hd, Summable.tsum_add (summable_ind hW S)
    (summable_ind hW S'), add_div]

theorem pm_univ : pm b Set.univ = 1 := by
  unfold pm
  simp only [Set.indicator_univ]
  show Zb b / Zb b = 1
  exact div_self (by linarith [one_le_Zb hW])

theorem pm_nonneg (S : Set (Finset Y)) : 0 ≤ pm b S :=
  div_nonneg (tsum_nonneg fun E => Set.indicator_nonneg (fun E _ => sq_nonneg _) E)
    (by linarith [one_le_Zb hW])

omit hW in
theorem pm_empty : pm b ∅ = 0 := by simp [pm]

theorem pm_le_one (S : Set (Finset Y)) : pm b S ≤ 1 := by
  have h := pm_union hW (disjoint_compl_right (a := S))
  rw [Set.union_compl_self, pm_univ hW] at h
  linarith [pm_nonneg hW Sᶜ]

theorem pm_half {y₀ : Y} (hb1 : b y₀ = 1) : pm b {E | y₀ ∈ E} = 1 / 2 := by
  have hy₀W : y₀ ∈ W := hW y₀ (by rw [hb1]; norm_num)
  set W' := W.erase y₀
  have hWW : W = insert y₀ W' := (Finset.insert_erase hy₀W).symm
  have hnot : y₀ ∉ W' := Finset.notMem_erase y₀ W
  have hins : ∀ E ∈ W'.powerset, xi b (insert y₀ E) = xi b E := by
    intro E hE
    have : y₀ ∉ E := fun h => hnot (Finset.mem_powerset.mp hE h)
    rw [xi, Finset.prod_insert this, hb1, one_mul]; rfl
  have hA : Zb b = 2 * ∑ E ∈ W'.powerset, xi b E ^ 2 := by
    have : ∑ E ∈ W'.powerset, xi b (insert y₀ E) ^ 2 = ∑ E ∈ W'.powerset, xi b E ^ 2 :=
      Finset.sum_congr rfl fun E hE => by rw [hins E hE]
    rw [Zb_eq hW, hWW, Finset.sum_powerset_insert hnot, this]
    ring
  unfold pm
  rw [tsum_eq_sum (s := W.powerset) fun E hE => by simp [Set.indicator, xi_eq_zero hW hE], hWW,
    Finset.sum_powerset_insert hnot, hA]
  have h1 : ∑ E ∈ W'.powerset, {E : Finset Y | y₀ ∈ E}.indicator (fun E => xi b E ^ 2) E = 0 :=
    Finset.sum_eq_zero fun E hE => by
      have : y₀ ∉ E := fun h => hnot (Finset.mem_powerset.mp hE h)
      simp [Set.indicator, this]
  have h2 : ∑ E ∈ W'.powerset,
      {E : Finset Y | y₀ ∈ E}.indicator (fun E => xi b E ^ 2) (insert y₀ E) =
        ∑ E ∈ W'.powerset, xi b E ^ 2 :=
    Finset.sum_congr rfl fun E hE => by simp [Set.indicator, hins E hE]
  rw [h1, h2, zero_add]
  have : 0 < ∑ E ∈ W'.powerset, xi b E ^ 2 := by
    have := Finset.single_le_sum (f := fun E => xi b E ^ 2) (fun E _ => sq_nonneg _)
      (Finset.empty_mem_powerset W')
    have h0 : xi b ∅ ^ 2 = 1 := by simp [xi]
    linarith
  field_simp

end Ozawa

/-! ## Almost invariance of the product means -/

section Trans

open Classical Function

variable {H Y : Type*} [Group H] [MulAction H Y]

/-- Translation of finite sets. -/
def tr (h : H) : Finset Y → Finset Y :=
  fun E => E.map (MulAction.toPerm h : Equiv.Perm Y).toEmbedding

theorem tr_injective (h : H) : Injective (tr (Y := Y) h) := Finset.map_injective _

theorem xi_tr (b : Y → ℝ) (h : H) (E : Finset Y) :
    xi b (tr h E) = xi (fun y => b (h • y)) E := by
  simp [xi, tr, Finset.prod_map]

theorem tsum_tr (h : H) (F : Finset Y → ℝ) : ∑' E, F (tr h E) = ∑' E, F E := by
  have := Equiv.tsum_eq (MulAction.toPerm h : Equiv.Perm Y).finsetCongr F
  simpa [Equiv.finsetCongr_apply, tr] using this

theorem Zb_smul (b : Y → ℝ) (h : H) : Zb (fun y => b (h • y)) = Zb b := by
  unfold Zb
  rw [← tsum_tr h (fun E => xi b E ^ 2)]
  exact tsum_congr fun E => by rw [xi_tr]

theorem pm_tr (b : Y → ℝ) (h : H) (S : Set (Finset Y)) :
    pm b (tr h '' S) = (∑' E, S.indicator (fun E => xi (fun y => b (h • y)) E ^ 2) E) / Zb b := by
  unfold pm
  congr 1
  rw [← tsum_tr h]
  refine tsum_congr fun E => ?_
  by_cases hE : E ∈ S
  · simp [Set.indicator, (tr_injective h).mem_set_image, hE, xi_tr]
  · simp [Set.indicator, (tr_injective h).mem_set_image, hE]

theorem pm_tr_sub_sq {b : Y → ℝ} (hb : ∀ y, 0 ≤ b y) (hfin : (support b).Finite) (h : H)
    (S : Set (Finset Y)) :
    (pm b (tr h '' S) - pm b S) ^ 2 ≤ 4 * ∑' y, (b (h • y) - b y) ^ 2 := by
  set b' : Y → ℝ := fun y => b (h • y) with hb'
  have hb'nn : ∀ y, 0 ≤ b' y := fun y => hb _
  have hfin' := hfin.union (support_smul_finite hfin h)
  set W := hfin'.toFinset
  have hW : ∀ y, b y ≠ 0 → y ∈ W := fun y hy => hfin'.mem_toFinset.mpr (Or.inl hy)
  have hW' : ∀ y, b' y ≠ 0 → y ∈ W := fun y hy => hfin'.mem_toFinset.mpr (Or.inr hy)
  set Z := Zb b
  have hZ1 : 1 ≤ Z := one_le_Zb hW
  have hZW : Z = ∑ E ∈ W.powerset, xi b E * xi b E := by
    show Zb b = _
    rw [Zb_eq hW]; simp only [sq]
  have hZW' : Z = ∑ E ∈ W.powerset, xi b' E * xi b' E := by
    rw [show Z = Zb b' from (Zb_smul b h).symm, Zb_eq hW']; simp only [sq]
  set I := ∑ E ∈ W.powerset, xi b' E * xi b E
  have hI : I = ∏ x ∈ W, (1 + b' x * b x) := sum_xi_mul _ _ _
  have hInn : 0 ≤ I := Finset.sum_nonneg fun E _ => mul_nonneg (xi_nonneg hb'nn E) (xi_nonneg hb E)
  set Δ := ∑' y, (b (h • y) - b y) ^ 2
  have hΔ : Δ = ∑ x ∈ W, (b' x - b x) ^ 2 := by
    refine tsum_eq_sum fun y hy => ?_
    have h1 : b y = 0 := by by_contra hn; exact hy (hW y hn)
    have h2 : b' y = 0 := by by_contra hn; exact hy (hW' y hn)
    simp only [hb'] at h2
    rw [h1, h2]; ring
  -- Z² ≤ I² exp Δ
  have hZsq : Z ^ 2 ≤ I ^ 2 * Real.exp Δ := by
    have e1 : Z ^ 2 = ∏ x ∈ W, ((1 + b x * b x) * (1 + b' x * b' x)) := by
      rw [Finset.prod_mul_distrib, ← sum_xi_mul, ← sum_xi_mul, ← hZW, ← hZW']; ring
    rw [e1, hI, hΔ, Real.exp_sum, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun x _ => mul_nonneg (by nlinarith [mul_self_nonneg (b x)])
      (by nlinarith [mul_self_nonneg (b' x)])) fun x _ => ?_
    have hd := Real.add_one_le_exp ((b' x - b x) ^ 2)
    have hst : 1 ≤ (1 + b' x * b x) ^ 2 := by nlinarith [mul_nonneg (hb'nn x) (hb x)]
    calc (1 + b x * b x) * (1 + b' x * b' x)
        = (1 + b' x * b x) ^ 2 + (b' x - b x) ^ 2 := by ring
      _ ≤ (1 + b' x * b x) ^ 2 * (1 + (b' x - b x) ^ 2) := by nlinarith [sq_nonneg (b' x - b x)]
      _ ≤ (1 + b' x * b x) ^ 2 * Real.exp ((b' x - b x) ^ 2) := by
          gcongr; linarith
  have hΔnn : 0 ≤ Δ := tsum_nonneg fun y => sq_nonneg _
  have hdiff : Z ^ 2 - I ^ 2 ≤ Z ^ 2 * Δ := by
    have h1 : Z ^ 2 * Real.exp (-Δ) ≤ I ^ 2 := by
      have := mul_le_mul_of_nonneg_right hZsq (Real.exp_pos (-Δ)).le
      rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
    have h2 := Real.add_one_le_exp (-Δ)
    nlinarith [sq_nonneg Z]
  -- the variation
  set D := ∑ E ∈ W.powerset, |xi b' E ^ 2 - xi b E ^ 2|
  have hD : D ^ 2 ≤ 4 * (Z ^ 2 - I ^ 2) := by
    have e : D = ∑ E ∈ W.powerset, |xi b' E - xi b E| * (xi b' E + xi b E) := by
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (xi_nonneg hb'nn E) (xi_nonneg hb E)),
        mul_comm]
    rw [e]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
    have e1 : ∑ E ∈ W.powerset, |xi b' E - xi b E| ^ 2 = Z + Z - 2 * I := by
      have : ∀ E, |xi b' E - xi b E| ^ 2 =
          xi b' E * xi b' E + xi b E * xi b E - 2 * (xi b' E * xi b E) := fun E => by
        rw [sq_abs]; ring
      simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← hZW, ← hZW']
    have e2 : ∑ E ∈ W.powerset, (xi b' E + xi b E) ^ 2 = Z + Z + 2 * I := by
      have : ∀ E, (xi b' E + xi b E) ^ 2 =
          xi b' E * xi b' E + xi b E * xi b E + 2 * (xi b' E * xi b E) := fun E => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← hZW, ← hZW']
    rw [e1, e2]; ring
  have hnum : pm b (tr h '' S) - pm b S =
      (∑ E ∈ W.powerset, (S.indicator (fun E => xi b' E ^ 2) E -
        S.indicator (fun E => xi b E ^ 2) E)) / Z := by
    rw [pm_tr, pm, ← sub_div, Finset.sum_sub_distrib]
    congr 2
    · exact tsum_eq_sum fun E hE => by
        have := xi_eq_zero hW' hE
        simp only [hb'] at this
        simp [Set.indicator, this]
    · exact tsum_eq_sum fun E hE => by simp [Set.indicator, xi_eq_zero hW hE]
  have hle : |∑ E ∈ W.powerset, (S.indicator (fun E => xi b' E ^ 2) E -
      S.indicator (fun E => xi b E ^ 2) E)| ≤ D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E _ => ?_)
    by_cases hE : E ∈ S <;> simp [Set.indicator, hE]
  rw [hnum, div_pow, div_le_iff₀ (by positivity), ← sq_abs]
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun E _ => abs_nonneg _
  calc |∑ E ∈ W.powerset, (S.indicator (fun E => xi b' E ^ 2) E -
        S.indicator (fun E => xi b E ^ 2) E)| ^ 2 ≤ D ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ ≤ 4 * (Z ^ 2 - I ^ 2) := hD
    _ ≤ 4 * Δ * Z ^ 2 := by nlinarith

end Trans

/-! ## The invariant mean -/

section Mean

open Classical Function
open scoped ENNReal

variable {H Y : Type*} [Group H] [MulAction H Y]

theorem tr_one (E : Finset Y) : tr (1 : H) E = E := by
  ext x; simp [tr]

theorem tr_mul (g h : H) (E : Finset Y) : tr (g * h) E = tr g (tr h E) := by
  ext x; simp [tr, mul_smul]

theorem exists_invariant_mean {T : Finset H} (hT : ∀ g, g⁻¹ ∈ T ↔ g ∈ T)
    (hgen : Subgroup.closure (T : Set H) = ⊤) {μ : H → ℝ} {c : ℝ}
    (hμ : ∀ g, μ g = if g ∈ T then c else 0) (hcT : c * T.card = 1) (y₀ : Y)
    (hrec : IsRecurrentChain (walkKernel μ) y₀) :
    ∃ m : Set (Finset Y) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
      (∀ (h : H) (S : Set (Finset Y)), m (tr h '' S) = m S) ∧ m {E | y₀ ∈ E} ≠ 0 := by
  have hb := fun n : ℕ => exists_small_energy hT hμ hcT y₀ hrec (1 / ((n : ℝ) + 1))
    (by positivity)
  choose b hbfin hb01 hby₀ hbE using hb
  have hW : ∀ n, ∀ y, b n y ≠ 0 → y ∈ (hbfin n).toFinset := fun n y hy =>
    (hbfin n).mem_toFinset.mpr hy
  let p : ℕ → Set (Finset Y) → ℝ := fun n S => pm (b n) S
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  have hex : ∀ S, ∃ L ∈ Set.Icc (0 : ℝ) 1, Filter.Tendsto (fun n => p n S) U (nhds L) := by
    intro S
    obtain ⟨L, hL, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map fun n => p n S) (by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff]
      exact Filter.mem_map.mpr (Filter.univ_mem' fun n =>
        ⟨pm_nonneg (hW n) S, pm_le_one (hW n) S⟩))
    exact ⟨L, hL, by rw [Ultrafilter.coe_map] at hle; exact hle⟩
  choose L hL01 hL using hex
  have huniq : ∀ S (v : ℝ), (∀ n, p n S = v) → L S = v := fun S v hv =>
    tendsto_nhds_unique (hL S) (tendsto_const_nhds.congr fun n => (hv n).symm)
  have hinvT : ∀ h ∈ T, ∀ S, L (tr h '' S) = L S := by
    intro h hh S
    have h1 : Filter.Tendsto (fun n => (p n (tr h '' S) - p n S) ^ 2) U
        (nhds ((L (tr h '' S) - L S) ^ 2)) := ((hL _).sub (hL S)).pow 2
    have h2 : Filter.Tendsto (fun n : ℕ => 4 * (1 / ((n : ℝ) + 1))) U (nhds (4 * 0)) :=
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat).mono_left hU
    have hle : (L (tr h '' S) - L S) ^ 2 ≤ 4 * 0 :=
      le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall fun n =>
        (pm_tr_sub_sq (fun y => (hb01 n y).1) (hbfin n) h S).trans
          (mul_le_mul_of_nonneg_left (hbE n h hh) (by norm_num)))
    nlinarith [sq_nonneg (L (tr h '' S) - L S)]
  have hinv : ∀ h : H, ∀ S, L (tr h '' S) = L S := by
    intro h
    have hmem : h ∈ Subgroup.closure (T : Set H) := hgen ▸ Subgroup.mem_top h
    induction hmem using Subgroup.closure_induction with
    | mem g hg => exact hinvT g hg
    | one => intro S; simp [tr_one]
    | mul g k _ _ hg hk =>
      intro S
      have : tr (g * k) '' S = tr g '' (tr k '' S) := by
        rw [Set.image_image]; exact Set.image_congr fun E _ => tr_mul g k E
      rw [this, hg, hk]
    | inv g _ hg =>
      intro S
      have : S = tr g '' (tr g⁻¹ '' S) := by
        rw [Set.image_image]
        conv_lhs => rw [← Set.image_id S]
        exact Set.image_congr fun E _ => by rw [← tr_mul, mul_inv_cancel, tr_one]; rfl
      conv_rhs => rw [this]
      rw [hg]
  refine ⟨fun S => ENNReal.ofReal (L S), ⟨?_, fun S S' hd => ?_⟩, ?_, fun h S => ?_, ?_⟩
  · simp only [huniq ∅ 0 fun n => pm_empty, ENNReal.ofReal_zero]
  · show ENNReal.ofReal (L (S ∪ S')) = ENNReal.ofReal (L S) + ENNReal.ofReal (L S')
    rw [tendsto_nhds_unique (hL (S ∪ S')) (((hL S).add (hL S')).congr
        fun n => (pm_union (hW n) hd).symm), ENNReal.ofReal_add (hL01 S).1 (hL01 S').1]
  · simp only [huniq Set.univ 1 fun n => pm_univ (hW n), ENNReal.ofReal_one]
  · simp only [hinv h S]
  · show ENNReal.ofReal (L _) ≠ 0
    rw [huniq _ (1 / 2) fun n => pm_half (hW n) (hby₀ n)]
    norm_num

end Mean

section Copied

open Classical

/-! ## Restricting a Markov chain to an invariant set -/

section Restrict

variable {V : Type*} (P : V → V → ℝ) (O : Set V)

theorem avoidProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) :
    ∀ k (y : V), (y ∉ O → avoidProb P x₀ k y = 0) ∧
      ∀ hy : y ∈ O, avoidProb (fun a b : O => P a b) x₀ k ⟨y, hy⟩ = avoidProb P x₀ k y
  | 0, y => by simp [avoidProb]
  | 1, y => by
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp [avoidProb, this, hP _ x₀.2 y hy]
    · simp only [avoidProb, Subtype.ext_iff]
  | k + 2, y => by
    have ih := avoidProb_restrict hP x₀ (k + 1)
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp only [avoidProb, this, if_false]
      refine (tsum_congr fun z => ?_).trans tsum_zero
      by_cases hz : z ∈ O
      · simp [hP z hz y hy]
      · simp [(ih z).1 hz]
    · simp only [avoidProb, Subtype.ext_iff]
      split_ifs with h
      · rfl
      · rw [← tsum_subtype_eq_of_support_subset (s := O)]
        · exact tsum_congr fun z => by rw [(ih z).2 z.2]
        · intro z hz
          by_contra hzO
          exact hz (by simp [(ih z).1 hzO])

theorem firstReturnProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) (k : ℕ) :
    firstReturnProb (fun a b : O => P a b) x₀ k = firstReturnProb P x₀ k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [firstReturnProb]
    rw [← tsum_subtype_eq_of_support_subset (s := O)]
    · exact tsum_congr fun z => by rw [(avoidProb_restrict P O hP x₀ (k + 1) z).2 z.2]
    · intro z hz
      by_contra hzO
      exact hz (by simp [(avoidProb_restrict P O hP x₀ (k + 1) z).1 hzO])

theorem isRecurrentChain_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O)
    (h : IsRecurrentChain P x₀) : IsRecurrentChain (fun a b : O => P a b) x₀ := by
  unfold IsRecurrentChain at *
  rwa [show firstReturnProb (fun a b : O => P a b) x₀ = firstReturnProb P x₀ from
    funext (firstReturnProb_restrict P O hP x₀)]

end Restrict

/-! ## Recurrence passes to a subgroup acting on one of its orbits -/

section Sub

variable {G X : Type*} [Group G] [MulAction G X]

theorem isRecurrentAction_orbit (h : IsRecurrentAction G X) (H : Subgroup G) (x : X) :
    IsRecurrentAction H (MulAction.orbit H x) := by
  intro μ hμ hsymm x₀
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  set ν : G →₀ ℝ := μ.mapDomain Subtype.val with hν
  have hνH : ∀ g : H, ν g = μ g := fun g => Finsupp.mapDomain_apply hinj μ g
  have hνn : ∀ g : G, g ∉ H → ν g = 0 := fun g hg =>
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨g', rfl⟩; exact hg g'.2)
  have hνp : ThompsonAmenability.IsProbability ν := by
    refine ⟨fun g => ?_, ?_⟩
    · by_cases hg : g ∈ H
      · rw [show g = ((⟨g, hg⟩ : H) : G) from rfl, hνH]; exact hμ.1 _
      · rw [hνn g hg]
    · rw [hν, Finsupp.sum_mapDomain_index_inj hinj]; exact hμ.2
  have hνs : IsSymmetric ν := by
    intro g
    by_cases hg : g ∈ H
    · rw [show g = ((⟨g, hg⟩ : H) : G) from rfl, ← Subgroup.coe_inv, hνH, hνH, hsymm]
    · rw [hνn g hg, hνn g⁻¹ (fun h' => hg (by simpa using H.inv_mem h'))]
  have hrec := h ν hνp hνs (x₀ : X)
  have hP : ∀ a ∈ MulAction.orbit H x, ∀ b ∉ MulAction.orbit H x, walkKernel (ν : G → ℝ) a b = 0 := by
    intro a ha b hb
    unfold walkKernel
    refine (tsum_congr fun g => ?_).trans tsum_zero
    split_ifs with hgb
    · by_cases hg : g ∈ H
      · exfalso; apply hb; rw [← hgb]
        obtain ⟨k, rfl⟩ := ha
        exact ⟨⟨g, hg⟩ * k, show (g * (k : G)) • x = g • ((k : G) • x) from mul_smul _ _ _⟩
      · exact hνn g hg
    · rfl
  have key := isRecurrentChain_restrict (walkKernel (ν : G → ℝ)) _ hP x₀ hrec
  convert key using 1
  funext a b
  unfold walkKernel
  rw [← tsum_subtype_eq_of_support_subset (s := (H : Set G))]
  · refine tsum_congr fun g => ?_
    rw [hνH]
    congr 1
    exact propext ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  · intro g hg
    by_contra hgH
    exact hg (by simp [hνn g hgH])

end Sub

end Copied

end JMMS.IETP42D

namespace JMMS.IETP42D

open IntervalExchange Classical

theorem chk_isExtensivelyAmenable_of_isRecurrentAction {G X : Type*} [Group G] [MulAction G X]
    (h : IsRecurrentAction G X) : IsExtensivelyAmenable G X := by
  refine ((JMMS.isExtensivelyAmenable_tfae (G := G) (X := X)).out 2 0).mp ?_
  intro H hH x
  have : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨S, hS⟩ := Group.FG.out (G := H)
  set T : Finset H := S ∪ S.image (·⁻¹) ∪ {1} with hTdef
  have hTinv : ∀ g, g⁻¹ ∈ T ↔ g ∈ T := by
    intro g
    simp only [hTdef, Finset.mem_union, Finset.mem_image, Finset.mem_singleton, inv_eq_one]
    constructor
    · rintro ((hg | ⟨a, ha, hag⟩) | hg)
      · exact Or.inl (Or.inr ⟨g⁻¹, hg, inv_inv g⟩)
      · exact Or.inl (Or.inl (by rw [← inv_inv g, ← hag, inv_inv]; exact ha))
      · exact Or.inr hg
    · rintro ((hg | ⟨a, ha, hag⟩) | hg)
      · exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
      · exact Or.inl (Or.inl (by rw [← hag, inv_inv]; exact ha))
      · exact Or.inr hg
  have hTne : 0 < T.card := Finset.card_pos.mpr ⟨1, by simp [hTdef]⟩
  set c : ℝ := (T.card : ℝ)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcT : c * T.card = 1 := by rw [hc, inv_mul_cancel₀ (by positivity)]
  let f : H → ℝ := fun g => if g ∈ T then c else 0
  let μ : H →₀ ℝ := Finsupp.onFinset T f (fun g hg => by by_contra hgT; exact hg (by simp [f, hgT]))
  have hμf : ∀ g, μ g = f g := fun g => Finsupp.onFinset_apply
  have hμnn : ∀ g, 0 ≤ μ g := fun g => by rw [hμf]; simp only [f]; split_ifs <;> positivity
  have hμsum : ∑ g ∈ T, μ g = 1 := by
    rw [Finset.sum_congr rfl fun g hg => show μ g = c by rw [hμf]; simp [f, hg]]
    rw [Finset.sum_const, nsmul_eq_mul, hc, mul_inv_cancel₀ (by positivity)]
  have hprob : ThompsonAmenability.IsProbability μ := by
    refine ⟨hμnn, ?_⟩
    rw [Finsupp.sum_of_support_subset μ (Finsupp.support_onFinset_subset) (fun _ w => w)
      (fun _ _ => rfl)]
    exact hμsum
  have hsymm : IsSymmetric μ := by
    intro g; rw [hμf, hμf]; simp only [f, hTinv]
  have hgen : Subgroup.closure (T : Set H) = ⊤ := by
    rw [eq_top_iff, ← hS]
    exact Subgroup.closure_mono (fun g hg => by simp [hTdef, Finset.mem_coe.mp hg])
  let x₀ : MulAction.orbit H x := ⟨x, MulAction.mem_orbit_self x⟩
  have hrec := isRecurrentAction_orbit h H x μ hprob hsymm x₀
  obtain ⟨m, hm, h1, hinv, hx₀⟩ := exists_invariant_mean hTinv hgen (μ := (μ : H → ℝ))
    (fun g => by by_cases hg : g ∈ T <;> simp [hμf, f, hg]) hcT x₀ hrec
  exact ⟨m, hm, h1, hinv, hx₀⟩

end JMMS.IETP42D


namespace JMMS

theorem chk_isExtensivelyAmenable_of_isRecurrentAction {G X : Type*} [Group G] [MulAction G X]
    (h : IsRecurrentAction G X) : IsExtensivelyAmenable G X :=
  IETP42D.chk_isExtensivelyAmenable_of_isRecurrentAction h

end JMMS
end

open IntervalExchange
open JMMS in
theorem solution {G X : Type*} [Group G] [MulAction G X]
    (h : IsRecurrentAction G X) : IsExtensivelyAmenable G X :=
  JMMS.chk_isExtensivelyAmenable_of_isRecurrentAction h
