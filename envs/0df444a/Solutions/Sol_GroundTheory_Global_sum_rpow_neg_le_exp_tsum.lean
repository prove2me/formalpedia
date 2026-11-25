-- Prove2me | solution 1 for GroundTheory.Global.sum_rpow_neg_le_exp_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:37.282697+00:00
-- url     : https://prove2.me/submissions/26d610bc-68b9-4d75-ae84-86812e994c76

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_geom_sum_le_exp
import Theorems.Thm_GroundTheory_Global_rpow_neg_absNorm_le_half
import Theorems.Thm_GroundTheory_Global_absNorm_eq_prod_count
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by
  classical
  set x : Ideal (𝓞 K) → ℝ := fun p => (absNorm p : ℝ) ^ (-s) with hxdef
  have hx0 : ∀ p, 0 ≤ x p := fun p => by positivity
  have hs0 : -s ≠ 0 := by intro h; linarith
  have hbot : x ⊥ = 0 := by simp [x, Real.zero_rpow hs0]
  set nf := fun I : Ideal (𝓞 K) => UniqueFactorizationMonoid.normalizedFactors I with hnf
  set T' := T.erase ⊥ with hT'
  set P : Finset (Ideal (𝓞 K)) := T'.biUnion fun I => (nf I).toFinset with hP
  set M : ℕ := T'.sup (fun I => Multiset.card (nf I)) + 1 with hM
  have hPprime : ∀ p ∈ P, Prime p := by
    intro p hp
    obtain ⟨I, _, hpI⟩ := Finset.mem_biUnion.mp hp
    exact UniqueFactorizationMonoid.prime_of_normalized_factor p (Multiset.mem_toFinset.mp hpI)
  have hxI : ∀ I ∈ T', x I = ∏ p : P, x p.1 ^ (nf I).count p.1 := by
    intro I hI
    have hI0 : I ≠ ⊥ := (Finset.mem_erase.mp hI).1
    rw [Finset.prod_coe_sort P (fun p => x p ^ (nf I).count p)]
    simp only [x]
    rw [absNorm_eq_prod_count hI0 P (Finset.subset_biUnion_of_mem (fun I => (nf I).toFinset) hI),
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  let E : Ideal (𝓞 K) → (P → ℕ) := fun I p => (nf I).count p.1
  have hE : Set.InjOn E T' := by
    intro I hI J hJ hIJ
    have hI0 : I ≠ ⊥ := (Finset.mem_erase.mp hI).1
    have hJ0 : J ≠ ⊥ := (Finset.mem_erase.mp hJ).1
    have hnfeq : nf I = nf J := by
      ext q
      by_cases hq : q ∈ P
      · exact congrFun hIJ ⟨q, hq⟩
      · have hqI : q ∉ nf I := fun h =>
          hq (Finset.mem_biUnion.mpr ⟨I, hI, Multiset.mem_toFinset.mpr h⟩)
        have hqJ : q ∉ nf J := fun h =>
          hq (Finset.mem_biUnion.mpr ⟨J, hJ, Multiset.mem_toFinset.mpr h⟩)
        rw [Multiset.count_eq_zero.mpr hqI, Multiset.count_eq_zero.mpr hqJ]
    rw [← associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI0),
      ← associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hJ0)]
    exact congrArg Multiset.prod hnfeq
  have hEM : ∀ I ∈ T', E I ∈ Fintype.piFinset (fun _ : P => Finset.range M) := by
    intro I hI
    refine Fintype.mem_piFinset.mpr fun p => Finset.mem_range.mpr ?_
    exact Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans
      (Finset.le_sup (f := fun I => Multiset.card (nf I)) hI))
  have hxhalf : ∀ p : P, x p.1 ≤ 1 / 2 := fun p =>
    rpow_neg_absNorm_le_half (hPprime p.1 p.2) hs.le
  let ι : P → HeightOneSpectrum (𝓞 K) := fun p => heightOneOfPrime (hPprime p.1 p.2)
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  have hsum : Summable fun w : HeightOneSpectrum (𝓞 K) =>
      (absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2 := by
    have h1 := summable_absNorm_rpow_neg (L := K) hs
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun w => ?_) (h1.mul_left 3)
    have hw0 : (0 : ℝ) ≤ (absNorm w.asIdeal : ℝ) ^ (-s) := by positivity
    have hw1 := rpow_neg_absNorm_le_half w.prime hs.le
    nlinarith
  calc ∑ I ∈ T, x I = ∑ I ∈ T', x I := (Finset.sum_erase (f := x) T hbot).symm
    _ = ∑ I ∈ T', ∏ p : P, x p.1 ^ E I p := Finset.sum_congr rfl hxI
    _ = ∑ e ∈ T'.image E, ∏ p : P, x p.1 ^ e p :=
        (Finset.sum_image (f := fun e : P → ℕ => ∏ p : P, x p.1 ^ e p) hE).symm
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : P => Finset.range M), ∏ p : P, x p.1 ^ e p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he => ?_)
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg (hx0 _) _)
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp he
        exact hEM I hI
    _ = ∏ p : P, ∑ k ∈ Finset.range M, x p.1 ^ k :=
        (Finset.prod_univ_sum (fun _ : P => Finset.range M) (fun p k => x p.1 ^ k)).symm
    _ ≤ ∏ p : P, Real.exp (x p.1 + 2 * x p.1 ^ 2) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (hx0 _) _)
          (fun p _ => geom_sum_le_exp (hx0 _) (hxhalf p) M)
    _ = Real.exp (∑ p : P, (x p.1 + 2 * x p.1 ^ 2)) :=
        (Real.exp_sum Finset.univ fun p : P => x p.1 + 2 * x p.1 ^ 2).symm
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr ?_
        calc ∑ p : P, (x p.1 + 2 * x p.1 ^ 2)
            = ∑ w ∈ Finset.univ.image ι, ((absNorm w.asIdeal : ℝ) ^ (-s) +
                2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2) :=
              (Finset.sum_image (f := fun w : HeightOneSpectrum (𝓞 K) =>
                (absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)
                (s := Finset.univ) (g := ι) (fun a _ b _ h => hι h)).symm
          _ ≤ _ := hsum.sum_le_tsum _ (fun _ _ => by positivity)
end GroundTheory.Global
