-- Prove2me | solution 1 for NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5e7daf17-5c5a-5814-8f01-6f365d6df58b

import Mathlib.NumberTheory.NumberField.AdeleRing
import Definitions.Def_AutomorphicForm_SiegelReduction
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact

set_option autoImplicit false

open scoped NumberField

open NumberField IsDedekindDomain

noncomputable section

namespace AdelicBoxCount

open AutomorphicForm.SiegelReduction NumberField.InfinitePlace

variable (K : Type) [Field K] [NumberField K]

private def boxCell (w : InfinitePlace K) (x : K) : ℤ × ℤ :=
  (⌊2 * (w.embedding x).re⌋, ⌊2 * (w.embedding x).im⌋)

private theorem apply_sub_lt_one_of_cell_eq {w : InfinitePlace K} {x y : K}
    (h : boxCell K w x = boxCell K w y) : w (x - y) < 1 := by
  have h1 : ⌊2 * (w.embedding x).re⌋ = ⌊2 * (w.embedding y).re⌋ := congrArg Prod.fst h
  have h2 : ⌊2 * (w.embedding x).im⌋ = ⌊2 * (w.embedding y).im⌋ := congrArg Prod.snd h
  have hre := Int.abs_sub_lt_one_of_floor_eq_floor h1
  have him := Int.abs_sub_lt_one_of_floor_eq_floor h2
  rw [← mul_sub, abs_mul, abs_two] at hre him
  rw [← norm_embedding_eq, map_sub]
  calc ‖w.embedding x - w.embedding y‖
      ≤ |(w.embedding x - w.embedding y).re| + |(w.embedding x - w.embedding y).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(w.embedding x).re - (w.embedding y).re| + |(w.embedding x).im - (w.embedding y).im| := by
        rw [Complex.sub_re, Complex.sub_im]
    _ < 1 := by linarith

private theorem eq_of_forall_cell_eq {x y : K} (hx : x ∈ (algebraMap (𝓞 K) K).range)
    (hy : y ∈ (algebraMap (𝓞 K) K).range) (h : ∀ w : InfinitePlace K, boxCell K w x = boxCell K w y) :
    x = y := by
  by_contra hne
  have hnorm : (1 : ℝ) ≤ |(Algebra.norm ℚ (x - y) : ℝ)| :=
    one_le_abs_norm_of_mem_range K (sub_mem hx hy) (sub_ne_zero.2 hne)
  have hprod := prod_eq_abs_norm (x - y)
  rw [Rat.cast_abs] at hprod
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hlt : ∏ w : InfinitePlace K, w (x - y) ^ w.mult < 1 := by
    classical
    rw [← Finset.mul_prod_erase Finset.univ (fun w : InfinitePlace K => w (x - y) ^ w.mult)
      (Finset.mem_univ w₀)]
    refine mul_lt_one_of_nonneg_of_lt_one_left (pow_nonneg (apply_nonneg w₀ _) _) ?_ ?_
    · exact pow_lt_one₀ (apply_nonneg w₀ _) (apply_sub_lt_one_of_cell_eq K (h w₀))
        (by unfold mult; split_ifs <;> norm_num)
    · refine Finset.prod_le_one (fun w _ => pow_nonneg (apply_nonneg w _) _) fun w _ => ?_
      exact pow_le_one₀ (apply_nonneg w _) (apply_sub_lt_one_of_cell_eq K (h w)).le
  rw [hprod] at hlt
  exact absurd (hnorm.trans_lt hlt) (lt_irrefl _)

omit [NumberField K] in

private theorem im_embedding_eq_zero {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    (w.embedding x).im = 0 := by
  have hφ : ComplexEmbedding.IsReal w.embedding := isReal_iff.1 hw
  rw [← hφ.coe_embedding_apply, Complex.ofReal_im]

open Classical in

private def cellBox (w : InfinitePlace K) (r : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋ ×ˢ
    (if w.IsReal then {0} else Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋)

private theorem floor_mem_Icc {t r : ℝ} (ht : |t| ≤ r) :
    ⌊2 * t⌋ ∈ Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋ := by
  obtain ⟨h1, h2⟩ := abs_le.1 ht
  rw [Finset.mem_Icc]
  constructor
  · have h3 : ⌊2 * (-r)⌋ ≤ ⌊2 * t⌋ := Int.floor_le_floor (by linarith)
    have h4 : ⌊2 * (-r)⌋ = -⌈2 * r⌉ := by rw [mul_neg, Int.floor_neg]
    have h5 := Int.ceil_le_floor_add_one (2 * r)
    omega
  · exact Int.floor_le_floor (by linarith)

omit [NumberField K] in

private theorem cell_mem_cellBox (w : InfinitePlace K) {r : ℝ} {x : K} (hx : w x ≤ r) :
    boxCell K w x ∈ cellBox K w r := by
  have hnorm : ‖w.embedding x‖ ≤ r := by rw [norm_embedding_eq]; exact hx
  unfold boxCell cellBox
  rw [Finset.mem_product]
  refine ⟨floor_mem_Icc ((Complex.abs_re_le_norm _).trans hnorm), ?_⟩
  split_ifs with hw
  · rw [im_embedding_eq_zero K hw x, mul_zero, Int.floor_zero]
    exact Finset.mem_singleton_self 0
  · exact floor_mem_Icc ((Complex.abs_im_le_norm _).trans hnorm)

omit [NumberField K] in

private theorem card_cellBox_le (w : InfinitePlace K) (r : ℝ) :
    ((cellBox K w r).card : ℝ) ≤ (6 * max 1 r) ^ w.mult := by
  have hI : ((Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋).card : ℝ) ≤ 6 * max 1 r := by
    rw [Int.card_Icc]
    have h1 : ((2 * ⌊2 * r⌋ + 2 : ℤ) : ℝ) ≤ 6 * max 1 r := by
      have h2 : ((⌊2 * r⌋ : ℤ) : ℝ) ≤ 2 * r := Int.floor_le _
      have h3 : r ≤ max 1 r := le_max_right _ _
      have h4 : (1 : ℝ) ≤ max 1 r := le_max_left _ _
      push_cast
      linarith
    have h5 : (0 : ℝ) ≤ 6 * max 1 r := by positivity
    have h6 : (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℤ) : ℝ)
        = max (((2 * ⌊2 * r⌋ + 2 : ℤ) : ℝ)) 0 := by
      rw [Int.toNat_eq_max, Int.cast_max, Int.cast_zero]
      congr 2
      ring
    have h7 : (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℕ) : ℝ)
        = (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℤ) : ℝ) := (Int.cast_natCast _).symm
    rw [h7, h6]
    exact max_le h1 h5
  have h0 : (0 : ℝ) ≤ ((Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋).card : ℝ) := Nat.cast_nonneg _
  unfold cellBox
  rw [Finset.card_product, Nat.cast_mul]
  split_ifs with hw
  · have hm : w.mult = 1 := mult_isReal ⟨w, hw⟩
    rw [hm, pow_one, Finset.card_singleton, Nat.cast_one, mul_one]
    exact hI
  · have hm : w.mult = 2 := mult_isComplex ⟨w, not_isReal_iff_isComplex.1 hw⟩
    rw [hm, pow_two]
    exact mul_le_mul hI hI h0 (by positivity)

private theorem max_one_mul_le {a b : ℝ} (ha : 0 ≤ a) : max 1 (a * b) ≤ max 1 a * max 1 b := by
  have h1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  refine max_le (one_le_mul_of_one_le_of_one_le h1 h2) ?_
  rcases le_or_gt 0 b with hb | hb
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hb (zero_le_one.trans h1)
  · calc a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb.le
      _ ≤ 1 := zero_le_one
      _ ≤ max 1 a * max 1 b := one_le_mul_of_one_le_of_one_le h1 h2

omit [NumberField K] in

private theorem card_cellBox_mul_le (w : InfinitePlace K) {c : ℝ} (hc : 0 ≤ c) (R : ℝ) :
    ((cellBox K w (c * R)).card : ℝ) ≤ (6 * max 1 c) ^ w.mult * max 1 R ^ w.mult := by
  refine (card_cellBox_le K w (c * R)).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (max_one_mul_le hc) (by norm_num)

private theorem apply_sub_le (a : AdeleRing (𝓞 K) K) {R : InfinitePlace K → ℝ} {k k' : K}
    (hk : ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w)
    (hk' : ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k' - a).1 w‖ ≤ R w)
    (w : InfinitePlace K) : w (k - k') ≤ 2 * R w := by
  have e : algebraMap K w.Completion (k - k')
      = (algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w
        - (algebraMap K (AdeleRing (𝓞 K) K) k' - a).1 w := by
    rw [map_sub]
    show algebraMap K w.Completion k - algebraMap K w.Completion k'
      = (algebraMap K w.Completion k - a.1 w) - (algebraMap K w.Completion k' - a.1 w)
    ring
  have hn : ‖algebraMap K w.Completion (k - k')‖ = w (k - k') := norm_coe_completion K w (k - k')
  rw [← hn, e, two_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hk w) (hk' w))

private theorem mul_sub_mem_range (a : AdeleRing (𝓞 K) K) {B : Set (FiniteAdeleRing (𝓞 K) K)}
    {d : 𝓞 K}
    (hd : ∀ y ∈ (fun p : FiniteAdeleRing (𝓞 K) K × FiniteAdeleRing (𝓞 K) K => p.1 - p.2) '' (B ×ˢ B),
      ∀ v : HeightOneSpectrum (𝓞 K),
        (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d * y) v ∈ v.adicCompletionIntegers K)
    {k k' : K} (hk : (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B)
    (hk' : (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2 ∈ B) :
    algebraMap (𝓞 K) K d * (k - k') ∈ (algebraMap (𝓞 K) K).range := by
  refine mem_range_of_coe_mem_integralFiniteAdeles K fun v => ?_
  have e : algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d * (k - k'))
      = algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d
        * ((algebraMap K (AdeleRing (𝓞 K) K) k - a).2 - (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, map_sub]
    congr 1
    show algebraMap K (FiniteAdeleRing (𝓞 K) K) k - algebraMap K (FiniteAdeleRing (𝓞 K) K) k'
      = (algebraMap K (FiniteAdeleRing (𝓞 K) K) k - a.2) - (algebraMap K (FiniteAdeleRing (𝓞 K) K) k' - a.2)
    ring
  rw [e]
  exact hd _ ⟨((algebraMap K (AdeleRing (𝓞 K) K) k - a).2, (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2),
    Set.mk_mem_prod hk hk', rfl⟩ v

end AdelicBoxCount

end

open AdelicBoxCount NumberField IsDedekindDomain in

theorem solution
    (K : Type) [Field K] [NumberField K]
    {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ (a : NumberField.AdeleRing (𝓞 K) K) (R : NumberField.InfinitePlace K → ℝ),
      ∃ s : Finset K,
        (∀ k : K, (algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).2 ∈ B →
          (∀ w : NumberField.InfinitePlace K,
            ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w) → k ∈ s) ∧
        (s.card : ℝ) ≤ M * ∏ w : NumberField.InfinitePlace K, max 1 (R w) ^ w.mult := by
  classical

  have hBB : IsCompact ((fun p : FiniteAdeleRing (𝓞 K) K × FiniteAdeleRing (𝓞 K) K => p.1 - p.2)
      '' (B ×ˢ B)) :=
    (hB.prod hB).image (continuous_fst.sub continuous_snd)
  obtain ⟨d, hd0, hd⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
      (𝓞 K) K hBB
  have hc0 : algebraMap (𝓞 K) K d ≠ 0 := fun h => hd0 (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  have hcnn : ∀ w : InfinitePlace K, (0 : ℝ) ≤ 2 * w (algebraMap (𝓞 K) K d) :=
    fun w => by positivity
  refine ⟨∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult, fun a R => ?_⟩
  have hMnn : (0 : ℝ) ≤ ∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity
  have hPnn : (0 : ℝ) ≤ ∏ w : InfinitePlace K, max 1 (R w) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity

  set S : Set K := {k | (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B ∧
    ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w} with hSdef
  by_cases hS : S.Nonempty
  swap
  · refine ⟨∅, fun k h1 h2 => (hS ⟨k, h1, h2⟩).elim, ?_⟩
    rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hMnn hPnn
  obtain ⟨k₀, hk₀⟩ := hS

  set f : K → (InfinitePlace K → ℤ × ℤ) :=
    fun k w => boxCell K w (algebraMap (𝓞 K) K d * (k - k₀)) with hfdef
  set T : Finset (InfinitePlace K → ℤ × ℤ) :=
    Fintype.piFinset fun w : InfinitePlace K => cellBox K w (2 * w (algebraMap (𝓞 K) K d) * R w)
    with hTdef
  have hmaps : ∀ k ∈ S, f k ∈ T := by
    intro k hk
    rw [hTdef, Fintype.mem_piFinset]
    intro w
    refine cell_mem_cellBox K w ?_
    rw [map_mul]
    calc w (algebraMap (𝓞 K) K d) * w (k - k₀)
        ≤ w (algebraMap (𝓞 K) K d) * (2 * R w) :=
          mul_le_mul_of_nonneg_left (apply_sub_le K a hk.2 hk₀.2 w) (apply_nonneg w _)
      _ = 2 * w (algebraMap (𝓞 K) K d) * R w := by ring
  have hinj : S.InjOn f := by
    intro k hk k' hk' hkk'
    have h1 := mul_sub_mem_range K a hd hk.1 hk₀.1
    have h2 := mul_sub_mem_range K a hd hk'.1 hk₀.1
    have h3 := eq_of_forall_cell_eq K h1 h2 fun w => congrFun hkk' w
    have h4 := mul_left_cancel₀ hc0 h3
    exact sub_left_inj.1 h4
  have hfin : S.Finite :=
    Set.Finite.of_finite_image (T.finite_toSet.subset (by
      rintro _ ⟨k, hk, rfl⟩
      exact hmaps k hk)) hinj
  refine ⟨hfin.toFinset, fun k h1 h2 => hfin.mem_toFinset.2 ⟨h1, h2⟩, ?_⟩
  have hcard : hfin.toFinset.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn f (fun k hk => hmaps k (hfin.mem_toFinset.1 hk)) ?_
    intro k hk k' hk' h
    exact hinj (hfin.mem_toFinset.1 hk) (hfin.mem_toFinset.1 hk') h
  calc (hfin.toFinset.card : ℝ) ≤ T.card := Nat.cast_le.2 hcard
    _ = ∏ w : InfinitePlace K, ((cellBox K w (2 * w (algebraMap (𝓞 K) K d) * R w)).card : ℝ) := by
        rw [hTdef, Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ w : InfinitePlace K,
          (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult * max 1 (R w) ^ w.mult :=
        Finset.prod_le_prod (fun w _ => Nat.cast_nonneg _)
          fun w _ => card_cellBox_mul_le K w (hcnn w) (R w)
    _ = (∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult)
          * ∏ w : InfinitePlace K, max 1 (R w) ^ w.mult := Finset.prod_mul_distrib

end S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact (solution)
