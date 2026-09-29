-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b131bc18-a65e-549b-9b5f-2f7b737a5d17

import Definitions.Def_LanglandsTunnell_JLData
import Theorems.Thm_LanglandsTunnell_Converse_sPart_shift
import Theorems.Thm_LanglandsTunnell_Converse_isNicePinned_sPart_shift
import Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg
import Theorems.Thm_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_jlData_isJLNice_of_forall_isNicePinned

set_option autoImplicit false

section

open LanglandsTunnell LanglandsTunnell.Converse

open NumberField IsDedekindDomain AutomorphicForm

section Summability

private theorem aux_summable_pi_pow {ι : Type} [Fintype ι] (r : ι → ℝ) (h0 : ∀ i, 0 ≤ r i)
    (h1 : ∀ i, r i < 1) : Summable fun m : ι → ℕ => ∏ i, r i ^ m i := by
  classical
  refine summable_of_sum_le (c := ∏ i, (1 - r i)⁻¹)
    (fun m => Finset.prod_nonneg fun i _ => pow_nonneg (h0 i) _) fun u => ?_
  show ∑ m ∈ u, ∏ i, r i ^ m i ≤ ∏ i, (1 - r i)⁻¹
  calc ∑ m ∈ u, ∏ i, r i ^ m i
      ≤ ∑ m ∈ Fintype.piFinset (fun i => u.image fun m => m i), ∏ i, r i ^ m i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ =>
          Finset.prod_nonneg fun i _ => pow_nonneg (h0 i) _
        intro m hm
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem (fun m => m i) hm
    _ = ∏ i, ∑ j ∈ u.image (fun m => m i), r i ^ j :=
        (Finset.prod_univ_sum (fun i => u.image fun m => m i) (fun i j => r i ^ j)).symm
    _ ≤ ∏ i, (1 - r i)⁻¹ := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg (h0 i) _)
          fun i _ => ?_
        rw [← tsum_geometric_of_lt_one (h0 i) (h1 i)]
        exact (summable_geometric_of_lt_one (h0 i) (h1 i)).sum_le_tsum _ fun j _ => pow_nonneg (h0 i) _

private theorem aux_summable_mul_prod_zpow {ι : Type} [Fintype ι] (x : ι → ℂ) (hx0 : ∀ i, x i ≠ 0)
    (hx1 : ∀ i, ‖x i‖ < 1) (A : (ι → ℤ) → ℂ) (C : ℝ) (hbd : ∀ n, ‖A n‖ ≤ C) (n₀ : ι → ℤ)
    (hsupp : ∀ n : ι → ℤ, (∃ i, n i < n₀ i) → A n = 0) :
    Summable fun n : ι → ℤ => A n * ∏ i, x i ^ n i := by
  have hinj : Function.Injective fun (m : ι → ℕ) (i : ι) => n₀ i + (m i : ℤ) := by
    intro m m' h
    funext i
    have h' : n₀ i + (m i : ℤ) = n₀ i + (m' i : ℤ) := congrFun h i
    exact_mod_cast add_left_cancel h'
  have hvan : ∀ n ∉ Set.range (fun (m : ι → ℕ) (i : ι) => n₀ i + (m i : ℤ)),
      A n * ∏ i, x i ^ n i = 0 := by
    intro n hn
    rw [hsupp n, zero_mul]
    by_contra hlt
    simp only [not_exists, not_lt] at hlt
    refine hn ⟨fun i => (n i - n₀ i).toNat, funext fun i => ?_⟩
    show n₀ i + (((n i - n₀ i).toNat : ℕ) : ℤ) = n i
    rw [Int.toNat_of_nonneg (by linarith [hlt i])]
    ring
  refine (hinj.summable_iff hvan).1 ?_
  have hgeo : Summable fun m : ι → ℕ => (C * ∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i :=
    (aux_summable_pi_pow (fun i => ‖x i‖) (fun i => norm_nonneg _) hx1).mul_left _
  refine Summable.of_norm_bounded hgeo fun m => ?_
  show ‖A (fun i => n₀ i + (m i : ℤ)) * ∏ i, x i ^ (n₀ i + (m i : ℤ))‖ ≤
    (C * ∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i
  rw [norm_mul, norm_prod]
  simp only [norm_zpow]
  have hsplit : ∀ i, ‖x i‖ ^ (n₀ i + (m i : ℤ)) = ‖x i‖ ^ n₀ i * ‖x i‖ ^ m i := fun i => by
    rw [zpow_add₀ (norm_ne_zero_iff.2 (hx0 i)), zpow_natCast]
  simp only [hsplit, Finset.prod_mul_distrib]
  have hprod : 0 ≤ (∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i :=
    mul_nonneg (Finset.prod_nonneg fun i _ => zpow_nonneg (norm_nonneg _) _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
  calc ‖A fun i => n₀ i + (m i : ℤ)‖ * ((∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i)
      ≤ C * ((∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i) := mul_le_mul_of_nonneg_right (hbd _) hprod
    _ = (C * ∏ i, ‖x i‖ ^ n₀ i) * ∏ i, ‖x i‖ ^ m i := by ring

variable (K : Type) [Field K] [NumberField K]

private theorem aux_one_lt_absNorm (S : Finset (HeightOneSpectrum (𝓞 K))) (v : ↥S) :
    1 < Ideal.absNorm v.1.asIdeal := by
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := fun h => v.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := fun h => v.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem aux_summable_sPart_family (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (C : ℝ) (hbd : ∀ n, ‖A n‖ ≤ C) (n₀ : ↥S → ℤ)
    (hsupp : ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0)
    (hμ : ∀ v : ↥S, ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1) (s : ℂ) (hs : 1 / 2 < s.re) :
    Summable fun n : ↥S → ℤ => A n * ∏ v : ↥S,
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
  have hqpos : ∀ v : ↥S, 0 < Ideal.absNorm v.1.asIdeal := fun v =>
    zero_lt_one.trans (aux_one_lt_absNorm K S v)
  have hq : ∀ v : ↥S, (1 : ℝ) < ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := fun v => by
    exact_mod_cast aux_one_lt_absNorm K S v
  have hre : ((1 : ℂ) / 2 - s).re = 1 / 2 - s.re := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  refine aux_summable_mul_prod_zpow
    (fun v : ↥S => ((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s))
    (fun v => mul_ne_zero (Units.ne_zero _) fun h0 =>
      absurd ((Complex.cpow_eq_zero_iff _ _).1 h0).1 (by exact_mod_cast (hqpos v).ne'))
    (fun v => ?_) A C hbd n₀ hsupp
  show ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ < 1
  rw [norm_mul, hμ v, one_mul, Complex.norm_natCast_cpow_of_pos (hqpos v), hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (hq v) (by linarith)

end Summability

open NumberField IsDedekindDomain AutomorphicForm

section Moduli

variable (K : Type) [Field K] [NumberField K]

private theorem aux_one_lt_absNorm' (v : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem aux_norm_absNorm_cpow_lt_one (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ < 1 := by
  have hqpos : 0 < Ideal.absNorm v.asIdeal := zero_lt_one.trans (aux_one_lt_absNorm' K v)
  have hq : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast aux_one_lt_absNorm' K v
  have hre : ((1 : ℂ) / 2 - s).re = 1 / 2 - s.re := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  rw [Complex.norm_natCast_cpow_of_pos hqpos, hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

private theorem aux_norm_sVariable_lt_one (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖((μ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖
      < 1 := by
  rw [norm_mul, hμ.2.2 (uniformizerIdele K v), one_mul]
  exact aux_norm_absNorm_cpow_lt_one K v s hs

private theorem aux_norm_sVariableDual_lt_one (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖(((μ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖
      < 1 := by
  rw [norm_mul, ← map_inv μ, hμ.2.2 (uniformizerIdele K v)⁻¹, one_mul]
  exact aux_norm_absNorm_cpow_lt_one K v s hs

end Moduli

open IsDedekindDomain NumberField

section Levels

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem aux_eq_one_of_forall_norm_pow_sub_one_le (g : ℂ) (h : ∀ n : ℕ, ‖g ^ n - 1‖ ≤ 1 / 2) :
    g = 1 := by
  by_contra hg
  have hδ : 0 < ‖g - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hg)
  have key : ∀ j : ℕ, (3 / 2 : ℝ) ^ j * ‖g - 1‖ ≤ ‖g ^ (2 ^ j) - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : g ^ (2 ^ (j + 1)) - 1 = (g ^ (2 ^ j) - 1) * (g ^ (2 ^ j) + 1) := by
        rw [pow_succ, pow_mul]
        ring
      have h2 : (3 / 2 : ℝ) ≤ ‖g ^ (2 ^ j) + 1‖ := by
        have h3 : ‖1 - g ^ (2 ^ j)‖ ≤ 1 / 2 := by
          rw [norm_sub_rev]
          exact h _
        have h4 : ‖(2 : ℂ)‖ - ‖1 - g ^ (2 ^ j)‖ ≤ ‖(2 : ℂ) - (1 - g ^ (2 ^ j))‖ :=
          norm_sub_norm_le _ _
        have h5 : (2 : ℂ) - (1 - g ^ (2 ^ j)) = g ^ (2 ^ j) + 1 := by ring
        have h6 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h5, h6] at h4
        linarith
      calc (3 / 2 : ℝ) ^ (j + 1) * ‖g - 1‖ = (3 / 2) * ((3 / 2 : ℝ) ^ j * ‖g - 1‖) := by ring
        _ ≤ (3 / 2) * ‖g ^ (2 ^ j) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ ‖g ^ (2 ^ j) + 1‖ * ‖g ^ (2 ^ j) - 1‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖g ^ (2 ^ (j + 1)) - 1‖ := by rw [h1, norm_mul, mul_comm]
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / ‖g - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h7 : 1 / ‖g - 1‖ * ‖g - 1‖ < (3 / 2 : ℝ) ^ j * ‖g - 1‖ := mul_lt_mul_of_pos_right hj hδ
  rw [one_div_mul_cancel hδ.ne'] at h7
  have h8 : (3 / 2 : ℝ) ^ j * ‖g - 1‖ ≤ 1 / 2 := (key j).trans (h _)
  linarith

private theorem aux_valuation_pow_sub_one_le (u : v.adicCompletion K) (g : WithZero (Multiplicative ℤ))
    (hg : g < 1) (hu : Valued.v (u - 1) ≤ g) (n : ℕ) : Valued.v (u ^ n - 1) ≤ g := by
  have hu1 : Valued.v u = 1 := by
    have h := Valuation.map_one_add_of_lt (Valued.v) (hu.trans_lt hg)
    simpa using h
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : u ^ (n + 1) - 1 = u ^ n * (u - 1) + (u ^ n - 1) := by ring
    rw [hsplit]
    refine (Valued.v).map_add_le ?_ ih
    rw [map_mul, map_pow, hu1, one_pow, one_mul]
    exact hu

private theorem aux_exists_level_of_continuous (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ u : (v.adicCompletion K)ˣ,
      Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) → χ u = 1 := by

  have hcont : Continuous fun u : (v.adicCompletion K)ˣ => ((χ u : ℂˣ) : ℂ) :=
    Units.continuous_val.comp hχ
  have hball : {u : (v.adicCompletion K)ˣ | ((χ u : ℂˣ) : ℂ) ∈ Metric.ball (1 : ℂ) (1 / 2)} ∈
      nhds (1 : (v.adicCompletion K)ˣ) := by
    exact (hcont.continuousAt (x := 1)).preimage_mem_nhds
      (by simpa using Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))

  rw [Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hball
  obtain ⟨V, hV, hVsub⟩ := hball
  rw [Units.val_one, Valued.mem_nhds] at hV
  obtain ⟨γ, hγ⟩ := hV

  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hgdef
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := congrArg MonoidWithZeroHom.ValueGroup₀.embedding (Units.mul_inv γ)
    simp only [map_mul, map_one, ← hgdef, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨(-(WithZero.log g)).toNat + 1, by omega, fun u hu => ?_⟩

  have hlt : ∀ n : ℕ, Valued.v (((u : v.adicCompletion K) ^ n) - 1) < g := by
    intro n
    have hm : WithZero.exp (-(((-(WithZero.log g)).toNat + 1 : ℕ) : ℤ)) < g := by
      conv_rhs => rw [← WithZero.exp_log hg0]
      rw [WithZero.exp_lt_exp]
      omega
    refine (aux_valuation_pow_sub_one_le K v u _ ?_ hu n).trans_lt hm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hpow : ∀ n : ℕ, ‖((χ u : ℂˣ) : ℂ) ^ n - 1‖ ≤ 1 / 2 := by
    intro n
    have hmem : (u ^ n : (v.adicCompletion K)ˣ) ∈ (Units.val ⁻¹' V) := by
      show ((u ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ V
      apply hγ
      show Valued.v.restrict (((u ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val]
      exact hlt n
    have h := hVsub hmem
    simp only [Set.mem_setOf_eq, map_pow, Units.val_pow_eq_pow_val, Metric.mem_ball,
      dist_eq_norm] at h
    exact h.le
  exact Units.val_eq_one.1 (aux_eq_one_of_forall_norm_pow_sub_one_le _ hpow)

end Levels

open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.TateGlobal

section Continuity

variable (K : Type) [Field K] [NumberField K]

private theorem aux_isOpen_integers (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

open scoped Classical in

private noncomputable def aux_addSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x
  map_zero' := RestrictedProduct.single_zero _ _
  map_add' x y := RestrictedProduct.single_add _ _ x y

open scoped Classical in

private theorem aux_single_mem (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (w : HeightOneSpectrum (𝓞 K)) :
    (Pi.single v (y : v.adicCompletion K) : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w ∈
      (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := by
  by_cases hw : w = v
  · subst hw
    simp
  · rw [Pi.single_eq_of_ne hw]
    exact zero_mem _

open scoped Classical in

private theorem aux_continuousOn_addSingle (v : HeightOneSpectrum (𝓞 K)) :
    ContinuousOn (aux_addSingle K v) (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hs : Continuous fun x : v.adicCompletion K =>
      (Pi.single v x : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) := continuous_single v
  have htoA : Continuous fun y : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =>
      (fun w => ⟨_, aux_single_mem K v y w⟩ :
        ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletionIntegers K : Set (w.adicCompletion K))) :=
    continuous_pi fun w => ((continuous_apply w).comp (hs.comp continuous_subtype_val)).subtype_mk _
  have hmap : (v.adicCompletionIntegers K : Set (v.adicCompletion K)).domRestrict (aux_addSingle K v) =
      fun y => RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w : HeightOneSpectrum (𝓞 K) => (w.adicCompletionIntegers K : Set (w.adicCompletion K)))
        Filter.cofinite (fun w => ⟨_, aux_single_mem K v y w⟩) := by
    funext y
    apply FiniteAdeleRing.ext
    intro w
    rfl
  rw [hmap]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (aux_isOpen_integers K)).continuous.comp htoA

private theorem aux_continuous_addSingle (v : HeightOneSpectrum (𝓞 K)) : Continuous (aux_addSingle K v) :=
  continuous_of_continuousAt_zero (aux_addSingle K v)
    ((aux_continuousOn_addSingle K v).continuousAt ((aux_isOpen_integers K v).mem_nhds (zero_mem _)))

open scoped Classical in

private noncomputable def aux_mulSingleF (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x

open scoped Classical in

private theorem aux_continuous_mulSingleF (v : HeightOneSpectrum (𝓞 K)) : Continuous (aux_mulSingleF K v) := by
  have hsplit : aux_mulSingleF K v = fun x => aux_mulSingleF K v 0 + aux_addSingle K v x := by
    funext x
    apply FiniteAdeleRing.ext
    intro w
    show Pi.mulSingle v x w = Pi.mulSingle v (0 : v.adicCompletion K) w + Pi.single v x w
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Pi.mulSingle_eq_of_ne hw, Pi.single_eq_of_ne hw]
  rw [hsplit]
  exact continuous_const.add (aux_continuous_addSingle K v)

open scoped Classical in

private theorem aux_continuous_localUnit (v : HeightOneSpectrum (𝓞 K)) : Continuous (localUnit (𝓞 K) K v) :=
  Units.continuous_iff.2
    ⟨(aux_continuous_mulSingleF K v).comp Units.continuous_val,
      (aux_continuous_mulSingleF K v).comp Units.continuous_coe_inv⟩

private theorem aux_continuous_unitsMap_finIncl : Continuous (Units.map (finIncl (𝓞 K) K)) :=
  Units.continuous_iff.2
    ⟨(continuous_const.prodMk continuous_id).comp Units.continuous_val,
      (continuous_const.prodMk continuous_id).comp Units.continuous_coe_inv⟩

private theorem aux_continuous_localChar (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ)
    (v : HeightOneSpectrum (𝓞 K)) : Continuous (localChar μ v) :=
  hμ.comp ((aux_continuous_unitsMap_finIncl K).comp (aux_continuous_localUnit K v))

end Continuity

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

section

variable (K : Type) [Field K] [NumberField K]

private theorem aux_bosConst (c : ℂ) : LDatum.BoundedOnStrips (fun _ => c) :=
  fun _ _ => ⟨‖c‖, fun _ _ _ => le_rfl⟩

private theorem aux_bosMul {F G : ℂ → ℂ} (hF : LDatum.BoundedOnStrips F) (hG : LDatum.BoundedOnStrips G) :
    LDatum.BoundedOnStrips (fun s => F s * G s) := by
  intro a b
  obtain ⟨C, hC⟩ := hF a b
  obtain ⟨E, hE⟩ := hG a b
  refine ⟨max C 0 * max E 0, fun s ha hb => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC s ha hb).trans (le_max_left _ _)) ((hE s ha hb).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private theorem aux_bosProd {κ : Type} (t : Finset κ) (F : κ → ℂ → ℂ)
    (h : ∀ i ∈ t, LDatum.BoundedOnStrips (F i)) :
    LDatum.BoundedOnStrips (fun s => ∏ i ∈ t, F i s) := by
  have hfun : (fun s => ∏ i ∈ t, F i s) = ∏ i ∈ t, F i := by
    funext s
    rw [Finset.prod_apply]
  rw [hfun]
  exact Finset.prod_induction F LDatum.BoundedOnStrips (fun _ _ hf hg => aux_bosMul hf hg) (aux_bosConst (1 : ℂ)) h

private theorem aux_diffProd {κ : Type} (t : Finset κ) (F : κ → ℂ → ℂ)
    (h : ∀ i ∈ t, Differentiable ℂ (F i)) :
    Differentiable ℂ (fun s => ∏ i ∈ t, F i s) := by
  have hfun : (fun s => ∏ i ∈ t, F i s) = ∏ i ∈ t, F i := by
    funext s
    rw [Finset.prod_apply]
  rw [hfun]
  exact Finset.prod_induction F (Differentiable ℂ) (fun _ _ hf hg => hf.mul hg)
    (differentiable_const (1 : ℂ)) h

private theorem aux_diffMonomialFactor (c : ℂ) (hc : c ≠ 0) (q : ℕ) (hq : 0 < q) (j : ℤ) :
    Differentiable ℂ (fun s : ℂ => (c * (q : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ j) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  refine Differentiable.zpow ?_
    (Or.inl fun s => mul_ne_zero hc fun h0 => hq' ((Complex.cpow_eq_zero_iff _ _).1 h0).1)
  exact (differentiable_const c).mul
    (((differentiable_const ((1 : ℂ) / 2)).sub differentiable_id).const_cpow (Or.inl hq'))

private theorem aux_bosMonomialFactor (c : ℂ) (q : ℕ) (hq : 0 < q) (j : ℤ) :
    LDatum.BoundedOnStrips (fun s : ℂ => (c * (q : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ j) := by
  intro a b
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hre : ∀ s : ℂ, ((1 : ℂ) / 2 - s).re = 1 / 2 - s.re := fun s => by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  refine ⟨‖c‖ ^ j * (q : ℝ) ^ (max ((1 / 2 - a) * (j : ℝ)) ((1 / 2 - b) * (j : ℝ))), fun s ha hb => ?_⟩
  calc ‖(c * (q : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ j‖
      = (‖c‖ * (q : ℝ) ^ (1 / 2 - s.re)) ^ j := by
        rw [norm_zpow, norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre]
    _ = ‖c‖ ^ j * (q : ℝ) ^ ((1 / 2 - s.re) * (j : ℝ)) := by
        rw [mul_zpow, Real.rpow_mul (Nat.cast_nonneg q), Real.rpow_intCast]
    _ ≤ ‖c‖ ^ j * (q : ℝ) ^ (max ((1 / 2 - a) * (j : ℝ)) ((1 / 2 - b) * (j : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 ?_)
          (zpow_nonneg (norm_nonneg c) j)
        rcases le_total (0 : ℝ) (j : ℝ) with hj | hj
        · exact le_max_of_le_left (mul_le_mul_of_nonneg_right (by linarith) hj)
        · exact le_max_of_le_right (mul_le_mul_of_nonpos_right (by linarith) hj)

private theorem aux_absNorm_pos (S : Finset (HeightOneSpectrum (𝓞 K))) (v : ↥S) :
    0 < Ideal.absNorm v.1.asIdeal :=
  Nat.pos_of_ne_zero fun h0 => v.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

private theorem aux_factor_mul_factorDual (u : ℂˣ) (q : ℕ) (hq : 0 < q) (j : ℤ) (s : ℂ) :
    ((u : ℂ) * (q : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ j *
      (((u⁻¹ : ℂˣ) : ℂ) * (q : ℂ) ^ ((1 : ℂ) / 2 - (1 - s))) ^ j = 1 := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (1 : ℂ) / 2 - (1 - s) = -((1 : ℂ) / 2 - s) := by ring
  have hx : (u : ℂ) * (q : ℂ) ^ ((1 : ℂ) / 2 - s) ≠ 0 :=
    mul_ne_zero (Units.ne_zero u) fun h0 => hq' ((Complex.cpow_eq_zero_iff _ _).1 h0).1
  rw [e, Complex.cpow_neg, Units.val_inv_eq_inv_val, ← mul_inv, ← mul_zpow, mul_inv_cancel₀ hx, one_zpow]

end

section

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

private theorem aux_differentiable_yMon {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ↥S → ℤ) :
    Differentiable ℂ (fun s : ℂ => ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) := by
  exact aux_diffProd _ _ fun v _ => aux_diffMonomialFactor _ (Units.ne_zero _) _ (aux_absNorm_pos K S v) _

private theorem aux_bos_const_yMon_mul {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ↥S → ℤ) (c : ℂ)
    (f : ℂ → ℂ) (hf : LDatum.BoundedOnStrips f) :
    LDatum.BoundedOnStrips (fun s : ℂ => c * (∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) * f s) := by
  exact aux_bosMul
    (aux_bosMul (aux_bosConst c)
      (aux_bosProd _ _ fun v _ => aux_bosMonomialFactor _ _ (aux_absNorm_pos K S v) _)) hf

private theorem aux_xMon_mul_yMon {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ↥S → ℤ) (s : ℂ) :
    (∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      (∏ v : ↥S, ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - (1 - s))) ^ (m v)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ =>
    aux_factor_mul_factorDual (μ (uniformizerIdele K v.1)) (Ideal.absNorm v.1.asIdeal)
      (aux_absNorm_pos K S v) (m v) s

end

end

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.Converse NumberField.StandardAddChar

section

variable (K : Type) [Field K] [NumberField K]

private theorem aux_localOf_mul (v : HeightOneSpectrum (𝓞 K)) (α β : Kˣ) :
    localOf K v (α * β) = localOf K v α * localOf K v β :=
  map_mul (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom) α β

private theorem aux_localOf_neg (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    ((localOf K v (-α) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      -((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
  simp [localOf]

private def aux_ordAt (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) : ℤ :=
  -WithZero.log (Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K))

private theorem aux_valued_localOf_ne_zero (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (localOf K v α).ne_zero

private theorem aux_valued_localOf_eq_exp (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-aux_ordAt K v α) := by
  unfold aux_ordAt
  rw [neg_neg, WithZero.exp_log (aux_valued_localOf_ne_zero K v α)]

private theorem aux_ordAt_eq_of_valued (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) (n : ℤ)
    (h : Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-n)) :
    aux_ordAt K v α = n := by
  unfold aux_ordAt
  rw [h, WithZero.log_exp, neg_neg]

private theorem aux_ordAt_mul_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (α β : Kˣ)
    (hβ : Valued.v ((localOf K v β : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1) :
    aux_ordAt K v (α * β) = aux_ordAt K v α := by
  unfold aux_ordAt
  rw [aux_localOf_mul, Units.val_mul, map_mul, hβ, mul_one]

private theorem aux_ordAt_neg (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) : aux_ordAt K v (-α) = aux_ordAt K v α := by
  unfold aux_ordAt
  rw [aux_localOf_neg, Valuation.map_neg]

private theorem aux_ordAt_lt_neg_iff (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) (n : ℤ) :
    aux_ordAt K v α < -n ↔
      ¬ Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ WithZero.exp n := by
  rw [aux_valued_localOf_eq_exp, not_le, WithZero.exp_lt_exp]
  omega

private def aux_unitPart (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) : (v.adicCompletion K)ˣ :=
  localOf K v α * uniformizerUnit K v ^ (-aux_ordAt K v α)

private theorem aux_localOf_eq_unitPart_mul (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    localOf K v α = aux_unitPart K v α * uniformizerUnit K v ^ aux_ordAt K v α := by
  unfold aux_unitPart
  rw [zpow_neg, inv_mul_cancel_right]

private theorem aux_valued_unitPart (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((aux_unitPart K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  unfold aux_unitPart
  rw [Units.val_mul, map_mul, aux_valued_localOf_eq_exp, Units.val_zpow_eq_zpow_val, map_zpow₀,
    valued_uniformizerUnit, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

private theorem aux_unitPart_mul_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (α β : Kˣ)
    (hβ : Valued.v ((localOf K v β : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1) :
    aux_unitPart K v (α * β) = aux_unitPart K v α * localOf K v β := by
  unfold aux_unitPart
  rw [aux_ordAt_mul_of_valued_eq_one K v α β hβ, aux_localOf_mul, mul_right_comm]

private theorem aux_localChar_localOf (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    localChar χ v (localOf K v α) =
      localChar χ v (aux_unitPart K v α) * χ (uniformizerIdele K v) ^ aux_ordAt K v α := by
  rw [aux_localOf_eq_unitPart_mul, map_mul, map_zpow]
  rfl

private theorem aux_localChar_unitPart_of_isJLTwist (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsJLTwist K S epsS μ) (v : ↥S) (α : Kˣ) :
    localChar μ v.1 (aux_unitPart K v.1 α) = (epsS v.1 (aux_unitPart K v.1 α))⁻¹ :=
  eq_inv_of_mul_eq_one_left (hμ.2 v.1 v.2 _ (aux_valued_unitPart K v.1 α))

private theorem aux_cpow_log_valued_eq_zpow (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) (s : ℂ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^
        (((WithZero.log (Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K)) : ℤ) : ℂ)
          * (s - 1 / 2)) =
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ aux_ordAt K v α := by
  have hlog : WithZero.log (Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      -aux_ordAt K v α := by
    unfold aux_ordAt; rw [neg_neg]
  rw [hlog, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

private def aux_famA (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (A : (↥S → ℤ) → ℂ) (α : Kˣ) : ℂ :=
  A (fun v => aux_ordAt K v.1 α) * ∏ v : ↥S, ((epsS v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ)

private def aux_famAd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (Ad : (↥S → ℤ) → ℂ) (c : ℂ) (α : Kˣ) : ℂ :=
  c * (∏ v : ↥S, ((ω (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ aux_ordAt K v.1 α) * Ad (fun v => aux_ordAt K v.1 α) *
    ∏ v : ↥S, ((localChar ω v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ) * (((epsS v.1 (aux_unitPart K v.1 α))⁻¹ : ℂˣ) : ℂ)

private theorem aux_famA_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (A : (↥S → ℤ) → ℂ) :
    ∀ α β : Kˣ, IsSUnit K S β →
      aux_famA K S epsS A (α * β) = (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * aux_famA K S epsS A α := by
  intro α β hβ
  unfold aux_famA
  have hord : ∀ v : ↥S, aux_ordAt K v.1 (α * β) = aux_ordAt K v.1 α :=
    fun v => aux_ordAt_mul_of_valued_eq_one K v.1 α β (hβ v)
  simp only [hord]
  have hprod : (∏ v : ↥S, ((epsS v.1 (aux_unitPart K v.1 (α * β)) : ℂˣ) : ℂ)) =
      ∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * ((epsS v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ) := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [aux_unitPart_mul_of_valued_eq_one K v.1 α β (hβ v), map_mul, Units.val_mul, mul_comm]
  rw [hprod, Finset.prod_mul_distrib]
  ring

private theorem aux_famAd_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (Ad : (↥S → ℤ) → ℂ) (c : ℂ) :
    ∀ α β : Kˣ, IsSUnit K S β →
      aux_famAd K S epsS ω Ad c (α * β) =
        (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ))
          * aux_famAd K S epsS ω Ad c α := by
  intro α β hβ
  unfold aux_famAd
  have hord : ∀ v : ↥S, aux_ordAt K v.1 (α * β) = aux_ordAt K v.1 α :=
    fun v => aux_ordAt_mul_of_valued_eq_one K v.1 α β (hβ v)
  simp only [hord]
  have hprod : (∏ v : ↥S,
        ((localChar ω v.1 (aux_unitPart K v.1 (α * β)) : ℂˣ) : ℂ) *
          (((epsS v.1 (aux_unitPart K v.1 (α * β)))⁻¹ : ℂˣ) : ℂ)) =
      ∏ v : ↥S,
        (((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ)) *
          (((localChar ω v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ)
            * (((epsS v.1 (aux_unitPart K v.1 α))⁻¹ : ℂˣ) : ℂ)) := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [aux_unitPart_mul_of_valued_eq_one K v.1 α β (hβ v), map_mul, map_mul, mul_inv, Units.val_mul, Units.val_mul]
    ring
  rw [hprod, Finset.prod_mul_distrib]
  ring

private theorem aux_famA_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (A : (↥S → ℤ) → ℂ) (α : Kˣ)
    (hA : A (fun v => aux_ordAt K v.1 α) ≠ 0) : aux_famA K S epsS A α ≠ 0 :=
  mul_ne_zero hA (Finset.prod_ne_zero_iff.2 fun v _ => (epsS v.1 (aux_unitPart K v.1 α)).ne_zero)

private theorem aux_ordAt_rep (S : Finset (HeightOneSpectrum (𝓞 K))) (R : SOrderReps K S) (n : ↥S → ℤ) :
    (fun v : ↥S => aux_ordAt K v.1 (R.rep n)) = n :=
  funext fun v => aux_ordAt_eq_of_valued K v.1 (R.rep n) (n v) (R.rep_ord n v)

private theorem aux_famA_mul_sWeight (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (A : (↥S → ℤ) → ℂ)
    (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsJLTwist K S epsS μ) (n : ↥S → ℤ) (s : ℂ) :
    aux_famA K S epsS A (R.rep n) * sWeight K S μ (R.rep n) s =
      A n * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
  unfold aux_famA sWeight
  rw [aux_ordAt_rep, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have hn : aux_ordAt K v.1 (R.rep n) = n v := congrFun (aux_ordAt_rep K S R n) v
  have h1 : ((localChar μ v.1 (aux_unitPart K v.1 (R.rep n)) : ℂˣ) : ℂ) *
      ((epsS v.1 (aux_unitPart K v.1 (R.rep n)) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, hμ.2 v.1 v.2 _ (aux_valued_unitPart K v.1 (R.rep n)), Units.val_one]
  rw [aux_localChar_localOf, aux_cpow_log_valued_eq_zpow, hn, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_zpow]
  linear_combination (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v) *
    (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)) * h1

private theorem aux_famAd_mul_sWeight (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (Ad : (↥S → ℤ) → ℂ) (c : ℂ) (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsJLTwist K S epsS μ)
    (n : ↥S → ℤ) (s : ℂ) :
    aux_famAd K S epsS ω Ad c (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s =
      c * (Ad n * ∏ v : ↥S, ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)) := by
  unfold aux_famAd sWeight
  rw [aux_ordAt_rep]
  have hw : ∀ v : ↥S,
      ((localChar (ω * μ)⁻¹ v.1 (localOf K v.1 (R.rep n)) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (((WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
              v.1.adicCompletion K)) : ℤ) : ℂ) * (s - 1 / 2)) =
        ((((ω (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v))⁻¹ *
            (((localChar ω v.1 (aux_unitPart K v.1 (R.rep n)) : ℂˣ) : ℂ) *
              (((epsS v.1 (aux_unitPart K v.1 (R.rep n)))⁻¹ : ℂˣ) : ℂ))⁻¹) *
          ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
    intro v
    have hn : aux_ordAt K v.1 (R.rep n) = n v := congrFun (aux_ordAt_rep K S R n) v
    have hsplit : localChar (ω * μ)⁻¹ v.1 (localOf K v.1 (R.rep n)) =
        (localChar ω v.1 (localOf K v.1 (R.rep n)) * localChar μ v.1 (localOf K v.1 (R.rep n)))⁻¹ := rfl
    rw [hsplit, aux_localChar_localOf, aux_localChar_localOf, aux_localChar_unitPart_of_isJLTwist K S epsS μ hμ v,
      aux_cpow_log_valued_eq_zpow, hn]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_zpow, inv_zpow]
    field_simp
  have hn_all : ∀ v : ↥S, aux_ordAt K v.1 (R.rep n) = n v := fun v => congrFun (aux_ordAt_rep K S R n) v
  simp only [hn_all]
  have hprod : (∏ v : ↥S, ((ω (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v)) *
      (∏ v : ↥S,
        ((localChar ω v.1 (aux_unitPart K v.1 (R.rep n)) : ℂˣ) : ℂ) *
          (((epsS v.1 (aux_unitPart K v.1 (R.rep n)))⁻¹ : ℂˣ) : ℂ)) *
      (∏ v : ↥S,
        ((localChar (ω * μ)⁻¹ v.1 (localOf K v.1 (R.rep n)) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (((WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
              v.1.adicCompletion K)) : ℤ) : ℂ) * (s - 1 / 2))) =
      ∏ v : ↥S, ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hw v]
    have ha : ((ω (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v) ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
    have hb : ((localChar ω v.1 (aux_unitPart K v.1 (R.rep n)) : ℂˣ) : ℂ) *
        (((epsS v.1 (aux_unitPart K v.1 (R.rep n)))⁻¹ : ℂˣ) : ℂ) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    rw [show ∀ (a b r : ℂ), a * b * (a⁻¹ * b⁻¹ * r) = (a * a⁻¹) * (b * b⁻¹) * r from fun a b r => by ring,
      mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, one_mul, one_mul]
  rw [← hprod]
  ring

private theorem aux_sFactor_expr_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsJLTwist K S epsS μ) (m : ↥S → ℕ) (AK : Kˣ)
    (hAK : ∀ v : ↥S, Valued.v ((localOf K v.1 AK : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      = WithZero.exp (-(m v : ℤ))) (s : ℂ) :
    (∏ v : ↥S, ((localChar μ v.1 (localOf K v.1 (-AK)) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((m v : ℕ) : ℂ) * (s - 1 / 2))) =
      (∏ v : ↥S, ((epsS v.1 (aux_unitPart K v.1 (-AK)) : ℂˣ) : ℂ))⁻¹ *
        ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hord : aux_ordAt K v.1 (-AK) = (m v : ℤ) := by
    rw [aux_ordAt_neg]; exact aux_ordAt_eq_of_valued K v.1 AK _ (hAK v)
  have hexp : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((m v : ℕ) : ℂ) * (s - 1 / 2)) =
      (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := by
    rw [← Complex.cpow_int_mul]
    congr 1
    push_cast
    ring
  rw [aux_localChar_localOf, aux_localChar_unitPart_of_isJLTwist K S epsS μ hμ v, hord, hexp, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, mul_zpow]
  ring

private theorem aux_famA_eq_zero_of_floor (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (A : (↥S → ℤ) → ℂ) (n₀ : ↥S → ℤ)
    (hsupp : ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0) (f : ↥S → ℤ) (hf : ∀ v, -f v ≤ n₀ v) (α : Kˣ)
    (hα : ∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (f v)) :
    aux_famA K S epsS A α = 0 := by
  obtain ⟨v, hv⟩ := hα
  rw [← aux_ordAt_lt_neg_iff] at hv
  unfold aux_famA
  rw [hsupp _ ⟨v, by have := hf v; omega⟩, zero_mul]

private theorem aux_famAd_eq_zero_of_floor (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (Ad : (↥S → ℤ) → ℂ) (c : ℂ) (n₀ : ↥S → ℤ) (hsupp : ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → Ad n = 0) (f : ↥S → ℤ)
    (hf : ∀ v, -f v ≤ n₀ v) (α : Kˣ)
    (hα : ∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (f v)) :
    aux_famAd K S epsS ω Ad c α = 0 := by
  obtain ⟨v, hv⟩ := hα
  rw [← aux_ordAt_lt_neg_iff] at hv
  unfold aux_famAd
  rw [hsupp _ ⟨v, by have := hf v; omega⟩, mul_zero, zero_mul]

private def aux_unitBall (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K)ˣ :=
  Units.embedProduct (v.adicCompletion K) ⁻¹'
    ((v.adicCompletionIntegers K : Set (v.adicCompletion K)) ×ˢ
      (MulOpposite.op '' (v.adicCompletionIntegers K : Set (v.adicCompletion K))))

private theorem aux_isCompact_unitBall (v : HeightOneSpectrum (𝓞 K)) : IsCompact (aux_unitBall K v) := by
  have hI : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hI.prod (hI.image MulOpposite.continuous_op))

private theorem aux_mem_unitBall_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : u ∈ aux_unitBall K v := by
  have h1 : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have h2 : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  exact ⟨h1, _, h2, rfl⟩

private theorem aux_exists_bound_on_units (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) :
    ∃ B : ℝ, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ‖((χ u : ℂˣ) : ℂ)‖ ≤ B ∧ ‖(((χ u)⁻¹ : ℂˣ) : ℂ)‖ ≤ B := by
  have hc1 : Continuous fun u : (v.adicCompletion K)ˣ => ((χ u : ℂˣ) : ℂ) := Units.continuous_val.comp hχ
  have hc2 : Continuous fun u : (v.adicCompletion K)ˣ => (((χ u)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (continuous_inv.comp hχ)
  obtain ⟨B₁, hB₁⟩ := (aux_isCompact_unitBall K v).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨B₂, hB₂⟩ := (aux_isCompact_unitBall K v).exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max B₁ B₂, fun u hu => ?_⟩
  have hmem := aux_mem_unitBall_of_valued_eq_one K v u hu
  exact ⟨(hB₁ u hmem).trans (le_max_left _ _), (hB₂ u hmem).trans (le_max_right _ _)⟩

private theorem aux_exists_bound_famA_famAd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω) (A Ad : (↥S → ℤ) → ℂ)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) (c : ℂ) :
    ∃ C : ℝ, ∀ α : Kˣ, ‖aux_famA K S epsS A α‖ ≤ C ∧ ‖aux_famAd K S epsS ω Ad c α‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hbd
  choose B hB using fun v : ↥S => aux_exists_bound_on_units K v.1 (epsS v.1) (hepsS v.1 v.2)
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0).1
  have hunit : ∀ (x : (AdeleRing (𝓞 K) K)ˣ), ‖((ω x : ℂˣ) : ℂ)‖ = 1 := hω.2.2
  refine ⟨max (C₀ * ∏ v : ↥S, B v) (‖c‖ * C₀ * ∏ v : ↥S, B v), fun α => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (le_max_left _ _)
    unfold aux_famA
    rw [norm_mul, norm_prod]
    refine mul_le_mul (hC₀ _).1 (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ =>
      (hB v _ (aux_valued_unitPart K v.1 α)).1) (Finset.prod_nonneg fun v _ => norm_nonneg _) hC₀0
  · refine le_trans ?_ (le_max_right _ _)
    unfold aux_famAd
    rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
    have hϖ : (∏ v : ↥S, ‖((ω (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ aux_ordAt K v.1 α‖) = 1 :=
      Finset.prod_eq_one fun v _ => by rw [norm_zpow, hunit, one_zpow]
    have hloc : ∀ v : ↥S,
        ‖((localChar ω v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ)
            * (((epsS v.1 (aux_unitPart K v.1 α))⁻¹ : ℂˣ) : ℂ)‖ ≤ B v := by
      intro v
      have h1 : ‖((localChar ω v.1 (aux_unitPart K v.1 α) : ℂˣ) : ℂ)‖ = 1 := hunit _
      rw [norm_mul, h1, one_mul]
      exact (hB v _ (aux_valued_unitPart K v.1 α)).2
    rw [hϖ, mul_one]
    refine mul_le_mul (mul_le_mul le_rfl (hC₀ _).2 (norm_nonneg _) (norm_nonneg _))
      (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hloc v)
      (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg (norm_nonneg _) hC₀0)

end

private theorem aux_exists_periphery_data {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (A Ad : (↥S → ℤ) → ℂ) (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (n₀ : ↥S → ℤ) (hn₀ : ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (k : ↥S → ℤ) (m : ↥S → ℕ)
    (hk : ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v + k v)
    (hm : ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v - k v + (m v : ℤ))
    (AK : Kˣ)
    (hAK : ∀ v : ↥S, Valued.v ((localOf K v.1 AK : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      = WithZero.exp (-(m v : ℤ))) :
    ∃ (c : ℂ) (a ad : Kˣ → ℂ), c ≠ 0 ∧
      (∃ C : ℝ, ∀ α, ‖a α‖ ≤ C ∧ ‖ad α‖ ≤ C) ∧
      (∀ α β : Kˣ, IsSUnit K S β →
        a (α * β) = (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * a α) ∧
      (∀ α β : Kˣ, IsSUnit K S β →
        ad (α * β) =
          (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) *
            (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ)) * ad α) ∧
      (∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
          ≤ WithZero.exp (TateLocal.addCharLevel (psiLocal K v.1))) → a α = 0 ∧ ad α = 0) ∧
      (∀ n : ↥S → ℤ, A n ≠ 0 → ∀ R : SOrderReps K S, a (R.rep (n + k)) ≠ 0) ∧
      (∀ (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsJLTwist K S epsS μ →
        ∀ (n : ↥S → ℤ) (s : ℂ),
          a (R.rep n) * sWeight K S μ (R.rep n) s =
            A (n - k) * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)) ∧
      (∀ (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsJLTwist K S epsS μ →
        ∀ (n : ↥S → ℤ) (s : ℂ),
          ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s =
            c * (Ad (n + k - (fun v => (m v : ℤ))) * ∏ v : ↥S, ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v))) ∧
      (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ → ∀ s : ℂ,
        (∏ v : ↥S, ((localChar μ v.1 (localOf K v.1 (-AK)) : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((m v : ℕ) : ℂ) * (s - 1 / 2))) =
          c⁻¹ * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ)) := by
  obtain ⟨C₀, hC₀⟩ := hbd
  refine ⟨∏ v : ↥S, ((epsS v.1 (aux_unitPart K v.1 (-AK)) : ℂˣ) : ℂ),
    aux_famA K S epsS (fun n => A (n - k)),
    aux_famAd K S epsS ω (fun n => Ad (n + k - (fun v => (m v : ℤ))))
      (∏ v : ↥S, ((epsS v.1 (aux_unitPart K v.1 (-AK)) : ℂˣ) : ℂ)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun v _ => (epsS v.1 (aux_unitPart K v.1 (-AK))).ne_zero
  · exact aux_exists_bound_famA_famAd K S epsS hepsS ω hω _ _ ⟨C₀, fun n => ⟨(hC₀ _).1, (hC₀ _).2⟩⟩ _
  · exact aux_famA_mul K S epsS _
  · exact aux_famAd_mul K S epsS ω _ _
  · intro α hα
    refine ⟨aux_famA_eq_zero_of_floor K S epsS _ (n₀ + k) ?_
        (fun v => TateLocal.addCharLevel (psiLocal K v.1)) ?_ α hα,
      aux_famAd_eq_zero_of_floor K S epsS ω _ _ (n₀ - k + fun v => (m v : ℤ)) ?_
        (fun v => TateLocal.addCharLevel (psiLocal K v.1)) ?_ α hα⟩
    · rintro n ⟨v, hv⟩
      refine (hn₀ (n - k) ⟨v, ?_⟩).1
      simp only [Pi.add_apply, Pi.sub_apply] at hv ⊢
      omega
    · intro v
      simp only [Pi.add_apply]
      exact hk v
    · rintro n ⟨v, hv⟩
      refine (hn₀ (n + k - fun v => (m v : ℤ)) ⟨v, ?_⟩).2
      simp only [Pi.add_apply, Pi.sub_apply] at hv ⊢
      omega
    · intro v
      simp only [Pi.add_apply, Pi.sub_apply]
      exact hm v
  · intro n hn R
    refine aux_famA_ne_zero K S epsS _ (R.rep (n + k)) ?_
    rw [aux_ordAt_rep]
    simpa only [add_sub_cancel_right] using hn
  · intro R μ hμ n s
    exact aux_famA_mul_sWeight K S epsS _ R μ hμ n s
  · intro R μ hμ n s
    exact aux_famAd_mul_sWeight K S epsS ω _ _ R μ hμ n s
  · intro μ hμ s
    exact aux_sFactor_expr_eq K S epsS μ hμ m AK hAK s

private theorem aux_valued_localOf (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = v.valuation K (α : K) := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) (v := v) (α : K)

private theorem aux_sPartDual_shift (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (m : ↥S → ℤ) :
    (∏ v : ↥S,
        ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      sPartDual K S Ad μ s = sPartDual K S (fun n => Ad (n - m)) μ s := by
  simp only [sPartDual_eq_sPart_inv]
  exact sPart_shift K S Ad μ⁻¹ s m

end

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse
open NumberField.StandardAddChar

noncomputable section

private theorem aux_exists_level {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      IsOneMod K v m u → χ u = 1 := by
  obtain ⟨m, hm, h⟩ := aux_exists_level_of_continuous (K := K) (v := v) χ hχ
  exact ⟨m, hm, fun u _ hu => h u (by simpa only [IsOneMod] using hu)⟩

private theorem aux_continuous_localChar' {K : Type} [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous ⇑μ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ⇑(localChar μ v) := by
  exact aux_continuous_localChar (K := K) μ hμ v

private theorem aux_exists_ne_zero_valuation_eq {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) := by
  exact LanglandsTunnell.Converse.exists_ne_zero_valuation_eq_exp_neg K S n

private theorem aux_valued_localOf' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = v.valuation K (α : K) := by
  exact aux_valued_localOf K v α

private theorem aux_isNicePinned_sPart_shift (K : Type) [Field K] [NumberField K]
    {ι : Type} (D : LanglandsTunnell.LDatum ι) (hc : D.center = 1 / 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ε : ℂ) (N : ℝ) (k : ↥S → ℤ)
    (h : IsNicePinned D (sPart K S A μ) (sPartDual K S Ad μ) ε N) :
    IsNicePinned D (sPart K S (fun n => A (n - k)) μ) (sPartDual K S (fun n => Ad (n + k)) μ) ε N := by
  exact LanglandsTunnell.Converse.isNicePinned_sPart_shift K D hc S A Ad μ ε N k h

private theorem aux_sPartDual_shift' (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (m : ↥S → ℤ) :
    (∏ v : ↥S,
        ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      sPartDual K S Ad μ s = sPartDual K S (fun n => Ad (n - m)) μ s := by
  exact aux_sPartDual_shift K S Ad μ s m

private theorem aux_summable_mul_prod_zpow' {ι : Type} [Fintype ι] (x : ι → ℂ) (hx0 : ∀ i, x i ≠ 0)
    (hx1 : ∀ i, ‖x i‖ < 1) (A : (ι → ℤ) → ℂ) (C : ℝ) (hbd : ∀ n, ‖A n‖ ≤ C) (n₀ : ι → ℤ)
    (hsupp : ∀ n : ι → ℤ, (∃ i, n i < n₀ i) → A n = 0) :
    Summable fun n : ι → ℤ => A n * ∏ i, x i ^ n i := by
  exact aux_summable_mul_prod_zpow x hx0 hx1 A C hbd n₀ hsupp

private theorem aux_norm_x_lt_one {K : Type} [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ) (v : HeightOneSpectrum (𝓞 K))
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖((μ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖
      < 1 := by
  exact aux_norm_sVariable_lt_one (K := K) μ hμ v s hs

private theorem aux_norm_y_lt_one {K : Type} [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ) (v : HeightOneSpectrum (𝓞 K))
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖(((μ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖
      < 1 := by
  exact aux_norm_sVariableDual_lt_one (K := K) μ hμ v s hs

private theorem aux_exists_periphery_data' {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (A Ad : (↥S → ℤ) → ℂ) (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (n₀ : ↥S → ℤ) (hn₀ : ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (k : ↥S → ℤ) (m : ↥S → ℕ)
    (hk : ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v + k v)
    (hm : ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v - k v + (m v : ℤ))
    (AK : Kˣ)
    (hAK : ∀ v : ↥S, Valued.v ((localOf K v.1 AK : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      = WithZero.exp (-(m v : ℤ))) :
    ∃ (c : ℂ) (a ad : Kˣ → ℂ), c ≠ 0 ∧
      (∃ C : ℝ, ∀ α, ‖a α‖ ≤ C ∧ ‖ad α‖ ≤ C) ∧
      (∀ α β : Kˣ, IsSUnit K S β →
        a (α * β) = (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * a α) ∧
      (∀ α β : Kˣ, IsSUnit K S β →
        ad (α * β) =
          (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) *
            (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ)) * ad α) ∧
      (∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
          ≤ WithZero.exp (TateLocal.addCharLevel (psiLocal K v.1))) → a α = 0 ∧ ad α = 0) ∧
      (∀ n : ↥S → ℤ, A n ≠ 0 → ∀ R : SOrderReps K S, a (R.rep (n + k)) ≠ 0) ∧
      (∀ (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsJLTwist K S epsS μ →
        ∀ (n : ↥S → ℤ) (s : ℂ),
          a (R.rep n) * sWeight K S μ (R.rep n) s =
            A (n - k) * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)) ∧
      (∀ (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsJLTwist K S epsS μ →
        ∀ (n : ↥S → ℤ) (s : ℂ),
          ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s =
            c * (Ad (n + k - (fun v => (m v : ℤ))) * ∏ v : ↥S, ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v))) ∧
      (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ → ∀ s : ℂ,
        (∏ v : ↥S, ((localChar μ v.1 (localOf K v.1 (-AK)) : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((m v : ℕ) : ℂ) * (s - 1 / 2))) =
          c⁻¹ * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ)) := by
  exact aux_exists_periphery_data S epsS hepsS ω hω A Ad hbd n₀ hn₀ k m hk hm AK hAK

private theorem aux_unit_mul_cpow_absNorm_ne_zero {K : Type} [Field K] [NumberField K] (c : ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (e : ℂ) :
    (c : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ e ≠ 0 := by
  refine mul_ne_zero (Units.ne_zero _) fun h => ?_
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 0 := ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have hq' : Ideal.absNorm v.asIdeal = 0 := by exact_mod_cast hq
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 hq')

private theorem aux_isOneMod_mono {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {m m' : ℕ} (h : m ≤ m') (u : (v.adicCompletion K)ˣ) (hu : IsOneMod K v m' u) : IsOneMod K v m u :=
  le_trans hu (WithZero.exp_le_exp.2 (by omega))

private def aux_reps (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SOrderReps K S where
  rep n := Units.mk0 (aux_exists_ne_zero_valuation_eq S n).choose
    (aux_exists_ne_zero_valuation_eq S n).choose_spec.1
  rep_ord n v := by
    rw [aux_valued_localOf']
    exact (aux_exists_ne_zero_valuation_eq S n).choose_spec.2 v

theorem solution
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (A Ad : (↥S → ℤ) → ℂ)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (hsupp : ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (hA0 : A ≠ 0)
    (hnice : ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K Pi S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω) :
    ∀ mlow : ↥S → ℕ, ∃ J : JLData K S epsS ω,
      (∀ v : ↥S, mlow v ≤ J.m v) ∧ IsJLNice K S epsS ω J Pi archR archC := by
  intro mlow
  classical
  obtain ⟨n₀, hn₀⟩ := hsupp

  obtain ⟨k, hk0, hk⟩ : ∃ k : ↥S → ℤ, (∀ v, 0 ≤ k v) ∧
      ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v + k v := by
    refine ⟨fun v => max 0 (-TateLocal.addCharLevel (psiLocal K v.1) - n₀ v), fun v => le_max_left _ _, fun v => ?_⟩
    show -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v + max 0 (-TateLocal.addCharLevel (psiLocal K v.1) - n₀ v)
    have := le_max_right 0 (-TateLocal.addCharLevel (psiLocal K v.1) - n₀ v)
    omega

  choose mε hmε using fun v : ↥S => aux_exists_level v.1 (epsS v.1) (hepsS v.1 v.2)
  choose mω hmω using fun v : ↥S => aux_exists_level v.1 (localChar ω v.1)
    (aux_continuous_localChar' ω hω.2.1 v.1)

  obtain ⟨m, hm_low, hm_ε, hm_ω, hm_k⟩ : ∃ m : ↥S → ℕ, (∀ v, mlow v ≤ m v) ∧ (∀ v, mε v ≤ m v) ∧
      (∀ v, mω v ≤ m v) ∧ ∀ v, 2 * k v ≤ (m v : ℤ) := by
    refine ⟨fun v => max (mlow v) (max (mε v) (max (mω v) (2 * (k v).toNat))),
      fun v => le_max_left _ _,
      fun v => le_trans (le_max_left _ _) (le_max_right _ _),
      fun v => le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _),
      fun v => ?_⟩
    show 2 * k v ≤ ((max (mlow v) (max (mε v) (max (mω v) (2 * (k v).toNat))) : ℕ) : ℤ)
    have h1 : 2 * (k v).toNat ≤ max (mlow v) (max (mε v) (max (mω v) (2 * (k v).toNat))) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    have h2 : ((2 * (k v).toNat : ℕ) : ℤ) ≤
        ((max (mlow v) (max (mε v) (max (mω v) (2 * (k v).toNat))) : ℕ) : ℤ) := Nat.cast_le.2 h1
    rw [Nat.cast_mul, Nat.cast_ofNat, Int.toNat_of_nonneg (hk0 v)] at h2
    exact h2
  have hm : ∀ v : ↥S, -TateLocal.addCharLevel (psiLocal K v.1) ≤ n₀ v - k v + (m v : ℤ) := fun v => by
    have := hk v; have := hm_k v; have := hk0 v; omega

  obtain ⟨α, hα0, hαv⟩ := aux_exists_ne_zero_valuation_eq S (fun v => (m v : ℤ))
  obtain ⟨AK, hAK⟩ : ∃ AK : Kˣ, ∀ v : ↥S,
      Valued.v ((localOf K v.1 AK : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        = WithZero.exp (-(m v : ℤ)) :=
    ⟨Units.mk0 α hα0, fun v => by rw [aux_valued_localOf']; exact hαv v⟩

  obtain ⟨c, a, ad, hc0, hbd', ha_mul, had_mul, hfloor, hane, ha_term, had_term, hsF⟩ :=
    aux_exists_periphery_data' S epsS hepsS ω hω A Ad hbd n₀ hn₀ k m hk hm AK hAK

  obtain ⟨R⟩ : Nonempty (SOrderReps K S) := ⟨aux_reps K S⟩

  obtain ⟨J, hJm, hJA, hJa, hJad⟩ : ∃ J : JLData K S epsS ω,
      J.m = m ∧ J.A = AK ∧ J.a = a ∧ J.ad = ad := by
    refine ⟨⟨m, fun v => le_trans (hmε v).1 (hm_ε v),
      fun v u hu h1 => (hmε v).2 u hu (aux_isOneMod_mono v.1 (hm_ε v) u h1),
      fun v u hu h1 => (hmω v).2 u hu (aux_isOneMod_mono v.1 (hm_ω v) u h1),
      AK, hAK, a, ad, hbd', ha_mul, had_mul, hfloor, ?_⟩, rfl, rfl, rfl, rfl⟩
    obtain ⟨n, hn⟩ := Function.ne_iff.1 hA0
    exact ⟨R.rep (n + k), hane n (by simpa using hn) R⟩
  refine ⟨J, fun v => by rw [hJm]; exact hm_low v, ⟨R, fun μ hμ uR aR uC kC hR hC => ?_⟩⟩

  have hN := hnice μ hμ.1 hμ.2 uR aR uC kC hR hC
  have hN' := aux_isNicePinned_sPart_shift K (twistedDatum K Pi S archR archC μ uR aR uC kC) rfl
    S A Ad μ (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S) k hN
  obtain ⟨hwf, hconv, -, Λ₁, Λd₁, hΛ₁, hΛd₁, hbΛ₁, hbΛd₁, hrep₁, hrepd₁, hFE₁⟩ := hN'

  obtain ⟨Xm, hXm⟩ : ∃ Xm : ℂ → ℂ, ∀ s, Xm s = ∏ v : ↥S,
      (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := ⟨_, fun s => rfl⟩
  obtain ⟨Ym, hYm⟩ : ∃ Ym : ℂ → ℂ, ∀ s, Ym s = ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := ⟨_, fun s => rfl⟩
  obtain ⟨Λd, hΛd⟩ : ∃ Λd : ℂ → ℂ, ∀ s, Λd s = c * Ym s * Λd₁ s := ⟨_, fun s => rfl⟩
  have hYm_fun : Ym = fun s => ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := funext hYm
  have hΛd_fun : Λd = fun s => c * Ym s * Λd₁ s := funext hΛd
  have hYm_diff : Differentiable ℂ Ym := by
    rw [hYm_fun]
    exact aux_differentiable_yMon S μ (fun v => (m v : ℤ))
  have hΛd_diff : Differentiable ℂ Λd := by
    rw [hΛd_fun]
    exact ((differentiable_const c).mul hYm_diff).mul hΛd₁
  have hΛd_bos : LDatum.BoundedOnStrips Λd := by
    rw [hΛd_fun, hYm_fun]
    exact aux_bos_const_yMon_mul S μ (fun v => (m v : ℤ)) c Λd₁ hbΛd₁

  have hcen : (((twistedDatum K Pi S archR archC μ uR aR uC kC).center : ℝ) : ℂ) = 1 / 2 := by
    rw [show (twistedDatum K Pi S archR archC μ uR aR uC kC).center = 1 / 2 from rfl]
    norm_num
  have hFE : ∀ s : ℂ, Λ₁ s = pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
      ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * Λd₁ (1 - s) := fun s => by
    have h := hFE₁ s
    rw [hcen] at h
    have h2 : (2 : ℂ) * (1 / 2) - s = 1 - s := by ring
    rw [h2] at h
    exact h
  refine ⟨hwf, hconv, 1, Λ₁, Λd, hΛ₁, hΛd_diff, hbΛ₁, hΛd_bos, fun s hs => ⟨?_, ?_, ?_, ?_⟩, fun s => ?_⟩
  ·
    obtain ⟨C, hC⟩ := hbd
    refine (aux_summable_mul_prod_zpow'
      (fun v : ↥S => ((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s))
      (fun v => aux_unit_mul_cpow_absNorm_ne_zero (μ (uniformizerIdele K v.1)) v.1 ((1 : ℂ) / 2 - s))
      (fun v => aux_norm_x_lt_one μ hμ.1 v.1 s (by have h1 : (1 : ℝ) < s.re := hs; linarith))
      (fun n => A (n - k)) C (fun n => (hC (n - k)).1) (n₀ + k) ?_).congr (fun n => ?_)
    · intro n hn
      obtain ⟨v, hv⟩ := hn
      refine (hn₀ (n - k) ⟨v, ?_⟩).1
      simp only [_root_.Pi.add_apply, _root_.Pi.sub_apply] at hv ⊢
      omega
    · show A (n - k) * _ = J.a (R.rep n) * sWeight K S μ (R.rep n) s
      rw [hJa]
      exact (ha_term R μ hμ n s).symm
  ·
    obtain ⟨C, hC⟩ := hbd
    refine ((aux_summable_mul_prod_zpow'
      (fun v : ↥S => (((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s))
      (fun v => aux_unit_mul_cpow_absNorm_ne_zero (μ (uniformizerIdele K v.1))⁻¹ v.1 ((1 : ℂ) / 2 - s))
      (fun v => aux_norm_y_lt_one μ hμ.1 v.1 s (by have h1 : (1 : ℝ) < s.re := hs; linarith))
      (fun n => Ad (n + k - (fun v => (m v : ℤ)))) C (fun n => (hC _).2)
      (n₀ - k + (fun v => (m v : ℤ))) ?_).mul_left c).congr (fun n => ?_)
    · intro n hn
      obtain ⟨v, hv⟩ := hn
      refine (hn₀ _ ⟨v, ?_⟩).2
      simp only [_root_.Pi.add_apply, _root_.Pi.sub_apply] at hv ⊢
      omega
    · show c * (Ad (n + k - (fun v => (m v : ℤ))) * _) = J.ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s
      rw [hJad]
      exact (had_term R μ hμ n s).symm
  ·
    have hsum : J.sSum R μ s = sPart K S (fun n => A (n - k)) μ s := by
      unfold JLData.sSum sPart
      rw [hJa]
      exact tsum_congr (fun n => ha_term R μ hμ n s)
    rw [hsum]
    exact hrep₁ s hs
  ·
    have h1 : J.sSumDual R μ s = c * sPartDual K S (fun n => Ad (n + k - (fun v => (m v : ℤ)))) μ s := by
      unfold JLData.sSumDual sPartDual
      rw [hJad, ← tsum_mul_left]
      exact tsum_congr (fun n => had_term R μ hμ n s)
    have e : (fun n : ↥S → ℤ => Ad (n + k - (fun v => (m v : ℤ)))) =
        fun n => (fun n => Ad (n + k)) (n - (fun v => (m v : ℤ))) := by
      funext n
      show Ad (n + k - (fun v => (m v : ℤ))) = Ad (n - (fun v => (m v : ℤ)) + k)
      rw [sub_add_eq_add_sub]
    have h2 : sPartDual K S (fun n => Ad (n + k - (fun v => (m v : ℤ)))) μ s =
        Ym s * sPartDual K S (fun n => Ad (n + k)) μ s := by
      rw [e, hYm]
      exact (aux_sPartDual_shift' K S (fun n => Ad (n + k)) μ s (fun v => (m v : ℤ))).symm
    rw [hΛd, h1, h2, hrepd₁ s hs]
    ring
  ·
    have hsFJ : J.sFactor μ s = c⁻¹ * ∏ v : ↥S, (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v : ℤ) := by
      unfold JLData.sFactor
      rw [hJA, hJm]
      exact hsF μ hμ s
    have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0
    have hXY : Xm s * Ym (1 - s) = 1 := by
      rw [hXm, hYm]
      exact aux_xMon_mul_yMon S μ (fun v => (m v : ℤ)) s
    rw [hsFJ, ← hXm s, hΛd, hFE s]
    calc pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
          ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * Λd₁ (1 - s)
        = (c⁻¹ * c) * (Xm s * Ym (1 - s)) * (pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
            ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * Λd₁ (1 - s)) := by
          rw [hcc, hXY, one_mul, one_mul]
      _ = c⁻¹ * Xm s * pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
            ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * (c * Ym (1 - s) * Λd₁ (1 - s)) := by
          ring

end

end S_LanglandsTunnell_Converse_exists_jlData_isJLNice_of_forall_isNicePinned
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_jlData_isJLNice_of_forall_isNicePinned (solution)
