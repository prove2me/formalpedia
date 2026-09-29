-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12ae4796-d81e-56e3-9361-18d87db78ffa

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace T0R

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ϖ" => (NumberField.AdelicLevel.uniformizerUnit ℚ p)
local notation "νx" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem one_lt_N : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := p)

theorem N_pos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := zero_lt_one.trans (one_lt_N p)

theorem NC_ne_zero : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h := N_pos p
  exact_mod_cast h.ne'

theorem NC_eq : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℂ) :=
  (Complex.ofReal_natCast _).symm

theorem norm_NC_cpow (w : ℂ) : ‖((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ w‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ w.re := by
  rw [NC_eq, Complex.norm_cpow_eq_rpow_re_of_pos (N_pos p)]

theorem NC_cpow_int_mul (n : ℤ) (w : ℂ) :
    ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((n : ℂ) * w) = (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ w) ^ n := by
  rw [mul_comm, Complex.cpow_mul_int]

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

def U : Set Fˣ := {u | Valued.v (u : F) = 1}

theorem U_def : U p = {u : Fˣ | Valued.v (u : F) = 1} := rfl

theorem measurableSet_U : MeasurableSet (U p) := by
  have h := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).1 0
  simpa [U_def] using h

theorem valued_zpow_mul {n : ℤ} {u : Fˣ} (hu : u ∈ U p) :
    Valued.v (((ϖ ^ n * u : Fˣ)) : F) = WithZero.exp (-n) := by
  have hu' : Valued.v (u : F) = 1 := hu
  rw [Units.val_mul, map_mul, hu', mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀,
    NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]

theorem modulus_eq_of_valued {n : ℤ} {y : Fˣ} (hy : Valued.v (y : F) = WithZero.exp (-n)) :
    (modulus (y : F) : ℝ) = (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) := by
  have h := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.2.1
    n y hy
  rw [h]

theorem norm_eq_modulus (x : F) : ‖x‖ = (modulus x : ℝ) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_zpow_mul {n : ℤ} {u : Fˣ} (hu : u ∈ U p) :
    ‖(((ϖ ^ n * u : Fˣ)) : F)‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) := by
  rw [norm_eq_modulus p, modulus_eq_of_valued p (valued_zpow_mul p hu)]

theorem modulus_uniformizer : (modulus ((ϖ : Fˣ) : F) : ℝ) = (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := by
  have h : Valued.v ((ϖ : Fˣ) : F) = WithZero.exp (-(1 : ℤ)) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  rw [modulus_eq_of_valued p h, zpow_neg, zpow_one]

theorem modulus_coe_pos (y : Fˣ) : 0 < (modulus (y : F) : ℝ) := by
  exact_mod_cast modulus_pos (Units.ne_zero y)

theorem modulus_coe_cpow_ne_zero (y : Fˣ) (w : ℂ) : ((modulus (y : F) : ℝ) : ℂ) ^ w ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (modulus_coe_pos p y).ne'

theorem isLocallyConstant_modulus_coe : IsLocallyConstant fun y : Fˣ => (modulus (y : F) : ℝ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  have h0 : 0 < ‖(y₀ : F)‖ := norm_pos_iff.mpr (Units.ne_zero y₀)
  have hopen : IsOpen (Metric.ball (y₀ : F) ‖(y₀ : F)‖) := Metric.isOpen_ball
  have hmem : (fun y : Fˣ => (y : F)) ⁻¹' Metric.ball (y₀ : F) ‖(y₀ : F)‖ ∈ nhds y₀ := by
    refine (hopen.preimage Units.continuous_val).mem_nhds ?_
    show (y₀ : F) ∈ Metric.ball (y₀ : F) ‖(y₀ : F)‖
    exact Metric.mem_ball_self h0
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖(y : F) - (y₀ : F)‖ < ‖(y₀ : F)‖ := by
    have : dist (y : F) (y₀ : F) < ‖(y₀ : F)‖ := hy
    rwa [dist_eq_norm] at this
  show (modulus (y : F) : ℝ) = (modulus (y₀ : F) : ℝ)
  rw [← norm_eq_modulus p, ← norm_eq_modulus p]
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max ((y : F) - (y₀ : F)) (y₀ : F)
    rw [sub_add_cancel] at h1
    exact h1.trans (max_le hy'.le le_rfl)
  · have h2 := IsUltrametricDist.norm_add_le_max ((y₀ : F) - (y : F)) (y : F)
    rw [sub_add_cancel] at h2
    rcases le_max_iff.mp h2 with h | h
    · rw [norm_sub_rev] at h
      exact absurd (lt_of_le_of_lt h hy') (lt_irrefl _)
    · exact h

theorem isLocallyConstant_mul {X : Type*} [TopologicalSpace X] {f g : X → ℂ}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant fun x => f x * g x := by
  rw [IsLocallyConstant.iff_eventually_eq] at hf hg ⊢
  intro x
  filter_upwards [hf x, hg x] with y hy hy'
  rw [hy, hy']

theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℤ, (Ideal.absNorm p.asIdeal : ℝ) ^ (-k) < ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ε⁻¹ (one_lt_N p)
  refine ⟨k, ?_⟩
  rw [zpow_neg, zpow_natCast]
  rwa [inv_lt_comm₀ (pow_pos (N_pos p) k) hε]

theorem zpow_neg_antitone {a b : ℤ} (hab : a ≤ b) :
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-b) ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-a) :=
  zpow_le_zpow_right₀ (one_lt_N p).le (neg_le_neg hab)

theorem exists_thresholds {φ : F → ℂ} (hφ : IsSchwartzBruhat φ) :
    ∃ (n₁ n₀ : ℤ) (c₀ : ℝ), n₁ ≤ n₀ ∧
      (∀ (n : ℤ) (u : Fˣ), u ∈ U p → n < n₁ → φ (((ϖ ^ n * u : Fˣ)) : F) = 0) ∧
      (∀ (n : ℤ) (u : Fˣ), u ∈ U p → n₀ ≤ n → φ (((ϖ ^ n * u : Fˣ)) : F) = φ 0) ∧
      (∀ y : Fˣ, c₀ < modulus (y : F) → φ (y : F) = 0) := by

  obtain ⟨B, hB⟩ := hφ.2.isCompact.isBounded.exists_norm_le
  have hzero : ∀ x : F, B < ‖x‖ → φ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact absurd (hB x hmem) (not_le.mpr hx)

  have hopen : IsOpen {x : F | φ x = φ 0} := hφ.1.isOpen_fiber (φ 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 rfl
  obtain ⟨k₀, hk₀⟩ := exists_zpow_neg_lt p hε
  obtain ⟨k₁, hk₁⟩ := pow_unbounded_of_one_lt B (one_lt_N p)
  refine ⟨min (-(k₁ : ℤ)) k₀, k₀, B, min_le_right _ _, ?_, ?_, ?_⟩
  · intro n u hu hn
    apply hzero
    rw [norm_zpow_mul p hu]
    have hn' : n < -(k₁ : ℤ) := lt_of_lt_of_le hn (min_le_left _ _)
    calc B < (Ideal.absNorm p.asIdeal : ℝ) ^ k₁ := hk₁
      _ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-(-(k₁ : ℤ))) := by rw [neg_neg, zpow_natCast]
      _ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) := zpow_neg_antitone p hn'.le
  · intro n u hu hn
    have hmem : (((ϖ ^ n * u : Fˣ)) : F) ∈ Metric.ball (0 : F) ε := by
      rw [Metric.mem_ball, dist_zero_right, norm_zpow_mul p hu]
      exact lt_of_le_of_lt (zpow_neg_antitone p hn) hk₀
    exact hball hmem
  · intro y hy
    apply hzero
    rwa [norm_eq_modulus p]

theorem hasSum_tail {ρ : ℂ} (hρ : ‖ρ‖ < 1) (hρ0 : ρ ≠ 0) (c : ℂ) (n₀ : ℤ) :
    HasSum (fun n : ℤ => if n₀ ≤ n then c * ρ ^ n else 0) (c * ρ ^ n₀ * (1 - ρ)⁻¹) := by
  set g : ℕ → ℤ := fun k => n₀ + (k : ℤ) with hg
  have hginj : Function.Injective g := by
    intro a b h
    simp only [hg] at h
    exact_mod_cast (add_left_cancel h)
  have hvan : ∀ n : ℤ, n ∉ Set.range g → (fun n : ℤ => if n₀ ≤ n then c * ρ ^ n else 0) n = 0 := by
    intro n hn
    by_cases h : n₀ ≤ n
    · exfalso
      apply hn
      refine ⟨(n - n₀).toNat, ?_⟩
      simp only [hg]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr h)]
      ring
    · simp [h]
  refine (hginj.hasSum_iff hvan).mp ?_
  have hcomp : ((fun n : ℤ => if n₀ ≤ n then c * ρ ^ n else 0) ∘ g) = fun k : ℕ => c * ρ ^ n₀ * ρ ^ k := by
    funext k
    simp only [Function.comp, hg]
    rw [if_pos (by omega), zpow_add₀ hρ0, zpow_natCast]
    ring
  rw [hcomp]
  exact (hasSum_geometric_of_norm_lt_one hρ).mul_left (c * ρ ^ n₀)

theorem hasSum_unique_of_shells {a I : ℤ → ℂ} {ρ G₀ : ℂ} (hρ : ‖ρ‖ < 1) (hρ0 : ρ ≠ 0) {n₁ n₀ : ℤ} (h10 : n₁ ≤ n₀)
    (ha : ∀ n, a n = ρ ^ n * I n) (hlow : ∀ n, n < n₁ → I n = 0) (hhigh : ∀ n, n₀ ≤ n → I n = G₀)
    {S : ℂ} (hS : HasSum a S) :
    S = (∑ n ∈ Finset.Ico n₁ n₀, ρ ^ n * I n) + G₀ * ρ ^ n₀ * (1 - ρ)⁻¹ := by
  set b : ℤ → ℂ := fun n => if n₀ ≤ n then G₀ * ρ ^ n else 0 with hb
  have htail : HasSum b (G₀ * ρ ^ n₀ * (1 - ρ)⁻¹) := hasSum_tail hρ hρ0 G₀ n₀
  have hfin : HasSum (fun n => a n - b n) (∑ n ∈ Finset.Ico n₁ n₀, (a n - b n)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
    rcases hn with hn | hn
    · have : ¬ n₀ ≤ n := by omega
      simp only [hb, if_neg this, ha n, hlow n hn, mul_zero, sub_zero]
    · simp only [hb, if_pos hn, ha n, hhigh n hn]
      ring
  have hsum := hfin.add htail
  simp only [sub_add_cancel] at hsum
  have heq := hS.unique hsum
  rw [heq]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ico] at hn
  have : ¬ n₀ ≤ n := by omega
  simp only [hb, if_neg this, sub_zero, ha n]

theorem main (μ : Fˣ →* ℂˣ) (hμ : IsLocallyConstant μ) (φ : F → ℂ) (hφ : IsSchwartzBruhat φ) :
    ∃ (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
      ∀ s : ℂ, Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ ϖ : ℂˣ) : ℂ)‖ < s.re →
        Integrable (fun a : Fˣ => φ (a : F) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ s) νx ∧
        (∫ a : Fˣ, φ (a : F) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ s ∂νx) *
            Q.eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)) =
          ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((m : ℂ) * s) * P.eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p

  obtain ⟨c, hc⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p μ hμ.continuous
  obtain ⟨η, t, hη1, -, hμη⟩ :=
    LanglandsTunnell.TateLocal.exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow ℚ p μ c hc

  obtain ⟨n₁, n₀, c₀, h10, hlow, hhigh, hc₀⟩ := exists_thresholds p hφ
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2

  set β : ℂ := ((μ ϖ : ℂˣ) : ℂ) with hβ
  set G : ℂ := ∫ u in U p, ((η u : ℂˣ) : ℂ) ∂νx with hG
  set I : ℤ → ℂ := fun n => ∫ u in U p, φ (((ϖ ^ n * u : Fˣ)) : F) * ((η u : ℂˣ) : ℂ) ∂νx with hI
  refine ⟨(Polynomial.C 1 - Polynomial.C β * Polynomial.X) *
      (∑ n ∈ Finset.Ico n₁ n₀, Polynomial.C (I n * β ^ n) * Polynomial.X ^ (n - n₁).toNat) +
      Polynomial.C (φ 0 * G * β ^ n₀) * Polynomial.X ^ (n₀ - n₁).toNat,
    Polynomial.C 1 - Polynomial.C β * Polynomial.X, -n₁, ?_, ?_⟩
  ·
    intro hQ
    have h := congrArg (Polynomial.eval (0 : ℂ)) hQ
    simp at h
  intro s hs

  have hnormμ : ‖((μ ϖ : ℂˣ) : ℂ)‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-t) := by
    rw [hμη ϖ, norm_mul, hη1, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (modulus_coe_pos p ϖ),
      Complex.ofReal_re, modulus_uniformizer, Real.inv_rpow (N_pos p).le, Real.rpow_neg (N_pos p).le]
  have hz : (0 : ℝ) < (s + (t : ℂ)).re := by
    rw [hnormμ, Real.logb_rpow (N_pos p) (one_lt_N p).ne'] at hs
    rw [Complex.add_re, Complex.ofReal_re]
    linarith
  have hz' : ((0 : ℕ) : ℝ) < (s + (t : ℂ)).re := by exact_mod_cast hz

  have hηfun : ∀ y : Fˣ, ((η y : ℂˣ) : ℂ) = ((μ y : ℂˣ) : ℂ) * (((modulus (y : F) : ℝ) : ℂ) ^ (t : ℂ))⁻¹ := by
    intro y
    rw [hμη y, mul_assoc, mul_inv_cancel₀ (modulus_coe_cpow_ne_zero p y _), mul_one]
  have hηlc : IsLocallyConstant fun y : Fˣ => ((η y : ℂˣ) : ℂ) := by
    have h1 : IsLocallyConstant fun y : Fˣ => ((μ y : ℂˣ) : ℂ) := hμ.comp fun u : ℂˣ => (u : ℂ)
    have h2 : IsLocallyConstant fun y : Fˣ => (((modulus (y : F) : ℝ) : ℂ) ^ (t : ℂ))⁻¹ :=
      (isLocallyConstant_modulus_coe p).comp fun r : ℝ => (((r : ℂ) ^ (t : ℂ)))⁻¹
    have h3 := isLocallyConstant_mul h1 h2
    have hfeq : (fun y : Fˣ => ((η y : ℂˣ) : ℂ)) =
        fun y : Fˣ => ((μ y : ℂˣ) : ℂ) * (((modulus (y : F) : ℝ) : ℂ) ^ (t : ℂ))⁻¹ := funext hηfun
    rw [hfeq]
    exact h3

  have key := LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le ℚ p
    (selfDualHaarAt ℚ p) (fun y : Fˣ => φ (y : F)) (hφ.1.comp_continuous Units.continuous_val) C 0
    (fun y => by simpa using hC (y : F)) c₀ hc₀ η hηlc 1 (fun u _ => (hη1 u).le) (hη1 ϖ) (s + (t : ℂ)) hz'
  obtain ⟨hint, -, hsum⟩ := key

  have hfun : (fun a : Fˣ => φ (a : F) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ s) =
      fun y : Fˣ => (fun y : Fˣ => φ (y : F)) y * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s + (t : ℂ)) := by
    funext y
    beta_reduce
    rw [hμη y, Complex.cpow_add _ _ (by exact_mod_cast (modulus_coe_pos p y).ne')]
    ring
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun]

  set ρ : ℂ := ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-(s + (t : ℂ))) * ((η ϖ : ℂˣ) : ℂ) with hρ
  have hρnorm : ‖ρ‖ < 1 := by
    rw [hρ, norm_mul, hη1, mul_one, norm_NC_cpow, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_N p) (by linarith)
  have hρ0 : ρ ≠ 0 := by
    rw [hρ]
    refine mul_ne_zero ?_ (Units.ne_zero _)
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (NC_ne_zero p)
  have hterm : ∀ n : ℤ, ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-((n : ℂ) * (s + (t : ℂ)))) * ((η ϖ : ℂˣ) : ℂ) ^ n *
      (∫ u in {u : Fˣ | Valued.v (u : F) = 1}, (fun y : Fˣ => φ (y : F)) (ϖ ^ n * u) * ((η u : ℂˣ) : ℂ) ∂νx) =
      ρ ^ n * I n := by
    intro n
    rw [hρ, hI, mul_zpow, ← NC_cpow_int_mul, ← U_def, neg_mul_eq_mul_neg]
  have hsum' : HasSum (fun n : ℤ => ρ ^ n * I n)
      (∫ y : Fˣ, (fun y : Fˣ => φ (y : F)) y * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s + (t : ℂ)) ∂νx) := by
    convert hsum using 1
    funext n
    exact (hterm n).symm

  have hIlow : ∀ n, n < n₁ → I n = 0 := by
    intro n hn
    rw [hI]
    beta_reduce
    rw [setIntegral_congr_fun (measurableSet_U p) (g := fun _ => (0 : ℂ)) fun u hu => by
      beta_reduce; rw [hlow n u hu hn, zero_mul]]
    simp
  have hIhigh : ∀ n, n₀ ≤ n → I n = φ 0 * G := by
    intro n hn
    rw [hI, hG, ← integral_const_mul]
    beta_reduce
    exact setIntegral_congr_fun (measurableSet_U p) fun u hu => by rw [hhigh n u hu hn]
  have hS := hasSum_unique_of_shells hρnorm hρ0 h10 (fun n => rfl) hIlow hIhigh hsum'
  rw [hS]

  set X : ℂ := ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s) with hX
  have hX0 : X ≠ 0 := by
    rw [hX, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (NC_ne_zero p)
  have hNt : ((modulus ((ϖ : Fˣ) : F) : ℝ) : ℂ) ^ (t : ℂ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-(t : ℂ)) := by
    rw [modulus_uniformizer, ← Complex.ofReal_cpow (inv_nonneg.mpr (N_pos p).le), Real.inv_rpow (N_pos p).le,
      ← Real.rpow_neg (N_pos p).le, Complex.ofReal_cpow (N_pos p).le]
    push_cast
    rfl
  have hρX : ρ = β * X := by
    rw [hρ, hβ, hX, hμη ϖ, hNt, neg_add, Complex.cpow_add _ _ (NC_ne_zero p)]
    ring
  have hm : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (((-n₁ : ℤ) : ℂ) * s) = X ^ n₁ := by
    rw [hX, ← NC_cpow_int_mul]
    congr 1
    push_cast
    ring
  have h1ρ : (1 - ρ) ≠ 0 := by
    intro h
    have : ‖ρ‖ = 1 := by rw [(sub_eq_zero.mp h).symm, norm_one]
    linarith
  have hXpow : ∀ n : ℤ, n₁ ≤ n → X ^ n₁ * X ^ (n - n₁).toNat = X ^ n := by
    intro n hn
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hn), ← zpow_add₀ hX0]
    congr 1; ring
  rw [hm]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_finsetSum]
  rw [hρX]

  have hL : ((∑ n ∈ Finset.Ico n₁ n₀, (β * X) ^ n * I n) + φ 0 * G * (β * X) ^ n₀ * (1 - β * X)⁻¹) * (1 - β * X) =
      (1 - β * X) * (∑ n ∈ Finset.Ico n₁ n₀, (β * X) ^ n * I n) + φ 0 * G * (β * X) ^ n₀ := by
    rw [hρX] at h1ρ
    field_simp
  rw [hL, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ico] at hn
    have e := hXpow n hn.1
    rw [mul_zpow]
    calc (1 - β * X) * (β ^ n * X ^ n * I n) = (1 - β * X) * (I n * β ^ n * (X ^ n₁ * X ^ (n - n₁).toNat)) := by
          rw [e]; ring
      _ = X ^ n₁ * ((1 - β * X) * (I n * β ^ n * X ^ (n - n₁).toNat)) := by ring
  · rw [mul_zpow]
    calc φ 0 * G * (β ^ n₀ * X ^ n₀) = φ 0 * G * β ^ n₀ * (X ^ n₁ * X ^ (n₀ - n₁).toNat) := by
          rw [hXpow n₀ h10]; ring
      _ = X ^ n₁ * (φ 0 * G * β ^ n₀ * X ^ (n₀ - n₁).toNat) := by ring

end T0R

end

open T0R in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ)
    (φ : p.adicCompletion ℚ → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    ∃ (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
      ∀ s : ℂ, Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ < s.re →
        Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
          φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ a : (p.adicCompletion ℚ)ˣ,
            φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  exact T0R.main p μ hμ φ hφ

end S_LanglandsTunnell_TateLocal_exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re (solution)
