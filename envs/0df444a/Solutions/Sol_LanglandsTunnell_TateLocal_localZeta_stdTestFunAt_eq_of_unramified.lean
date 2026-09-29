-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d8e3de82-a727-53ab-8a13-c7a96c05f8f4

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain NumberField.AdelicTrace NumberField.AdelicBox

open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt localLFactorAt_of_hasConductorExponentAt_zero modulus modulus_coe_units charExt charExt_zero charExt_coe_units mulMeasure localZeta modulus_adicCompletion_eq_nnnorm"
namespace UnramB
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] localBorel borelSpace_localBorel

private theorem absNorm_ne_zero' : Ideal.absNorm v.asIdeal ≠ 0 :=
  Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot

private theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 := absNorm_ne_zero' K v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private def unitSphere : Set (v.adicCompletion K) := {x | Valued.v x = 1}

private def shell (m : ℕ) : Set (v.adicCompletion K) :=
  {x | Valued.v x = WithZero.exp (-(m : ℤ))}

private theorem mem_unitSphere {x : v.adicCompletion K} :
    x ∈ unitSphere K v ↔ Valued.v x = 1 := Iff.rfl

private theorem mem_shell {m : ℕ} {x : v.adicCompletion K} :
    x ∈ shell K v m ↔ Valued.v x = WithZero.exp (-(m : ℤ)) := Iff.rfl

private theorem valued_uniformizerUnit_pow (m : ℕ) :
    Valued.v ((uniformizerUnit K v : v.adicCompletion K) ^ m) = WithZero.exp (-(m : ℤ)) := by
  rw [map_pow, valued_uniformizerUnit, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem isClopen_sphere_valued {y : v.adicCompletion K} (hy : y ≠ 0) :
    IsClopen {x : v.adicCompletion K | Valued.v x = Valued.v y} := by
  have hr : Valued.v.restrict y ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff]
    exact (Valuation.ne_zero_iff _).mpr hy
  have hset : {x : v.adicCompletion K | Valued.v x = Valued.v y}
      = {x | Valued.v.restrict x = Valued.v.restrict y} := by
    ext x
    simp only [Set.mem_setOf_eq, le_antisymm_iff, Valuation.restrict_le_iff]
  rw [hset]
  exact Valued.isClopen_sphere _ hr

private theorem measurableSet_shell (m : ℕ) : MeasurableSet (shell K v m) := by
  have hy : ((uniformizerUnit K v : v.adicCompletion K) ^ m) ≠ 0 :=
    pow_ne_zero _ (uniformizerUnit K v).ne_zero
  have h := (isClopen_sphere_valued K v hy).isOpen.measurableSet
  rw [valued_uniformizerUnit_pow] at h
  exact h

private theorem unitSphere_subset_integers :
    unitSphere K v ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun x hx => by
  rw [SetLike.mem_coe, mem_adicCompletionIntegers]
  exact le_of_eq hx

private theorem zero_notMem_shell (m : ℕ) : (0 : v.adicCompletion K) ∉ shell K v m := by
  intro h
  rw [mem_shell, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

private theorem shell_eq_smul_unitSphere (m : ℕ) :
    shell K v m = (uniformizerUnit K v ^ m) • unitSphere K v := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_unitSphere, mem_shell, Units.smul_def, smul_eq_mul,
    map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val,
    valued_uniformizerUnit_pow, inv_mul_eq_one₀ WithZero.exp_ne_zero]
  exact eq_comm

private theorem integers_diff_zero_eq_iUnion :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) \ {0} = ⋃ m : ℕ, shell K v m := by
  ext x
  simp only [Set.mem_diff, SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_singleton_iff,
    Set.mem_iUnion, mem_shell]
  constructor
  · rintro ⟨hle, hne⟩
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
    have hlog : WithZero.log (Valued.v x) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact hle
    refine ⟨(-WithZero.log (Valued.v x)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hv0]
  · rintro ⟨m, hm⟩
    refine ⟨?_, ?_⟩
    · rw [hm, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    · rintro rfl
      rw [map_zero] at hm
      exact WithZero.exp_ne_zero hm.symm

private theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell K v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_iff]
  rintro x ⟨hm, hn⟩
  rw [mem_shell] at hm hn
  apply hmn
  have h := WithZero.exp_injective (hm.symm.trans hn)
  omega

private theorem charExt_of_mem_shell {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) {m : ℕ} {x : v.adicCompletion K}
    (hx : x ∈ shell K v m) : charExt χ x = (χ (uniformizerUnit K v) : ℂ) ^ m := by
  rw [shell_eq_smul_unitSphere] at hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [mem_unitSphere] at hu
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hval : ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u
      = ((uniformizerUnit K v ^ m * Units.mk0 u hu0 : (v.adicCompletion K)ˣ)
          : v.adicCompletion K) := by
    rw [Units.val_mul, Units.val_mk0]
  rw [Units.smul_def, smul_eq_mul, hval, charExt_coe_units, map_mul, map_pow, Units.val_mul,
    Units.val_pow_eq_pow_val,
    (hasConductorExponentAt_zero_iff K v).mp hχ (Units.mk0 u hu0) (by rwa [Units.val_mk0]),
    Units.val_one, mul_one]

private theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) = Multiplicative.ofAdd n :=
    WithZero.unzero_coe _
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, h, toAdd_ofAdd]

private theorem modulus_of_mem_shell
    (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) {m : ℕ}
    {x : v.adicCompletion K} (hx : x ∈ shell K v m) :
    modulus x = ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m := by
  rw [hA x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, (mem_shell K v).mp hx,
    toNNReal_exp _ (-(m : ℤ)), zpow_neg, zpow_natCast, inv_pow]

private theorem ofReal_inv_pow_cpow (q m : ℕ) (hq : 0 < q) (s : ℂ) :
    ((((q : ℝ)⁻¹) ^ m : ℝ) : ℂ) ^ s = ((q : ℂ) ^ (-s)) ^ m := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hr : (0 : ℝ) < ((q : ℝ)⁻¹) ^ m := pow_pos (inv_pos.mpr hqR) m
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hr0 : ((((q : ℝ)⁻¹) ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_nat_mul]
  congr 1
  rw [← Complex.ofReal_log hr.le, Real.log_pow, Real.log_inv, ← Complex.ofReal_natCast q,
    ← Complex.ofReal_log hqR.le]
  push_cast
  ring

private theorem addHaar_shell (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) (m : ℕ) :
    Measure.addHaarMeasure (integersPositiveCompacts K v) (shell K v m)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m : ℝ≥0) : ℝ≥0∞)
          * Measure.addHaarMeasure (integersPositiveCompacts K v) (unitSphere K v) := by
  rw [shell_eq_smul_unitSphere,
    ← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v))
      (uniformizerUnit K v ^ m) (unitSphere K v), ← modulus_coe_units]
  congr 2
  apply modulus_of_mem_shell K v hA
  rw [mem_shell, Units.val_pow_eq_pow_val]
  exact valued_uniformizerUnit_pow K v m

private theorem mulMeasure_shell (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    {μ : Measure (v.adicCompletion K)} (m : ℕ)
    (hμ : μ (shell K v m)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m : ℝ≥0) : ℝ≥0∞)
      * μ (unitSphere K v)) :
    mulMeasure μ (shell K v m) = μ (unitSphere K v) := by
  have hS := measurableSet_shell K v m
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hqtop : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : shell K v m ⊆ {0}ᶜ := fun x hx =>
    Set.mem_compl_singleton_iff.mpr fun h0 => zero_notMem_shell K v m (h0 ▸ hx)
  have hcoe : (((((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m : ℝ≥0) : ℝ≥0∞))
      = ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹) ^ m := by
    rw [ENNReal.coe_pow, ENNReal.coe_inv hq0, ENNReal.coe_natCast]
  have hcongr : ∫⁻ x in shell K v m, ((modulus x : ℝ≥0∞))⁻¹ ∂μ
      = ∫⁻ _ in shell K v m, (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ m ∂μ := by
    refine setLIntegral_congr_fun hS fun x hx => ?_
    rw [modulus_of_mem_shell K v hA hx, hcoe, ENNReal.inv_pow, inv_inv]
  unfold mulMeasure
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS, Set.inter_eq_left.mpr hsub, hcongr,
    setLIntegral_const, hμ, ← mul_assoc, hcoe, ← mul_pow, ENNReal.mul_inv_cancel hq0' hqtop,
    one_pow, one_mul]

private theorem localZeta_indicator_integers_eq
    (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    {μ : Measure (v.adicCompletion K)}
    (hμ : ∀ m : ℕ, μ (shell K v m)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m : ℝ≥0) : ℝ≥0∞)
      * μ (unitSphere K v))
    (hfin : μ (unitSphere K v) ≠ ⊤)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : HasConductorExponentAt K v χ 0) {s : ℂ}
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta μ ((v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator
        fun _ => (1 : ℂ)) χ s
      = ((μ.real (unitSphere K v) : ℝ) : ℂ)
          * (1 - (χ (uniformizerUnit K v) : ℂ)
              * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  set c : ℂ := (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hc
  set O : Set (v.adicCompletion K) := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    with hO
  set ν : Measure (v.adicCompletion K) := mulMeasure μ with hν
  set g : v.adicCompletion K → ℂ :=
    fun x => O.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s
    with hg
  have hq : 0 < Ideal.absNorm v.asIdeal := by
    have := one_lt_absNorm K v
    omega
  have hnc : ‖c‖ < 1 := by
    rw [hc, norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
    exact hs

  have hgm : ∀ m : ℕ, ∀ x ∈ shell K v m, g x = c ^ m := by
    intro m x hx
    have hxO : x ∈ O := by
      rw [hO, SetLike.mem_coe, mem_adicCompletionIntegers, (mem_shell K v).mp hx,
        ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    show O.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s = c ^ m
    rw [Set.indicator_of_mem hxO, one_mul, charExt_of_mem_shell K v hχ hx,
      modulus_of_mem_shell K v hA hx, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast,
      ofReal_inv_pow_cpow _ m hq s, hc, mul_pow]

  have hνm : ∀ m : ℕ, ν (shell K v m) = μ (unitSphere K v) := fun m =>
    mulMeasure_shell K v hA m (hμ m)
  have hνreal : ∀ m : ℕ, ν.real (shell K v m) = μ.real (unitSphere K v) := fun m => by
    rw [measureReal_def, measureReal_def, hνm m]
  have hint : ∀ m : ℕ,
      ∫ x in shell K v m, g x ∂ν = ((μ.real (unitSphere K v) : ℝ) : ℂ) * c ^ m := by
    intro m
    rw [setIntegral_congr_fun (measurableSet_shell K v m) (hgm m), setIntegral_const, hνreal m,
      Complex.real_smul]
  have hion : ∀ m : ℕ, IntegrableOn g (shell K v m) ν := by
    intro m
    refine IntegrableOn.congr_fun (f := fun _ => c ^ m) ?_ (fun x hx => (hgm m x hx).symm)
      (measurableSet_shell K v m)
    exact integrableOn_const (by rw [hνm m]; exact hfin)
  have hnorm : ∀ m : ℕ,
      ∫ x in shell K v m, ‖g x‖ ∂ν = μ.real (unitSphere K v) * ‖c‖ ^ m := by
    intro m
    have heq : Set.EqOn (fun x => ‖g x‖) (fun _ => ‖c‖ ^ m) (shell K v m) := fun x hx => by
      show ‖g x‖ = ‖c‖ ^ m
      rw [hgm m x hx, norm_pow]
    rw [setIntegral_congr_fun (measurableSet_shell K v m) heq, setIntegral_const, hνreal m,
      smul_eq_mul]
  have hsum : Summable fun m : ℕ => ∫ x in shell K v m, ‖g x‖ ∂ν := by
    simp_rw [hnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hnc).mul_left _
  have hiU : IntegrableOn g (⋃ m, shell K v m) ν :=
    integrableOn_iUnion_of_summable_integral_norm hion hsum
  have hzero : ∀ x, x ∉ O \ {0} → g x = 0 := by
    intro x hx
    rw [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not] at hx
    show O.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s = 0
    by_cases hxO : x ∈ O
    · rw [hx hxO, charExt_zero, mul_zero, zero_mul]
    · rw [Set.indicator_of_notMem hxO, zero_mul, zero_mul]
  calc localZeta μ (O.indicator fun _ => (1 : ℂ)) χ s
      = ∫ x, g x ∂ν := rfl
    _ = ∫ x in O \ {0}, g x ∂ν := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in ⋃ m, shell K v m, g x ∂ν := by rw [hO, integers_diff_zero_eq_iUnion]
    _ = ∑' m, ∫ x in shell K v m, g x ∂ν :=
        integral_iUnion (measurableSet_shell K v) (pairwise_disjoint_shell K v) hiU
    _ = ∑' m : ℕ, ((μ.real (unitSphere K v) : ℝ) : ℂ) * c ^ m := tsum_congr hint
    _ = ((μ.real (unitSphere K v) : ℝ) : ℂ) * ∑' m : ℕ, c ^ m := tsum_mul_left
    _ = ((μ.real (unitSphere K v) : ℝ) : ℂ) * (1 - c)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hnc]

private theorem localZeta_stdTestFunAt_eq (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
      = ((selfDualHaarAt K v).real {x | Valued.v x = 1} : ℂ) * localLFactorAt K v χ s := by
  set μ₀ := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ₀
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2)
    with hc
  have hμ : selfDualHaarAt K v = c • μ₀ := rfl
  have hf : stdTestFunAt K v χ
      = (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ) := by
    unfold stdTestFunAt
    rw [if_pos hχ]
  have hshell : ∀ m : ℕ, (c • μ₀) (shell K v m)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ m : ℝ≥0) : ℝ≥0∞)
          * (c • μ₀) (unitSphere K v) := fun m => by
    rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, addHaar_shell K v hA m]
    exact mul_left_comm _ _ _
  have hO : μ₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    rw [hμ₀, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self]
  have hfin : (c • μ₀) (unitSphere K v) ≠ ⊤ := by
    rw [Measure.coe_nnreal_smul_apply]
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
    refine (lt_of_le_of_lt (measure_mono (unitSphere_subset_integers K v)) ?_).ne
    rw [hO]
    exact ENNReal.one_lt_top
  rw [hf, hμ, localZeta_indicator_integers_eq K v hA hshell hfin hχ hs,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ]
  rfl

end LanglandsTunnell.TateLocal.UnramB

end

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified.LanglandsTunnell.TateLocal NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain MeasureTheory"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
      = ((selfDualHaarAt K v).real {x | Valued.v x = 1} : ℂ) * localLFactorAt K v χ s :=
  LanglandsTunnell.TateLocal.UnramB.localZeta_stdTestFunAt_eq K v
    (LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v) χ s hχ hs

#print axioms solution

end S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified (solution)
