-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c8150e57-f929-5958-aff7-93a84a1d3898

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain NumberField.AdelicTrace NumberField.AdelicBox

open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.modulus_adicCompletion_eq_nnnorm TateLocal.tateFourier_indicator_setOf_valued_sub_le TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt stdRootNumberAt_def higherUnitsAt higherUnitsAt_antitone HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique conductorExponentAt conductorExponentAt_eq_of_hasConductorExponentAt localLFactorAt localLFactorAt_of_hasConductorExponentAt_zero localEpsilonAt localEpsilonAt_def localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_coe_units modulus_mul tateFourier charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure localZeta localGammaAt modulus_adicCompletion_eq_nnnorm tateFourier_indicator_setOf_valued_sub_le forall_eq_one_and_exists_ne_one_of_addCharLevel"
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

private theorem isOpen_unitSphere : IsOpen (unitSphere K v) := by
  have h := (isClopen_sphere_valued K v (one_ne_zero : (1 : v.adicCompletion K) ≠ 0)).isOpen
  rw [map_one] at h
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

private theorem smul_integers_eq :
    (uniformizerUnit K v) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      = {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, mem_adicCompletionIntegers,
    Set.mem_setOf_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    valued_uniformizerUnit, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]

private theorem withZero_lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]

private theorem integers_eq_unitSphere_union :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      = unitSphere K v ∪ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  ext x
  rw [SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_union, mem_unitSphere, Set.mem_setOf_eq,
    ← withZero_lt_one_iff_le_exp_neg_one]
  exact le_iff_eq_or_lt

private theorem disjoint_unitSphere_smul_integers :
    Disjoint (unitSphere K v) {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} := by
  rw [Set.disjoint_iff]
  rintro x ⟨h1, h2⟩
  rw [mem_unitSphere] at h1
  rw [Set.mem_setOf_eq, h1, ← withZero_lt_one_iff_le_exp_neg_one] at h2
  exact lt_irrefl _ h2

private theorem addHaar_unitSphere (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) :
    Measure.addHaarMeasure (integersPositiveCompacts K v) (unitSphere K v)
      = 1 - (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  set μ₀ := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ₀
  have hO : μ₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    rw [hμ₀, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hmem : (uniformizerUnit K v : v.adicCompletion K) ∈ shell K v 1 := by
    rw [mem_shell, Nat.cast_one]
    exact valued_uniformizerUnit K v
  have hS : μ₀ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
    rw [← smul_integers_eq,
      ← distribHaarChar_mul μ₀ (uniformizerUnit K v)
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)),
      hO, mul_one, ← modulus_coe_units, modulus_of_mem_shell K v hA hmem, pow_one,
      ENNReal.coe_inv hq0, ENNReal.coe_natCast]
  have hsum : μ₀ (unitSphere K v) + μ₀ {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)} = 1 := by
    rw [← measure_union' (disjoint_unitSphere_smul_integers K v)
      (isOpen_unitSphere K v).measurableSet, ← integers_eq_unitSphere_union, hO]
  rw [hS] at hsum
  exact ENNReal.eq_sub_of_add_eq (ENNReal.inv_ne_top.mpr hq0') hsum

private theorem selfDualHaarAt_eq_smul :
    selfDualHaarAt K v = ((Ideal.absNorm v.asIdeal : ℝ≥0)
        ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2))
          • Measure.addHaarMeasure (integersPositiveCompacts K v) :=
  rfl

private theorem selfDualHaarAt_real_unitSphere (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) :
    (selfDualHaarAt K v).real (unitSphere K v)
      = (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
          * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) := by
  have hq1 : (1 : ℝ≥0∞) ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
    exact_mod_cast (one_lt_absNorm K v).le
  rw [selfDualHaarAt_eq_smul, measureReal_nnreal_smul_apply, measureReal_def,
    addHaar_unitSphere K v hA, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hq1)
      ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    NNReal.coe_rpow, NNReal.coe_natCast, mul_comm]

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

private theorem localZeta_stdTestFunAt_ne_zero (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s ≠ 0 := by
  have hq1 : 1 < Ideal.absNorm v.asIdeal := one_lt_absNorm K v
  have hq : 0 < Ideal.absNorm v.asIdeal := by omega
  have hqR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  rw [localZeta_stdTestFunAt_eq K v hA χ s hχ hs,
    show {x : v.adicCompletion K | Valued.v x = 1} = unitSphere K v from rfl,
    selfDualHaarAt_real_unitSphere K v hA, localLFactorAt_of_hasConductorExponentAt_zero K v hχ]
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [Complex.ofReal_ne_zero]
    refine mul_ne_zero (sub_ne_zero.mpr ?_) (Real.rpow_pos_of_pos hqR0 _).ne'
    exact (inv_lt_one_of_one_lt₀ hqR).ne'
  · refine sub_ne_zero.mpr fun h => ?_
    have hn : ‖(χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
      exact hs
    rw [← h, norm_one] at hn
    exact lt_irrefl _ hn

end LanglandsTunnell.TateLocal.UnramB

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.modulus_adicCompletion_eq_nnnorm TateLocal.tateFourier_indicator_setOf_valued_sub_le TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt stdRootNumberAt_def higherUnitsAt higherUnitsAt_antitone HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique conductorExponentAt conductorExponentAt_eq_of_hasConductorExponentAt localLFactorAt localLFactorAt_of_hasConductorExponentAt_zero localEpsilonAt localEpsilonAt_def localEpsilonAt_of_not_hasConductorExponentAt_zero modulus modulus_coe_units modulus_mul tateFourier charExt charExt_zero charExt_of_ne_zero charExt_coe_units mulMeasure localZeta localGammaAt modulus_adicCompletion_eq_nnnorm tateFourier_indicator_setOf_valued_sub_le forall_eq_one_and_exists_ne_one_of_addCharLevel"
namespace UnramTwist
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

open LanglandsTunnell.TateLocal.UnramB

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] localBorel borelSpace_localBorel

private theorem psiLocal_eq_one_of_valued_le_one (x : v.adicCompletion K) (hx : Valued.v x ≤ 1) :
    psiLocal K v x = 1 := by
  rw [psiLocal_apply, show stdAddChar K = (adelicTraceData K).psiK from rfl,
    AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch ((adelicTraceData K).traceInf 0)
      * psiFin (traceFinHom K (finAdeleSingleAt K v x)) = 1
  have hint : ∀ w : HeightOneSpectrum (𝓞 K),
      finAdeleSingleAt K v x w ∈ w.adicCompletionIntegers K := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [finAdeleSingleAt_apply_self]
      exact hx
    · rw [finAdeleSingleAt_apply_of_ne K v x hw]
      exact zero_mem _
  let z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K := fun w => ⟨_, hint w⟩
  have hsm : RestrictedProduct.structureMap
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z
      = finAdeleSingleAt K v x :=
    RestrictedProduct.ext _ _ fun w => rfl
  rw [← hsm, traceFinHom_structureMap, map_zero, AddChar.map_zero_eq_one, one_mul]
  exact psiFin_eq_one_of_forall_mem _ fun w => (traceInt K z w).2

private theorem eq_one_of_mem_higherUnitsAt {ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) {m : ℕ} {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v m) : ω u = 1 :=
  hω.1 u (higherUnitsAt_antitone K v (Nat.zero_le m) hu)

private theorem hasConductorExponentAt_inv_zero {ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) : HasConductorExponentAt K v ω⁻¹ 0 := by
  rw [hasConductorExponentAt_zero_iff] at hω ⊢
  intro u hu
  rw [MonoidHom.inv_apply, hω u hu, inv_one]

private theorem hasConductorExponentAt_mul {χ ω : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (hχ : HasConductorExponentAt K v χ c) (hω : HasConductorExponentAt K v ω 0) :
    HasConductorExponentAt K v (χ * ω) c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hχ.1 u hu, eq_one_of_mem_higherUnitsAt K v hω hu, one_mul]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.mul_apply, eq_one_of_mem_higherUnitsAt K v hω hu, mul_one]⟩

private theorem hasConductorExponentAt_mul_iff {χ ω : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (hω : HasConductorExponentAt K v ω 0) :
    HasConductorExponentAt K v (χ * ω) c ↔ HasConductorExponentAt K v χ c := by
  refine ⟨fun h => ?_, fun h => hasConductorExponentAt_mul K v h hω⟩
  have h' := hasConductorExponentAt_mul K v h (hasConductorExponentAt_inv_zero K v hω)
  have e : χ * ω * ω⁻¹ = χ := MonoidHom.ext fun u => by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right]
  rwa [e] at h'

private theorem conductorExponentAt_mul {χ ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) :
    conductorExponentAt K v (χ * ω) = conductorExponentAt K v χ := by
  unfold conductorExponentAt
  congr 1
  ext c
  exact hasConductorExponentAt_mul_iff K v hω

private theorem stdTestFunAt_mul {χ ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) :
    stdTestFunAt K v (χ * ω) = stdTestFunAt K v χ := by
  unfold stdTestFunAt
  rw [conductorExponentAt_mul K v hω]
  by_cases h : HasConductorExponentAt K v χ 0
  · rw [if_pos h, if_pos ((hasConductorExponentAt_mul_iff K v hω).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((hasConductorExponentAt_mul_iff K v hω).mp h'))]

private theorem hasConductorExponentAt_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (hχ : HasConductorExponentAt K v χ c) : HasConductorExponentAt K v χ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, fun h => hne (by rwa [MonoidHom.inv_apply, inv_eq_one] at h)⟩

private theorem charExt_mul (θ₁ θ₂ : (v.adicCompletion K)ˣ →* ℂˣ) (y : v.adicCompletion K) :
    charExt (θ₁ * θ₂) y = charExt θ₁ y * charExt θ₂ y := by
  by_cases hy : y = 0
  · rw [hy, charExt_zero, charExt_zero, zero_mul]
  · rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy, MonoidHom.mul_apply,
      Units.val_mul]

private theorem inv_mul_inv (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) : (χ * ω)⁻¹ = χ⁻¹ * ω⁻¹ :=
  MonoidHom.ext fun u => by
    rw [MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
      MonoidHom.inv_apply, mul_inv]

private def shellZ (k : ℤ) : Set (v.adicCompletion K) := {x | Valued.v x = WithZero.exp (-k)}

private theorem mem_shellZ {k : ℤ} {x : v.adicCompletion K} :
    x ∈ shellZ K v k ↔ Valued.v x = WithZero.exp (-k) := Iff.rfl

private theorem valued_uniformizerUnit_zpow (k : ℤ) :
    Valued.v (((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ)) : v.adicCompletion K)
      = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem measurableSet_shellZ (k : ℤ) : MeasurableSet (shellZ K v k) := by
  have hy : (((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := (isClopen_sphere_valued K v hy).isOpen.measurableSet
  rw [valued_uniformizerUnit_zpow] at h
  exact h

private theorem zero_notMem_shellZ (k : ℤ) : (0 : v.adicCompletion K) ∉ shellZ K v k := by
  intro h
  rw [mem_shellZ, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

private theorem ne_zero_of_mem_shellZ {k : ℤ} {x : v.adicCompletion K} (hx : x ∈ shellZ K v k) : x ≠ 0 :=
  fun h0 => zero_notMem_shellZ K v k (h0 ▸ hx)

private theorem shellZ_eq_smul_unitSphere (k : ℤ) :
    shellZ K v k = (uniformizerUnit K v ^ k) • unitSphere K v := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_unitSphere, mem_shellZ, Units.smul_def, smul_eq_mul,
    map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit_zpow,
    inv_mul_eq_one₀ WithZero.exp_ne_zero]
  exact eq_comm

private theorem ball_diff_zero_eq_iUnion (N : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp N} \ {0}
      = ⋃ j : ℕ, shellZ K v (-N + j) := by
  ext x
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_iUnion, mem_shellZ]
  constructor
  · rintro ⟨hle, hne⟩
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
    have hlog : WithZero.log (Valued.v x) ≤ N := by
      rw [WithZero.log_le_iff_le_exp hv0]
      exact hle
    refine ⟨(N - WithZero.log (Valued.v x)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    have e : -(-N + (N - WithZero.log (Valued.v x))) = WithZero.log (Valued.v x) := by ring
    rw [e, WithZero.exp_log hv0]
  · rintro ⟨j, hj⟩
    refine ⟨?_, ?_⟩
    · rw [hj]
      exact WithZero.exp_le_exp.mpr (by omega)
    · rintro rfl
      rw [map_zero] at hj
      exact WithZero.exp_ne_zero hj.symm

private theorem pairwise_disjoint_shellZ (N : ℤ) :
    Pairwise (Function.onFun Disjoint fun j : ℕ => shellZ K v (-N + j)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_iff]
  rintro x ⟨hi, hj⟩
  rw [mem_shellZ] at hi hj
  apply hij
  have h := WithZero.exp_injective (hi.symm.trans hj)
  omega

private theorem mem_shellZ_neg_log {x : v.adicCompletion K} (hx : x ≠ 0) :
    x ∈ shellZ K v (-WithZero.log (Valued.v x)) := by
  rw [mem_shellZ, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)]

private theorem modulus_of_mem_shellZ (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) {k : ℤ}
    {x : v.adicCompletion K} (hx : x ∈ shellZ K v k) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-k) := by
  rw [hA x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, (mem_shellZ K v).mp hx, toNNReal_exp _ (-k),
    NNReal.coe_zpow]

private theorem charExt_of_mem_shellZ {ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) {k : ℤ} {x : v.adicCompletion K}
    (hx : x ∈ shellZ K v k) : charExt ω x = (ω (uniformizerUnit K v) : ℂ) ^ k := by
  rw [shellZ_eq_smul_unitSphere] at hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [mem_unitSphere] at hu
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hval : ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u
      = ((uniformizerUnit K v ^ k * Units.mk0 u hu0 : (v.adicCompletion K)ˣ)
          : v.adicCompletion K) := by
    rw [Units.val_mul, Units.val_mk0]
  rw [Units.smul_def, smul_eq_mul, hval, charExt_coe_units, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val,
    (hasConductorExponentAt_zero_iff K v).mp hω (Units.mk0 u hu0) (by rwa [Units.val_mk0]),
    Units.val_one, mul_one]

private theorem addHaar_shellZ (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊) (k : ℤ) :
    Measure.addHaarMeasure (integersPositiveCompacts K v) (shellZ K v k)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-k) : ℝ≥0) : ℝ≥0∞)
          * Measure.addHaarMeasure (integersPositiveCompacts K v) (unitSphere K v) := by
  rw [shellZ_eq_smul_unitSphere,
    ← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v))
      (uniformizerUnit K v ^ k) (unitSphere K v), ← modulus_coe_units]
  congr 2
  apply modulus_of_mem_shellZ K v hA
  rw [mem_shellZ]
  exact valued_uniformizerUnit_zpow K v k

private theorem mulMeasure_restrict_shellZ (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (μ : Measure (v.adicCompletion K)) (k : ℤ) :
    (mulMeasure μ).restrict (shellZ K v k)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k : ℝ≥0) : ℝ≥0∞) • μ.restrict (shellZ K v k) := by
  have hS := measurableSet_shellZ K v k
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  have hsub : shellZ K v k ⊆ {0}ᶜ := fun x hx =>
    Set.mem_compl_singleton_iff.mpr (ne_zero_of_mem_shellZ K v hx)
  ext S hSm
  have hcongr : ∫⁻ x in S ∩ shellZ K v k, ((modulus x : ℝ≥0∞))⁻¹ ∂μ
      = ∫⁻ _ in S ∩ shellZ K v k, ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k : ℝ≥0) : ℝ≥0∞) ∂μ := by
    refine setLIntegral_congr_fun (hSm.inter hS) fun x hx => ?_
    rw [modulus_of_mem_shellZ K v hA hx.2, zpow_neg, ENNReal.coe_inv (zpow_ne_zero _ hq0), inv_inv]
  rw [Measure.restrict_apply hSm, Measure.smul_apply, Measure.restrict_apply hSm, smul_eq_mul]
  unfold mulMeasure
  rw [withDensity_apply _ (hSm.inter hS), Measure.restrict_restrict (hSm.inter hS),
    Set.inter_eq_left.mpr (Set.inter_subset_right.trans hsub), hcongr, setLIntegral_const]

private theorem mulMeasure_shellZ (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    {μ : Measure (v.adicCompletion K)} (k : ℤ)
    (hμ : μ (shellZ K v k)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-k) : ℝ≥0) : ℝ≥0∞) * μ (unitSphere K v)) :
    mulMeasure μ (shellZ K v k) = μ (unitSphere K v) := by
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_ne_zero' K v)
  rw [← Measure.restrict_apply_self, mulMeasure_restrict_shellZ K v hA μ k, Measure.smul_apply,
    Measure.restrict_apply_self, hμ, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, ← zpow_add₀ hq0,
    add_neg_cancel, zpow_zero, ENNReal.coe_one, one_mul]

private theorem ofReal_zpow_neg_cpow (q : ℕ) (hq : 0 < q) (m : ℤ) (s : ℂ) :
    (((q : ℝ) ^ (-m) : ℝ) : ℂ) ^ s = ((q : ℂ) ^ (-s)) ^ m := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hr : (0 : ℝ) < (q : ℝ) ^ (-m) := zpow_pos hqR _
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hr0 : (((q : ℝ) ^ (-m) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul]
  congr 1
  rw [← Complex.ofReal_log hr.le, Real.log_zpow, ← Complex.ofReal_natCast q,
    ← Complex.ofReal_log hqR.le]
  push_cast
  ring

private theorem localZeta_indicator_ball_eq (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    {μ : Measure (v.adicCompletion K)}
    (hμ : ∀ k : ℤ, μ (shellZ K v k)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-k) : ℝ≥0) : ℝ≥0∞) * μ (unitSphere K v))
    (hfin : μ (unitSphere K v) ≠ ⊤)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : HasConductorExponentAt K v χ 0) {s : ℂ}
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) (N : ℤ) :
    localZeta μ ({x : v.adicCompletion K | Valued.v x ≤ WithZero.exp N}.indicator fun _ => (1 : ℂ))
        χ s
      = ((μ.real (unitSphere K v) : ℝ) : ℂ)
          * ((χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-N)
          * (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  set c : ℂ := (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hc
  set B : Set (v.adicCompletion K) := {x | Valued.v x ≤ WithZero.exp N} with hB
  set ν : Measure (v.adicCompletion K) := mulMeasure μ with hν
  set g : v.adicCompletion K → ℂ :=
    fun x => B.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s with hg
  have hq : 0 < Ideal.absNorm v.asIdeal := by
    have := one_lt_absNorm K v
    omega
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hnc : ‖c‖ < 1 := by
    rw [hc, norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
    exact hs
  have hc0 : c ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) fun h => ?_
    rw [Complex.cpow_eq_zero_iff] at h
    exact hq0 h.1

  have hgm : ∀ j : ℕ, ∀ x ∈ shellZ K v (-N + j), g x = c ^ (-N) * c ^ j := by
    intro j x hx
    have hxB : x ∈ B := by
      rw [hB, Set.mem_setOf_eq, (mem_shellZ K v).mp hx]
      exact WithZero.exp_le_exp.mpr (by omega)
    show B.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s = _
    rw [Set.indicator_of_mem hxB, one_mul, charExt_of_mem_shellZ K v hχ hx,
      modulus_of_mem_shellZ K v hA hx, NNReal.coe_zpow, NNReal.coe_natCast,
      ofReal_zpow_neg_cpow _ hq (-N + j) s, ← mul_zpow, ← hc, ← zpow_natCast c j, ← zpow_add₀ hc0]

  have hνm : ∀ j : ℕ, ν (shellZ K v (-N + j)) = μ (unitSphere K v) := fun j =>
    mulMeasure_shellZ K v hA (-N + j) (hμ _)
  have hνreal : ∀ j : ℕ, ν.real (shellZ K v (-N + j)) = μ.real (unitSphere K v) := fun j => by
    rw [measureReal_def, measureReal_def, hνm j]
  have hint : ∀ j : ℕ, ∫ x in shellZ K v (-N + j), g x ∂ν
      = ((μ.real (unitSphere K v) : ℝ) : ℂ) * (c ^ (-N) * c ^ j) := by
    intro j
    rw [setIntegral_congr_fun (measurableSet_shellZ K v _) (hgm j), setIntegral_const, hνreal j,
      Complex.real_smul]
  have hion : ∀ j : ℕ, IntegrableOn g (shellZ K v (-N + j)) ν := by
    intro j
    refine IntegrableOn.congr_fun (f := fun _ => c ^ (-N) * c ^ j) ?_
      (fun x hx => (hgm j x hx).symm) (measurableSet_shellZ K v _)
    exact integrableOn_const (by rw [hνm j]; exact hfin)
  have hnorm : ∀ j : ℕ,
      ∫ x in shellZ K v (-N + j), ‖g x‖ ∂ν = μ.real (unitSphere K v) * (‖c ^ (-N)‖ * ‖c‖ ^ j) := by
    intro j
    have heq : Set.EqOn (fun x => ‖g x‖) (fun _ => ‖c ^ (-N)‖ * ‖c‖ ^ j) (shellZ K v (-N + j)) :=
      fun x hx => by
        show ‖g x‖ = ‖c ^ (-N)‖ * ‖c‖ ^ j
        rw [hgm j x hx, norm_mul, norm_pow]
    rw [setIntegral_congr_fun (measurableSet_shellZ K v _) heq, setIntegral_const, hνreal j,
      smul_eq_mul]
  have hsum : Summable fun j : ℕ => ∫ x in shellZ K v (-N + j), ‖g x‖ ∂ν := by
    simp_rw [hnorm]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hnc).mul_left _).mul_left _
  have hiU : IntegrableOn g (⋃ j : ℕ, shellZ K v (-N + j)) ν :=
    integrableOn_iUnion_of_summable_integral_norm hion hsum
  have hzero : ∀ x, x ∉ B \ {0} → g x = 0 := by
    intro x hx
    rw [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not] at hx
    show B.indicator (fun _ => (1 : ℂ)) x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s = 0
    by_cases hxB : x ∈ B
    · rw [hx hxB, charExt_zero, mul_zero, zero_mul]
    · rw [Set.indicator_of_notMem hxB, zero_mul, zero_mul]
  calc localZeta μ (B.indicator fun _ => (1 : ℂ)) χ s
      = ∫ x, g x ∂ν := rfl
    _ = ∫ x in B \ {0}, g x ∂ν := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in ⋃ j : ℕ, shellZ K v (-N + j), g x ∂ν := by
        rw [show B \ {0} = ⋃ j : ℕ, shellZ K v (-N + j) from ball_diff_zero_eq_iUnion K v N]
    _ = ∑' j : ℕ, ∫ x in shellZ K v (-N + j), g x ∂ν :=
        integral_iUnion (fun j => measurableSet_shellZ K v _) (pairwise_disjoint_shellZ K v N) hiU
    _ = ∑' j : ℕ, ((μ.real (unitSphere K v) : ℝ) : ℂ) * (c ^ (-N) * c ^ j) := tsum_congr hint
    _ = ((μ.real (unitSphere K v) : ℝ) : ℂ) * (c ^ (-N) * ∑' j : ℕ, c ^ j) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = ((μ.real (unitSphere K v) : ℝ) : ℂ) * c ^ (-N) * (1 - c)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hnc, mul_assoc]

private theorem tateFourier_smul_measure (ψ : AddChar (v.adicCompletion K) ℂ) (κ : ℝ≥0)
    (μ : Measure (v.adicCompletion K)) (f : v.adicCompletion K → ℂ) :
    tateFourier ψ (κ • μ) f = fun y => (κ : ℂ) * tateFourier ψ μ f y := by
  funext y
  unfold tateFourier
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem localZeta_smul_measure (κ : ℝ≥0) (μ : Measure (v.adicCompletion K))
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localZeta (κ • μ) f χ s = (κ : ℂ) * localZeta μ f χ s := by
  have h : mulMeasure (κ • μ) = κ • mulMeasure μ := by
    unfold mulMeasure
    rw [ENNReal.smul_def, ENNReal.smul_def, Measure.restrict_smul, withDensity_smul_measure]
  unfold localZeta
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem localZeta_const_mul (μ : Measure (v.adicCompletion K)) (a : ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (fun y => a * f y) χ s = a * localZeta μ f χ s := by
  unfold localZeta
  have e : (fun x => a * f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      = fun x => a * (f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) := by
    funext x
    ring
  rw [e, integral_const_mul]

private theorem image_higherUnitsAt_eq {c : ℕ} (hc : 1 ≤ c) :
    ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v c
      = {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(c : ℤ))} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases hu.2 with h0 | h
    · omega
    · exact h
  · intro hx
    have hlt : Valued.v (x - 1) < 1 := lt_of_le_of_lt hx (by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega))
    have hx1 : Valued.v x = 1 := by
      have h := Valued.v.map_one_add_of_lt hlt
      rwa [add_sub_cancel] at h
    have hx0 : x ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hx1
      exact zero_ne_one hx1
    exact ⟨Units.mk0 x hx0, ⟨by rwa [Units.val_mk0], Or.inr (by rwa [Units.val_mk0])⟩, Units.val_mk0 hx0⟩

private theorem image_higherUnitsAt_subset_unitSphere (c : ℕ) :
    ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v c ⊆ unitSphere K v := by
  rintro _ ⟨u, hu, rfl⟩
  exact hu.1

private theorem stdTestFunAt_eq_of_pos {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (hc : 1 ≤ c)
    (hχ : HasConductorExponentAt K v χ c) :
    stdTestFunAt K v χ
      = {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(c : ℤ))}.indicator
          fun _ => (1 : ℂ) := by
  have h0 : ¬ HasConductorExponentAt K v χ 0 := fun h => by
    have := hasConductorExponentAt_unique K v hχ h
    omega
  unfold stdTestFunAt
  rw [if_neg h0, conductorExponentAt_eq_of_hasConductorExponentAt K v hχ,
    image_higherUnitsAt_eq K v hc]

private theorem localZeta_testFun_mul {χ ω : (v.adicCompletion K)ˣ →* ℂˣ}
    (hω : HasConductorExponentAt K v ω 0) (c : ℕ) (μ : Measure (v.adicCompletion K)) (s : ℂ) :
    localZeta μ ((((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v c).indicator
        fun _ => (1 : ℂ)) (χ * ω) s
      = localZeta μ ((((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ''
          higherUnitsAt K v c).indicator fun _ => (1 : ℂ)) χ s := by
  unfold localZeta
  congr 1
  funext x
  by_cases hx : x ∈ ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v c
  · obtain ⟨u, hu, rfl⟩ := hx
    rw [charExt_coe_units, charExt_coe_units, MonoidHom.mul_apply,
      eq_one_of_mem_higherUnitsAt K v hω hu, mul_one]
  · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul, zero_mul, zero_mul]

section Dual

private theorem continuousOn_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (hχ : HasConductorExponentAt K v χ c) : ContinuousOn (charExt χ) {0}ᶜ := by
  intro y₀ hy₀
  rw [Set.mem_compl_singleton_iff] at hy₀
  have hv₀ : Valued.v y₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hy₀
  set t : v.adicCompletion K := (uniformizerUnit K v : v.adicCompletion K) ^ c * y₀ with ht
  have hvt : Valued.v t = WithZero.exp (-(c : ℤ)) * Valued.v y₀ := by
    rw [ht, map_mul, valued_uniformizerUnit_pow]
  have ht0 : Valued.v.restrict t ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvt]
    exact mul_ne_zero WithZero.exp_ne_zero hv₀
  apply ContinuousAt.continuousWithinAt
  refine (continuousAt_const (y := charExt χ y₀)).congr ?_
  refine Filter.eventually_of_mem (Valued.mem_nhds.mpr ⟨Units.mk0 _ ht0, subset_rfl⟩) fun y hy => ?_
  rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, hvt] at hy
  have hle1 : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hlt : Valued.v (y - y₀) < Valued.v y₀ := lt_of_lt_of_le hy (mul_le_of_le_one_left' hle1)
  have hvy : Valued.v y = Valued.v y₀ := by
    have h := Valued.v.map_add_eq_of_lt_left hlt
    rwa [add_sub_cancel] at h
  have hy0 : y ≠ 0 := fun h0 => hv₀ (by rw [← hvy, h0, map_zero])
  set u : (v.adicCompletion K)ˣ := Units.mk0 y hy0 * (Units.mk0 y₀ hy₀)⁻¹ with hu
  have hvu : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul, map_inv₀, hvy,
      mul_inv_cancel₀ hv₀]
  have hu1 : Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
    have e : (u : v.adicCompletion K) - 1 = (y - y₀) * y₀⁻¹ := by
      rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, sub_mul,
        mul_inv_cancel₀ hy₀]
    rw [e, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr hv₀)]
    exact hy.le
  have humem : u ∈ higherUnitsAt K v c := by
    refine ⟨hvu, ?_⟩
    rcases Nat.eq_zero_or_pos c with h | h
    · exact Or.inl h
    · exact Or.inr hu1
  show charExt χ y₀ = charExt χ y
  have e : Units.mk0 y hy0 = Units.mk0 y₀ hy₀ * u := by
    rw [hu, mul_comm (Units.mk0 y hy0), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [charExt_of_ne_zero χ hy₀, charExt_of_ne_zero χ hy0, e, map_mul, hχ.1 u humem, mul_one]

private theorem aestronglyMeasurable_dual (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (μ : Measure (v.adicCompletion K)) {ψ : AddChar (v.adicCompletion K) ℂ} (hψc : Continuous ψ)
    (C : ℂ) {B : Set (v.adicCompletion K)} (hB : MeasurableSet B) {θ : (v.adicCompletion K)ˣ →* ℂˣ}
    {c : ℕ} (hθ : HasConductorExponentAt K v θ c) (s : ℂ) :
    AEStronglyMeasurable (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt θ⁻¹ y
      * ((modulus y : ℝ) : ℂ) ^ s) (mulMeasure μ) := by
  have hmod : (fun y : v.adicCompletion K => ((modulus y : ℝ) : ℂ) ^ s)
      = fun y => ((‖y‖ : ℝ) : ℂ) ^ s := by
    funext y
    rw [hA y, coe_nnnorm]
  have h0 : AEStronglyMeasurable (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt θ⁻¹ y
      * ((modulus y : ℝ) : ℂ) ^ s) (μ.restrict {0}ᶜ) := by
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact ((hψc.measurable.mul measurable_const).mul (measurable_const.indicator hB)).aestronglyMeasurable
    · exact (continuousOn_charExt K v (hasConductorExponentAt_inv K v hθ)).aestronglyMeasurable
        (MeasurableSet.compl (MeasurableSet.singleton 0))
    · rw [hmod]
      exact ((Complex.measurable_ofReal.comp measurable_norm).pow_const s).aestronglyMeasurable
  unfold mulMeasure
  exact h0.mono_ac (withDensity_absolutelyContinuous _ _)

private theorem setIntegral_shellZ_eq_zero (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [μ.Regular] {ψ : AddChar (v.adicCompletion K) ℂ} {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (hc : 1 ≤ c) (hχ : HasConductorExponentAt K v χ c)
    {k : ℤ} (hk : -(n + c) < k) (C : ℂ) (s : ℂ) :
    ∫ y in shellZ K v k, ψ y * C * charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s ∂(mulMeasure μ) = 0 := by
  set T : Set (v.adicCompletion K) := shellZ K v k with hT
  set g : v.adicCompletion K → ℂ :=
    fun y => ψ y * C * charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s with hg
  have hTm : MeasurableSet T := measurableSet_shellZ K v k

  have hν : ∫ y in T, g y ∂(mulMeasure μ)
      = (((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k : ℝ≥0) : ℝ≥0∞)).toReal • ∫ y in T, g y ∂μ := by
    show ∫ y, g y ∂((mulMeasure μ).restrict T) = _
    rw [mulMeasure_restrict_shellZ K v hA μ k, integral_smul_measure]
  show ∫ y in T, g y ∂(mulMeasure μ) = 0
  rw [hν]

  set j : ℕ := (-k - n).toNat with hj
  have hjk : -k - n ≤ (j : ℤ) := by
    rw [hj]
    exact Int.self_le_toNat (-k - n)
  have hjc : j < c := by
    rw [hj]
    omega
  obtain ⟨w, hw, hχw⟩ := hχ.2 j hjc
  have hvw : Valued.v (w : v.adicCompletion K) = 1 := hw.1
  have hw1 : Valued.v ((w : v.adicCompletion K) - 1) ≤ WithZero.exp (-(j : ℤ)) := by
    rcases hw.2 with h0 | h
    · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      calc Valued.v ((w : v.adicCompletion K) - 1)
          ≤ max (Valued.v (w : v.adicCompletion K)) (Valued.v (1 : v.adicCompletion K)) :=
            Valuation.map_sub _ _ _
        _ = 1 := by rw [hvw, map_one, max_self]
    · exact h
  have hmodw : modulus (w : v.adicCompletion K) = 1 := by
    rw [hA]
    apply NNReal.coe_injective
    rw [coe_nnnorm, NumberField.FinitePlace.norm_def, hvw, map_one, NNReal.coe_one]
  have hdist : distribHaarChar (v.adicCompletion K) w = 1 := by rw [← modulus_coe_units, hmodw]

  have hdist' : distribHaarChar (v.adicCompletion K) w⁻¹ = 1 := by rw [map_inv, hdist, inv_one]
  set e : v.adicCompletion K ≃ᵐ v.adicCompletion K :=
    MeasurableEquiv.mulLeft₀ (w : v.adicCompletion K) w.ne_zero with he
  have he' : ∀ y : v.adicCompletion K, e y = (w : v.adicCompletion K) * y := fun _ => rfl
  have hmap : Measure.map e μ = μ := by
    ext S hS
    have hpre : e ⁻¹' S = w⁻¹ • S := Set.ext fun y => by
      rw [Set.mem_preimage, he', Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
    rw [Measure.map_apply e.measurable hS, hpre, ← distribHaarChar_mul μ w⁻¹ S, hdist', ENNReal.coe_one,
      one_mul]
  have hinv : ∫ y, T.indicator g ((w : v.adicCompletion K) * y) ∂μ = ∫ y, T.indicator g y ∂μ := by
    have h := integral_map_equiv (μ := μ) e (T.indicator g)
    rw [hmap] at h
    simp_rw [he'] at h
    exact h.symm

  have hmemT : ∀ y, (w : v.adicCompletion K) * y ∈ T ↔ y ∈ T := fun y => by
    rw [hT, mem_shellZ, mem_shellZ, map_mul, hvw, one_mul]
  have hpt : ∀ y, T.indicator g ((w : v.adicCompletion K) * y) = (χ⁻¹ w : ℂ) * T.indicator g y := by
    intro y
    by_cases hy : y ∈ T
    · have hwy : (w : v.adicCompletion K) * y ∈ T := (hmemT y).mpr hy
      rw [Set.indicator_of_mem hwy, Set.indicator_of_mem hy]
      have hy0 : y ≠ 0 := ne_zero_of_mem_shellZ K v hy
      have hwy0 : (w : v.adicCompletion K) * y ≠ 0 := mul_ne_zero w.ne_zero hy0
      have hψy : ψ ((w : v.adicCompletion K) * y) = ψ y := by
        have e : (w : v.adicCompletion K) * y = y + ((w : v.adicCompletion K) - 1) * y := by ring
        rw [e, AddChar.map_add_eq_mul, hψn (((w : v.adicCompletion K) - 1) * y) ?_, mul_one]
        rw [map_mul, (mem_shellZ K v).mp hy]
        calc Valued.v ((w : v.adicCompletion K) - 1) * WithZero.exp (-k)
            ≤ WithZero.exp (-(j : ℤ)) * WithZero.exp (-k) := mul_le_mul' hw1 le_rfl
          _ = WithZero.exp (-(j : ℤ) + -k) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp n := WithZero.exp_le_exp.mpr (by omega)
      have hχy : charExt χ⁻¹ ((w : v.adicCompletion K) * y) = (χ⁻¹ w : ℂ) * charExt χ⁻¹ y := by
        have e : Units.mk0 ((w : v.adicCompletion K) * y) hwy0 = w * Units.mk0 y hy0 :=
          Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0])
        rw [charExt_of_ne_zero _ hwy0, charExt_of_ne_zero _ hy0, e, map_mul, Units.val_mul]
      have hmod : modulus ((w : v.adicCompletion K) * y) = modulus y := by
        rw [modulus_mul, hmodw, one_mul]
      show ψ ((w : v.adicCompletion K) * y) * C * charExt χ⁻¹ ((w : v.adicCompletion K) * y)
          * ((modulus ((w : v.adicCompletion K) * y) : ℝ) : ℂ) ^ s
        = (χ⁻¹ w : ℂ) * (ψ y * C * charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s)
      rw [hψy, hχy, hmod]
      ring
    · have hwy : (w : v.adicCompletion K) * y ∉ T := fun h => hy ((hmemT y).mp h)
      rw [Set.indicator_of_notMem hwy, Set.indicator_of_notMem hy, mul_zero]
  have hI : ∫ y in T, g y ∂μ = (χ⁻¹ w : ℂ) * ∫ y in T, g y ∂μ := by
    calc ∫ y in T, g y ∂μ = ∫ y, T.indicator g y ∂μ := (integral_indicator hTm).symm
      _ = ∫ y, T.indicator g ((w : v.adicCompletion K) * y) ∂μ := hinv.symm
      _ = ∫ y, (χ⁻¹ w : ℂ) * T.indicator g y ∂μ := by simp_rw [hpt]
      _ = (χ⁻¹ w : ℂ) * ∫ y in T, g y ∂μ := by rw [integral_const_mul, integral_indicator hTm]
  have hne : (χ⁻¹ w : ℂ) ≠ 1 := by
    intro h
    apply hχw
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_eq_one, Units.val_eq_one] at h
    exact h
  have hzero : ∫ y in T, g y ∂μ = 0 := by
    have h : (1 - (χ⁻¹ w : ℂ)) * ∫ y in T, g y ∂μ = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne.symm)
  rw [hzero, smul_zero]

private theorem localZeta_dual_mul (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] [μ.Regular]
    {ψ : AddChar (v.adicCompletion K) ℂ} (hψc : Continuous ψ) {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    {χ ω : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (hc : 1 ≤ c) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) (huω : ‖(ω (uniformizerUnit K v) : ℂ)‖ = 1)
    (C : ℂ) (s : ℂ) :
    localZeta μ (fun y => ψ y * C
        * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + c)}.indicator
            (fun _ => (1 : ℂ)) y) (χ * ω)⁻¹ s
      = (ω (uniformizerUnit K v) : ℂ) ^ ((c : ℤ) + n)
          * localZeta μ (fun y => ψ y * C
              * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + c)}.indicator
                  (fun _ => (1 : ℂ)) y) χ⁻¹ s := by
  set N : ℤ := n + c with hN
  set B : Set (v.adicCompletion K) := {y' | Valued.v y' ≤ WithZero.exp N} with hB
  set ν : Measure (v.adicCompletion K) := mulMeasure μ with hν
  set z : ℂ := (ω (uniformizerUnit K v) : ℂ) with hz
  set I : ((v.adicCompletion K)ˣ →* ℂˣ) → v.adicCompletion K → ℂ := fun θ y =>
    ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt θ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s with hI
  have hχω : HasConductorExponentAt K v (χ * ω) c := hasConductorExponentAt_mul K v hχ hω
  have h0B : ({0} : Set (v.adicCompletion K)) ⊆ B := by
    rintro _ rfl
    rw [hB, Set.mem_setOf_eq, map_zero]
    exact zero_le'
  have hBm : MeasurableSet B := by
    rw [← Set.diff_union_of_subset h0B, show B \ {0} = ⋃ j : ℕ, shellZ K v (-N + j) from
      ball_diff_zero_eq_iUnion K v N]
    exact (MeasurableSet.iUnion fun j => measurableSet_shellZ K v _).union (MeasurableSet.singleton 0)

  have hrel : ∀ (k : ℤ) (y : v.adicCompletion K), y ∈ shellZ K v k → I (χ * ω) y = z ^ (-k) * I χ y := by
    intro k y hy
    show ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt (χ * ω)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s
      = z ^ (-k) * (ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s)
    rw [inv_mul_inv, charExt_mul, charExt_of_mem_shellZ K v (hasConductorExponentAt_inv_zero K v hω) hy,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_zpow', hz]
    ring

  have hnorm : ∀ y, ‖I (χ * ω) y‖ = ‖I χ y‖ := by
    intro y
    by_cases hy : y = 0
    · show ‖ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt (χ * ω)⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s‖
        = ‖ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s‖
      rw [hy, charExt_zero, charExt_zero]
    · have hz1 : ‖z‖ = 1 := by
        rw [hz]
        exact huω
      rw [hrel _ y (mem_shellZ_neg_log K v hy), norm_mul, norm_zpow, hz1, one_zpow, one_mul]

  have hmeas : ∀ {θ : (v.adicCompletion K)ˣ →* ℂˣ}, HasConductorExponentAt K v θ c →
      AEStronglyMeasurable (I θ) ν := fun hθ =>
    aestronglyMeasurable_dual K v hA μ hψc C hBm hθ s

  have hsplit : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, Integrable (I θ) ν →
      localZeta μ (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y) θ⁻¹ s
        = ∑' j : ℕ, ∫ y in shellZ K v (-N + j), I θ y ∂ν := by
    intro θ hθ
    have hzero : ∀ y, y ∉ B \ {0} → I θ y = 0 := by
      intro y hy
      rw [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not] at hy
      show ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt θ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s = 0
      by_cases hyB : y ∈ B
      · rw [hy hyB, charExt_zero, mul_zero, zero_mul]
      · rw [Set.indicator_of_notMem hyB, mul_zero, zero_mul, zero_mul]
    calc localZeta μ (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y) θ⁻¹ s
        = ∫ y, I θ y ∂ν := rfl
      _ = ∫ y in B \ {0}, I θ y ∂ν := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ y in ⋃ j : ℕ, shellZ K v (-N + j), I θ y ∂ν := by
          rw [show B \ {0} = ⋃ j : ℕ, shellZ K v (-N + j) from ball_diff_zero_eq_iUnion K v N]
      _ = ∑' j : ℕ, ∫ y in shellZ K v (-N + j), I θ y ∂ν :=
          integral_iUnion (fun j => measurableSet_shellZ K v _) (pairwise_disjoint_shellZ K v N)
            hθ.integrableOn

  have hon : ∀ (θ : (v.adicCompletion K)ˣ →* ℂˣ) (j : ℕ),
      ∫ y in shellZ K v (-N + j), I θ y ∂ν
        = ∫ y in shellZ K v (-N + j), ψ y * C * charExt θ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s ∂ν := by
    intro θ j
    refine setIntegral_congr_fun (measurableSet_shellZ K v _) fun y hy => ?_
    have hyB : y ∈ B := by
      rw [hB, Set.mem_setOf_eq, (mem_shellZ K v).mp hy]
      exact WithZero.exp_le_exp.mpr (by omega)
    show ψ y * C * B.indicator (fun _ => (1 : ℂ)) y * charExt θ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ s = _
    rw [Set.indicator_of_mem hyB, mul_one]
  by_cases hint : Integrable (I χ) ν
  · have hint' : Integrable (I (χ * ω)) ν :=
      hint.congr' (hmeas hχω) (Filter.Eventually.of_forall fun y => (hnorm y).symm)
    rw [hsplit _ hint', hsplit _ hint]
    have hterm : ∀ j : ℕ, ∫ y in shellZ K v (-N + j), I (χ * ω) y ∂ν
        = z ^ N * ∫ y in shellZ K v (-N + j), I χ y ∂ν := by
      intro j
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [Nat.cast_zero, add_zero, setIntegral_congr_fun (measurableSet_shellZ K v _)
          (fun y hy => hrel (-N) y hy), integral_const_mul, neg_neg]
      · have hk : -(n + (c : ℤ)) < -N + j := by omega
        rw [hon, hon, setIntegral_shellZ_eq_zero K v hA μ hψn hc hχω hk C s,
          setIntegral_shellZ_eq_zero K v hA μ hψn hc hχ hk C s, mul_zero]
    rw [tsum_congr hterm, tsum_mul_left, hN, add_comm]
  · have hint' : ¬ Integrable (I (χ * ω)) ν := fun h =>
      hint (h.congr' (hmeas hχ) (Filter.Eventually.of_forall hnorm))
    rw [show localZeta μ (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y) (χ * ω)⁻¹ s
        = ∫ y, I (χ * ω) y ∂ν from rfl, integral_undef hint',
      show localZeta μ (fun y => ψ y * C * B.indicator (fun _ => (1 : ℂ)) y) χ⁻¹ s
        = ∫ y, I χ y ∂ν from rfl, integral_undef hint, mul_zero]

end Dual

private theorem stdEpsilonAt_eq_of_unram (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (hF : ∀ (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
      (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ),
      (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) →
      (∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1) →
      ∀ (a : v.adicCompletion K) (m : ℤ) (y : v.adicCompletion K),
      tateFourier ψ μ ({x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator
          fun _ => (1 : ℂ)) y
        = ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
            * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator
                (fun _ => (1 : ℂ)) y)
    (hL : ∀ ψ : AddChar (v.adicCompletion K) ℂ,
      (∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) → ψ ≠ 1 →
      (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
        ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : HasConductorExponentAt K v χ 0) {s : ℂ}
    (hs1 : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1)
    (hs2 : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 - s).re) < 1)
    (hψ : psiLocal K v ≠ 1) :
    stdEpsilonAt K v χ s
      = (((selfDualHaarAt K v).real
            (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ)
          * ((χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s))
              ^ (addCharLevel (psiLocal K v)) := by
  set ψ := psiLocal K v with hψdef
  set n : ℤ := addCharLevel ψ with hn
  set μ₀ : Measure (v.adicCompletion K) := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ₀
  set κ : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(n : ℝ) / 2) with hκ
  have hsd : selfDualHaarAt K v = κ • μ₀ := rfl
  set O : Set (v.adicCompletion K) := (v.adicCompletionIntegers K : Set (v.adicCompletion K)) with hO
  set ϖ := uniformizerUnit K v with hϖ
  set q := Ideal.absNorm v.asIdeal with hqdef
  set c : ℂ := (χ ϖ : ℂ) * (q : ℂ) ^ (-s) with hc
  set c' : ℂ := (χ⁻¹ ϖ : ℂ) * (q : ℂ) ^ (-(1 - s)) with hc'
  have hq1 : 1 < q := one_lt_absNorm K v
  have hq : 0 < q := by omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hκ0 : (κ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (NNReal.rpow_pos (Nat.cast_pos.mpr hq)).ne')

  obtain ⟨hψn, hψn1⟩ := hL ψ ⟨0, fun x hx => psiLocal_eq_one_of_valued_le_one K v x
    (by rwa [WithZero.exp_zero] at hx)⟩ hψ
  have hχ' : HasConductorExponentAt K v χ⁻¹ 0 := hasConductorExponentAt_inv_zero K v hχ

  have hf : stdTestFunAt K v χ = O.indicator fun _ => (1 : ℂ) := by
    unfold stdTestFunAt
    rw [if_pos hχ]
  have hO0 : O = {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (0 : ℤ)} := by
    ext x
    rw [hO, SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_setOf_eq, WithZero.exp_zero]
  have hOa : O = {x : v.adicCompletion K | Valued.v (x - 0) ≤ WithZero.exp (-(0 : ℤ))} := by
    rw [hO0]
    ext x
    simp only [Set.mem_setOf_eq, sub_zero, neg_zero]
  have hμO : μ₀.real O = 1 := by
    rw [measureReal_def, show O = (integersPositiveCompacts K v : Set (v.adicCompletion K)) from rfl,
      Measure.addHaarMeasure_self, ENNReal.toReal_one]
  have hsdO : (selfDualHaarAt K v).real O = κ := by
    rw [measureReal_def, hsd, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ← measureReal_def, hμO, mul_one]

  have hμ0 : ∀ k : ℤ, μ₀ (shellZ K v k)
      = ((((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-k) : ℝ≥0) : ℝ≥0∞) * μ₀ (unitSphere K v) :=
    addHaar_shellZ K v hA
  have hfin0 : μ₀ (unitSphere K v) ≠ ⊤ :=
    ((measure_mono (unitSphere_subset_integers K v)).trans_lt (by
      rw [show (v.adicCompletionIntegers K : Set (v.adicCompletion K))
          = (integersPositiveCompacts K v : Set (v.adicCompletion K)) from rfl, Measure.addHaarMeasure_self]
      exact ENNReal.one_lt_top)).ne
  have hUreal : μ₀.real (unitSphere K v) = 1 - (q : ℝ)⁻¹ := by
    have hq1' : (1 : ℝ≥0∞) ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by exact_mod_cast hq1.le
    rw [measureReal_def, addHaar_unitSphere K v hA, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hq1')
      ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hU0 : ((μ₀.real (unitSphere K v) : ℝ) : ℂ) ≠ 0 := by
    rw [hUreal]
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
    have hpos : (0 : ℝ) < 1 - (q : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hqR)
    exact_mod_cast hpos.ne'

  have hnc : ‖c‖ < 1 := by
    rw [hc, norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
    exact hs1
  have hnc' : ‖c'‖ < 1 := by
    rw [hc', norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
    exact hs2
  have hD : (1 - c) ≠ 0 := fun h => by
    rw [(sub_eq_zero.mp h).symm, norm_one] at hnc
    exact lt_irrefl _ hnc
  have hD' : (1 - c') ≠ 0 := fun h => by
    rw [(sub_eq_zero.mp h).symm, norm_one] at hnc'
    exact lt_irrefl _ hnc'

  have hFT : tateFourier ψ (selfDualHaarAt K v) (O.indicator fun _ => (1 : ℂ))
      = fun y => (κ : ℂ) * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp n}.indicator
          (fun _ => (1 : ℂ)) y := by
    rw [hsd, tateFourier_smul_measure]
    funext y
    rw [hOa, hF μ₀ ψ n hψn hψn1 0 0 y, zero_mul, AddChar.map_zero_eq_one, one_mul, neg_zero, ← hO0, hμO,
      Complex.ofReal_one, one_mul, add_zero]

  have hdual : localZeta (selfDualHaarAt K v) (tateFourier ψ (selfDualHaarAt K v) (O.indicator fun _ => (1 : ℂ)))
      χ⁻¹ (1 - s)
      = (κ : ℂ) * ((κ : ℂ) * (((μ₀.real (unitSphere K v) : ℝ) : ℂ) * c' ^ (-n) * (1 - c')⁻¹)) := by
    rw [hFT, localZeta_const_mul, hsd, localZeta_smul_measure,
      localZeta_indicator_ball_eq K v hA hμ0 hfin0 hχ' hs2 n]
  have htest : localZeta (selfDualHaarAt K v) (O.indicator fun _ => (1 : ℂ)) χ s
      = (κ : ℂ) * (((μ₀.real (unitSphere K v) : ℝ) : ℂ) * c ^ (-(0 : ℤ)) * (1 - c)⁻¹) := by
    rw [hsd, localZeta_smul_measure, hO0, localZeta_indicator_ball_eq K v hA hμ0 hfin0 hχ hs1 0]
  have hc'n : c' ^ (-n) = ((χ ϖ : ℂ) * (q : ℂ) ^ (1 - s)) ^ n := by
    rw [hc', MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Complex.cpow_neg, ← mul_inv, inv_zpow', neg_neg]

  show localEpsilonAt K v (selfDualHaarAt K v) ψ (stdTestFunAt K v χ) χ s = _
  rw [localEpsilonAt_def, localGammaAt, hf, hdual, htest, localLFactorAt_of_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ', hsdO, ← hc, ← hc', hc'n, neg_zero, zpow_zero,
    mul_one]
  field_simp

private theorem stdRootNumberAt_mul (hA : ∀ x : v.adicCompletion K, modulus x = ‖x‖₊)
    (hF : ∀ (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
      (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ),
      (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) →
      (∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1) →
      ∀ (a : v.adicCompletion K) (m : ℤ) (y : v.adicCompletion K),
      tateFourier ψ μ ({x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator
          fun _ => (1 : ℂ)) y
        = ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
            * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator
                (fun _ => (1 : ℂ)) y)
    (hL : ∀ ψ : AddChar (v.adicCompletion K) ℂ,
      (∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) → ψ ≠ 1 →
      (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
        ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1)
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    (huω : ‖(ω (uniformizerUnit K v) : ℂ)‖ = 1) (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v (χ * ω)
      = (ω (uniformizerUnit K v) : ℂ) ^ ((c : ℤ) + addCharLevel (psiLocal K v))
          * stdRootNumberAt K v χ := by
  set ψ := psiLocal K v with hψdef
  set n : ℤ := addCharLevel ψ with hn
  set ϖ := uniformizerUnit K v with hϖ
  set q := Ideal.absNorm v.asIdeal with hqdef
  have hq1 : 1 < q := one_lt_absNorm K v

  obtain ⟨hψn, hψn1⟩ := hL ψ ⟨0, fun x hx => psiLocal_eq_one_of_valued_le_one K v x
    (by rwa [WithZero.exp_zero] at hx)⟩ hψ
  have hχω : HasConductorExponentAt K v (χ * ω) c := hasConductorExponentAt_mul K v hχ hω
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  ·
    subst hc0
    have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hre1 : (-(1 / 2 : ℂ).re) = -(1 / 2 : ℝ) := by norm_num
    have hre2 : (-(1 - 1 / 2 : ℂ).re) = -(1 / 2 : ℝ) := by norm_num
    have hhalf : (q : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hqR (by norm_num)
    have conv1 : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, ‖(θ ϖ : ℂ)‖ = 1 →
        ‖(θ ϖ : ℂ)‖ * (q : ℝ) ^ (-(1 / 2 : ℂ).re) < 1 := fun θ h => by
      rw [h, one_mul, hre1]
      exact hhalf
    have conv2 : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, ‖(θ ϖ : ℂ)‖ = 1 →
        ‖(θ⁻¹ ϖ : ℂ)‖ * (q : ℝ) ^ (-(1 - 1 / 2 : ℂ).re) < 1 := fun θ h => by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h, inv_one, one_mul, hre2]
      exact hhalf
    have huχω : ‖((χ * ω) ϖ : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hu, huω, mul_one]
    rw [stdRootNumberAt_def, stdRootNumberAt_def,
      stdEpsilonAt_eq_of_unram K v hA hF hL hχω (conv1 _ huχω) (conv2 _ huχω) hψ,
      stdEpsilonAt_eq_of_unram K v hA hF hL hχ (conv1 _ hu) (conv2 _ hu) hψ, MonoidHom.mul_apply,
      Units.val_mul, Nat.cast_zero, zero_add, mul_right_comm (χ ϖ : ℂ) (ω ϖ : ℂ), mul_zpow]
    ring
  ·
    have hc1 : 1 ≤ c := hcpos
    set μ₀ : Measure (v.adicCompletion K) := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ₀
    set κ : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(n : ℝ) / 2) with hκ
    have hsd : selfDualHaarAt K v = κ • μ₀ := rfl
    have hnot : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, HasConductorExponentAt K v θ c →
        ¬ HasConductorExponentAt K v θ 0 := fun θ h h0 => by
      have := hasConductorExponentAt_unique K v h h0
      omega
    set Bc : Set (v.adicCompletion K) := {x | Valued.v (x - 1) ≤ WithZero.exp (-(c : ℤ))} with hBc
    have hfχ : stdTestFunAt K v χ = Bc.indicator fun _ => (1 : ℂ) := stdTestFunAt_eq_of_pos K v hc1 hχ
    have hfχω : stdTestFunAt K v (χ * ω) = Bc.indicator fun _ => (1 : ℂ) := by
      rw [stdTestFunAt_mul K v hω, hfχ]

    have hFT : tateFourier ψ (selfDualHaarAt K v) (Bc.indicator fun _ => (1 : ℂ))
        = fun y => (κ : ℂ) * (ψ y
            * ((μ₀.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(c : ℤ))} : ℝ) : ℂ)
            * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + c)}.indicator
                (fun _ => (1 : ℂ)) y) := by
      rw [hsd, tateFourier_smul_measure]
      funext y
      rw [hBc, hF μ₀ ψ n hψn hψn1 1 c y, one_mul]

    have hγ : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, HasConductorExponentAt K v θ c →
        stdRootNumberAt K v θ
          = localZeta (selfDualHaarAt K v) (tateFourier ψ (selfDualHaarAt K v) (stdTestFunAt K v θ))
              θ⁻¹ (1 - 1 / 2)
            / localZeta (selfDualHaarAt K v) (stdTestFunAt K v θ) θ (1 / 2) := fun θ h => by
      rw [stdRootNumberAt_def]
      show localEpsilonAt K v (selfDualHaarAt K v) ψ (stdTestFunAt K v θ) θ (1 / 2) = _
      rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _ (hnot θ h)]
      rfl
    have htest : localZeta μ₀ (Bc.indicator fun _ => (1 : ℂ)) (χ * ω) (1 / 2)
        = localZeta μ₀ (Bc.indicator fun _ => (1 : ℂ)) χ (1 / 2) := by
      rw [hBc, ← image_higherUnitsAt_eq K v hc1, localZeta_testFun_mul K v hω c μ₀ (1 / 2)]
    rw [hγ _ hχω, hγ _ hχ, hfχω, hfχ, hFT, localZeta_const_mul, localZeta_const_mul, hsd,
      localZeta_smul_measure, localZeta_smul_measure, localZeta_smul_measure, localZeta_smul_measure,
      localZeta_dual_mul K v hA μ₀ (continuous_psiLocal K v) hψn hc1 hχ hω huω _ (1 - 1 / 2), htest]
    ring

end LanglandsTunnell.TateLocal.UnramTwist

end

p2m_open "NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero.LanglandsTunnell.TateLocal"

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    (huω : ‖(ω (uniformizerUnit K v) : ℂ)‖ = 1) (hψ : psiLocal K v ≠ 1) :
    stdRootNumberAt K v (χ * ω)
      = (ω (uniformizerUnit K v) : ℂ) ^ ((c : ℤ) + addCharLevel (psiLocal K v))
          * stdRootNumberAt K v χ := by
  letI : MeasurableSpace (v.adicCompletion K) := LanglandsTunnell.TateLocal.localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  exact LanglandsTunnell.TateLocal.UnramTwist.stdRootNumberAt_mul K v
    (LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v)
    (fun μ _ ψ n hψn hψn' a m y =>
      LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' a m y)
    (fun ψ hψk hψ1 =>
      LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v ψ hψk hψ1)
    χ ω c hχ hω hu huω hψ

end S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero (solution)
