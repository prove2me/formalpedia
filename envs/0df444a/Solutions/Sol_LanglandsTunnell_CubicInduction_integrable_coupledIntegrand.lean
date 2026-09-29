-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_coupledIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a3eafe06-7651-5f66-89de-26bd8d31195f

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar
open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_zero modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_one modulus_mul charExt charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section GaussProductViaRootNumbers

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem norm_inv_apply_uniformizerUnit {η : (w.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(η (uniformizerUnit K w) : ℂ)‖ = 1) : ‖(η⁻¹ (uniformizerUnit K w) : ℂ)‖ = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

end GaussProductViaRootNumbers

end LanglandsTunnell.TateLocal
end

section
set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace LaurentLocalZeta

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem continuousOn_charExt_compl (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmk : Continuous fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) => Units.mk0 (x : v.adicCompletion ℚ) x.2 :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hlc : IsLocallyConstant fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) =>
      ((χ (Units.mk0 (x : v.adicCompletion ℚ) x.2) : ℂˣ) : ℂ) :=
    IsLocallyConstant.comp (IsLocallyConstant.comp_continuous hχ hmk) fun u : ℂˣ => (u : ℂ)
  refine (IsLocallyConstant.continuous hlc).congr fun x => ?_
  simp only [Set.restrict_apply, charExt_of_ne_zero χ x.2]

private theorem measurable_modulus : Measurable fun x : v.adicCompletion ℚ => (modulus x : ℝ) := by
  have h : (fun x : v.adicCompletion ℚ => (modulus x : ℝ)) = fun x => ‖x‖ := by
    funext x
    rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]
  rw [h]
  exact measurable_norm

private theorem measurable_modulus_cpow (s : ℂ) :
    Measurable fun x : v.adicCompletion ℚ => ((modulus x : ℝ) : ℂ) ^ s :=
  (Complex.measurable_ofReal.comp (measurable_modulus v)).pow_const s

private theorem measurable_charExt (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Measurable (charExt χ) :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) (continuousOn_charExt_compl v χ hχ)

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_shell (j : ℤ) : MeasurableSet (shell v j) :=
  (isClopen_shell v j).isOpen.measurableSet

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem shell_subset_compl_zero (j : ℤ) : shell v j ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  intro h0
  rw [Set.mem_singleton_iff.mp h0, map_zero] at hx'
  exact WithZero.exp_ne_zero hx'.symm

private theorem valued_uniformizerUnit_zpow (j : ℤ) :
    Valued.v ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-j) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem image_unitShell_eq_shell (j : ℤ) :
    (fun x : v.adicCompletion ℚ => ((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ''
      unitShell v = shell v j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : Valued.v x = 1 := hx
    show Valued.v _ = WithZero.exp (-j)
    rw [map_mul, valued_uniformizerUnit_zpow, hx', mul_one]
  · intro hy
    have hy' : Valued.v y = WithZero.exp (-j) := hy
    refine ⟨((uniformizerUnit ℚ v ^ j : (v.adicCompletion ℚ)ˣ)⁻¹ : (v.adicCompletion ℚ)ˣ) * y, ?_, ?_⟩
    · show Valued.v _ = 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit_zpow, hy']
      exact inv_mul_cancel₀ WithZero.exp_ne_zero
    · exact Units.mul_inv_cancel_left _ _

private theorem
    mulMeasure_unitShell : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem isLocallyConstant_inv (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    IsLocallyConstant (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) := by
  have h : (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) = fun x => (χ x)⁻¹ := by
    funext x
    simp
  rw [h]
  exact IsLocallyConstant.comp hχ fun y : ℂˣ => y⁻¹

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

private theorem coe_modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [modulus_eq_of_mem_shell v hx, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem exists_bound_charExt_unitShell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Mχ : ℝ, ∀ u ∈ unitShell v, ‖charExt χ u‖ ≤ Mχ :=
  (isCompact_unitShell v).exists_bound_of_continuousOn ((continuousOn_charExt_compl v χ hχ).mono
    (by rw [unitShell_eq_shell_zero]; exact shell_subset_compl_zero v 0))

end LaurentLocalZeta
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_support_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ R := by
  have hK : IsCompact (tsupport Φ) := hΦc
  choose C hC using fun i : Fin 3 =>
    hK.exists_bound_of_continuousOn
      ((continuous_apply i).continuousOn : ContinuousOn (fun p : Fin 3 → v.adicCompletion ℚ => p i) (tsupport Φ))
  refine ⟨∑ i, max (C i) 0, fun p hp i => ?_⟩
  have hpK : p ∈ tsupport Φ := subset_tsupport Φ hp
  calc ‖p i‖ ≤ C i := hC i p hpK
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
        Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)

private theorem norm_le_zpow_of_valued_le {x : v.adicCompletion ℚ} {n : ℤ} (hx : Valued.v x ≤ WithZero.exp n) :
    ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) :=
    (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))).monotone hx
  have h2 : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (hkey.trans_eq hexp)
  rw [NumberField.FinitePlace.norm_def v x]
  exact_mod_cast h2

private theorem
    valued_le_of_norm_le_zpow {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v x ≤ WithZero.exp n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hx' : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) := by
    rw [NumberField.FinitePlace.norm_def v x] at hx
    exact_mod_cast hx
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) := by
    rw [hexp]
    exact NNReal.coe_le_coe.mp hx'
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))
  exact hmono.le_iff_le.mp hkey

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

end TorusValues

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus modulus_zero modulus_of_ne_zero modulus_pos modulus_ne_zero modulus_one modulus_mul charExt charExt_of_ne_zero charExt_coe_units mulMeasure modulus_adicCompletion_eq_nnnorm"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

private theorem modulus_coe_units_eq (u : (v.adicCompletion K)ˣ) :
    modulus (u : v.adicCompletion K) = distribHaarChar (v.adicCompletion K) u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

private theorem charExt_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : v.adicCompletion K) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [charExt_of_ne_zero χ (mul_ne_zero ha hb), charExt_of_ne_zero χ ha, charExt_of_ne_zero χ hb,
    ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext (by simp)

private theorem selfDualHaarAt_smul_set (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    letI := localBorel K v
    selfDualHaarAt K v (u • S) = (modulus (u : v.adicCompletion K) : ℝ≥0∞) * selfDualHaarAt K v S := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [modulus_coe_units_eq]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply]
  rw [← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v)) u S]
  exact (mul_smul_comm _ _ _).symm

private theorem map_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ • selfDualHaarAt K v := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' S = u⁻¹ • S :=
    Set.preimage_smul u S
  rw [hpre, selfDualHaarAt_smul_set, modulus_coe_units_eq, modulus_coe_units_eq, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := v.adicCompletion K) (g := u)).ne']

private theorem lintegral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (g : v.adicCompletion K → ℝ≥0∞) :
    letI := localBorel K v
    ∫⁻ x, g ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ * ∫⁻ x, g x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).lintegral_map g, map_mul_left_selfDualHaarAt]
  simp only [lintegral_smul_measure, smul_eq_mul]

private theorem map_mul_left_mulMeasure (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (mulMeasure (selfDualHaarAt K v)) =
      mulMeasure (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS]
  unfold mulMeasure
  rw [withDensity_apply _ (hmul hS), withDensity_apply _ hS, Measure.restrict_restrict (hmul hS),
    Measure.restrict_restrict hS, ← lintegral_indicator (hmul hS |>.inter hc), ← lintegral_indicator (hS.inter hc)]
  have hpt : ∀ x : v.adicCompletion K,
      ((fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) x =
        (modulus (u : v.adicCompletion K) : ℝ≥0∞) *
          (S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((u : v.adicCompletion K) * x) := by
    intro x
    by_cases hx : (u : v.adicCompletion K) * x ∈ S ∩ {0}ᶜ
    · have hx' : x ∈ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        refine ⟨hx.1, ?_⟩
        intro h0
        exact hx.2 (by simp [Set.mem_singleton_iff.mp h0])
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero))) (Or.inl ENNReal.coe_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
        one_mul]
    · have hx' : x ∉ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        intro h
        refine hx ⟨h.1, ?_⟩
        intro h0
        exact h.2 (by simp [mul_eq_zero, u.ne_zero] at h0; simp [h0])
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_mul_left_selfDualHaarAt,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
    one_mul]

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def truncChar (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v t : ℂ) else 0

private theorem coupledKernel_lintegral_comp_sub_mul {u : v.adicCompletion ℚ} (hu : u ≠ 0)
    (y : v.adicCompletion ℚ) (g : v.adicCompletion ℚ → ENNReal) :
    ∫⁻ w, g (y - u * w) ∂(selfDualHaarAt ℚ v) = (modulus u : ENNReal)⁻¹ * ∫⁻ x, g x ∂(selfDualHaarAt ℚ v) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hnu : -u ≠ 0 := neg_ne_zero.mpr hu
  have h1 : (fun w => g (y - u * w)) =
      fun w => (fun x => g (y + x)) (((Units.mk0 (-u) hnu : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * w) := by
    funext w
    simp only [Units.val_mk0]
    congr 1
    ring
  have hneg : modulus (-u) = modulus u := by
    apply NNReal.coe_injective
    rw [modulus_real_eq_norm, modulus_real_eq_norm, norm_neg]
  rw [h1, lintegral_mul_left_selfDualHaarAt ℚ v (Units.mk0 (-u) hnu) (fun x => g (y + x)), Units.val_mk0, hneg,
    lintegral_add_left_eq_self]

private noncomputable def coupledKernel_scale (n : ℤ) : v.adicCompletion ℚ :=
  ((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-n) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)

private theorem coupledKernel_scale_ne_zero (n : ℤ) : coupledKernel_scale v n ≠ 0 :=
  Units.ne_zero _

private theorem coupledKernel_valued_scale (n : ℤ) : Valued.v (coupledKernel_scale v n) = WithZero.exp n := by
  unfold coupledKernel_scale
  rw [LaurentLocalZeta.valued_uniformizerUnit_zpow, neg_neg]

private def coupledKernel_ball (t : v.adicCompletion ℚ) : Set (v.adicCompletion ℚ) :=
  {x : v.adicCompletion ℚ | Valued.v x ≤ Valued.v t}

private theorem coupledKernel_modulus_le_of_valued_le {x y : v.adicCompletion ℚ} (hy : y ≠ 0)
    (h : Valued.v x ≤ Valued.v y) : modulus x ≤ modulus y := by
  have hxy : x = y * (x / y) := by field_simp
  have hq : Valued.v (x / y) ≤ WithZero.exp 0 := by
    rw [map_div₀, WithZero.exp_zero]
    exact div_le_one_of_le₀ h (zero_le')
  have hnorm : ‖x / y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (0 : ℤ) := norm_le_zpow_of_valued_le v hq
  rw [zpow_zero] at hnorm
  have hmod : modulus (x / y) ≤ 1 := by
    have h1 : (modulus (x / y) : ℝ) ≤ 1 := by rw [modulus_real_eq_norm]; exact hnorm
    exact_mod_cast h1
  calc modulus x = modulus y * modulus (x / y) := by rw [← modulus_mul, ← hxy]
    _ ≤ modulus y * 1 := mul_le_mul_right hmod _
    _ = modulus y := mul_one _

private theorem coupledKernel_modulus_eq_of_valued_eq {x y : v.adicCompletion ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Valued.v x = Valued.v y) : modulus x = modulus y :=
  le_antisymm (coupledKernel_modulus_le_of_valued_le v hy h.le) (coupledKernel_modulus_le_of_valued_le v hx h.ge)

private theorem coupledKernel_measurableSet_ball {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    MeasurableSet (coupledKernel_ball v t) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hvt : Valued.v t = WithZero.exp (WithZero.log (Valued.v t)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr ht)).symm
  have hset : coupledKernel_ball v t =
      {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (WithZero.log (Valued.v t))} := by
    ext x; simp only [coupledKernel_ball, Set.mem_setOf_eq]; rw [← hvt]
  rw [hset]
  exact (isClosed_valued_le v _).measurableSet

private theorem coupledKernel_ball_eq_image {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    coupledKernel_ball v t = (fun x => t * x) '' coupledKernel_ball v 1 := by
  ext x
  simp only [coupledKernel_ball, Set.mem_setOf_eq, Set.mem_image, map_one]
  constructor
  · intro hx
    refine ⟨x / t, ?_, by field_simp⟩
    rw [map_div₀]
    exact div_le_one_of_le₀ hx (zero_le')
  · rintro ⟨z, hz, rfl⟩
    rw [map_mul]
    calc Valued.v t * Valued.v z ≤ Valued.v t * 1 := mul_le_mul_right hz _
      _ = Valued.v t := mul_one _

private theorem coupledKernel_measure_ball {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    selfDualHaarAt ℚ v (coupledKernel_ball v t) =
      (modulus t : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1) := by
  open scoped Pointwise in
  have himg : coupledKernel_ball v t = Units.mk0 t ht • coupledKernel_ball v 1 := by
    rw [coupledKernel_ball_eq_image v ht, ← Set.image_smul]
    rfl
  rw [himg]
  exact selfDualHaarAt_smul_set ℚ v (Units.mk0 t ht) (coupledKernel_ball v 1)

private theorem coupledKernel_measure_ball_one_ne_top : selfDualHaarAt ℚ v (coupledKernel_ball v 1) ≠ ⊤ := by
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  have hsub : coupledKernel_ball v 1 ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    intro x hx
    rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa [coupledKernel_ball] using hx
  exact ne_top_of_le_ne_top hO.measure_lt_top.ne (measure_mono hsub)

private theorem coupledKernel_ballAround_eq (y t : v.adicCompletion ℚ) :
    {x : v.adicCompletion ℚ | Valued.v (y - x) ≤ Valued.v t} =
      (fun x : v.adicCompletion ℚ => -y + x) ⁻¹' coupledKernel_ball v t := by
  ext x
  simp only [coupledKernel_ball, Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub]
  rw [Valuation.map_sub_swap]

private theorem coupledKernel_measurableSet_ballAround (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    MeasurableSet {x : v.adicCompletion ℚ | Valued.v (y - x) ≤ Valued.v t} := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  rw [coupledKernel_ballAround_eq]
  exact (measurable_const.add measurable_id) (coupledKernel_measurableSet_ball v ht)

private theorem coupledKernel_measure_ballAround (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    selfDualHaarAt ℚ v {x : v.adicCompletion ℚ | Valued.v (y - x) ≤ Valued.v t} =
      (modulus t : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  rw [coupledKernel_ballAround_eq, measure_preimage_add, coupledKernel_measure_ball v ht]

private noncomputable def coupledKernel_fibreWeight (N c : ℤ) (a y w : v.adicCompletion ℚ) : ENNReal :=
  {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) w *
    ((modulus (y - a * w) : ENNReal))⁻¹ *
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v (y - a * t)}.indicator (fun _ => (1 : ENNReal)) w

private noncomputable def coupledKernel_majorant (N c : ℤ) (B σ : ℝ) (a y w : v.adicCompletion ℚ) : ENNReal :=
  ENNReal.ofReal B *
    ({t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) a *
      ENNReal.ofReal ((modulus a : ℝ) ^ (1 - σ))) *
    ({t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) y *
      ENNReal.ofReal ((modulus y : ℝ) ^ σ)) *
    coupledKernel_fibreWeight v N c a y w

private noncomputable def coupledKernel_fibreWeightAt (N c : ℤ) (a y x : v.adicCompletion ℚ) : ENNReal :=
  {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) ((y - x) / a) *
    ((modulus x : ENNReal))⁻¹ *
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v x}.indicator (fun _ => (1 : ENNReal))
      ((y - x) / a)

private theorem coupledKernel_fibreWeight_eq_fibreWeightAt (N c : ℤ) {a : v.adicCompletion ℚ} (ha : a ≠ 0)
    (y w : v.adicCompletion ℚ) :
    coupledKernel_fibreWeight v N c a y w = coupledKernel_fibreWeightAt v N c a y (y - a * w) := by
  have hw : (y - (y - a * w)) / a = w := by field_simp; ring
  simp only [coupledKernel_fibreWeight, coupledKernel_fibreWeightAt, Set.indicator, Set.mem_setOf_eq, hw]

private theorem coupledKernel_lintegral_fibreWeight_eq (N c : ℤ) {a : v.adicCompletion ℚ} (ha : a ≠ 0)
    (y : v.adicCompletion ℚ) :
    (∫⁻ w, coupledKernel_fibreWeight v N c a y w ∂(selfDualHaarAt ℚ v)) =
      (modulus a : ENNReal)⁻¹ * ∫⁻ x, coupledKernel_fibreWeightAt v N c a y x ∂(selfDualHaarAt ℚ v) := by
  rw [← coupledKernel_lintegral_comp_sub_mul v ha y (coupledKernel_fibreWeightAt v N c a y)]
  exact lintegral_congr fun w => coupledKernel_fibreWeight_eq_fibreWeightAt v N c ha y w

private noncomputable def coupledKernel_shellIndices (N c j α : ℤ) : Finset ℤ :=
  if 0 ≤ c + α then Finset.Ioc j (2 * N) ∪ Finset.Ico (j - c - α) j else ∅

private theorem coupledKernel_shellIndices_count_le (N c j α : ℤ) (hα : α ≤ N) :
    (coupledKernel_shellIndices N c j α).card ≤ (2 * N - j).toNat + (c + N).toNat := by
  unfold coupledKernel_shellIndices
  split_ifs with h
  · refine (Finset.card_union_le _ _).trans ?_
    rw [Int.card_Ioc, Int.card_Ico]
    omega
  · simp

private theorem coupledKernel_shellIndices_of_nonneg {N c j α : ℤ} (h : 0 ≤ c + α) :
    coupledKernel_shellIndices N c j α = Finset.Ioc j (2 * N) ∪ Finset.Ico (j - c - α) j := by
  simp only [coupledKernel_shellIndices, if_pos h]

private noncomputable def coupledKernel_ballTerm (c : ℤ) (a y x : v.adicCompletion ℚ) : ENNReal :=
  (modulus y : ENNReal)⁻¹ *
    {z : v.adicCompletion ℚ | Valued.v (y - z) ≤ Valued.v (coupledKernel_scale v c * a * y)}.indicator
      (fun _ => (1 : ENNReal)) x

private noncomputable def coupledKernel_shellTerm (i : ℤ) (x : v.adicCompletion ℚ) : ENNReal :=
  (modulus (coupledKernel_scale v i) : ENNReal)⁻¹ *
    (coupledKernel_ball v (coupledKernel_scale v i)).indicator (fun _ => (1 : ENNReal)) x

private theorem coupledKernel_indicator_one_le (s : Set (v.adicCompletion ℚ)) (z : v.adicCompletion ℚ) :
    s.indicator (fun _ => (1 : ENNReal)) z ≤ 1 := by
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]; exact zero_le

private theorem coupledKernel_fibreWeightAt_le_inv (N c : ℤ) (a y x : v.adicCompletion ℚ) :
    coupledKernel_fibreWeightAt v N c a y x ≤ ((modulus x : ENNReal))⁻¹ := by
  unfold coupledKernel_fibreWeightAt
  calc _ ≤ 1 * ((modulus x : ENNReal))⁻¹ * 1 :=
        mul_le_mul' (mul_le_mul' (coupledKernel_indicator_one_le v _ _) le_rfl) (coupledKernel_indicator_one_le v _ _)
    _ = ((modulus x : ENNReal))⁻¹ := by rw [one_mul, mul_one]

private theorem coupledKernel_fibreWeightAt_le (N c j : ℤ) {a y : v.adicCompletion ℚ} (ha : a ≠ 0)
    (hy : Valued.v y = WithZero.exp j) (haN : Valued.v a ≤ WithZero.exp N) (x : v.adicCompletion ℚ) :
    coupledKernel_fibreWeightAt v N c a y x ≤
      coupledKernel_ballTerm v c a y x +
        (∑ i ∈ coupledKernel_shellIndices N c j (WithZero.log (Valued.v a)), coupledKernel_shellTerm v i x) := by
  by_cases hG : coupledKernel_fibreWeightAt v N c a y x = 0
  · rw [hG]; exact zero_le
  have hfac := hG
  simp only [coupledKernel_fibreWeightAt, mul_eq_zero, not_or] at hfac
  obtain ⟨⟨h1, -⟩, h3⟩ := hfac
  have h1' : Valued.v ((y - x) / a) ≤ WithZero.exp N := by
    by_contra hm
    have hm' : (y - x) / a ∉ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N} := hm
    exact h1 (Set.indicator_of_notMem hm' _)
  have h3' : Valued.v ((y - x) / a) ≤ WithZero.exp c * Valued.v x := by
    by_contra hm
    have hm' : (y - x) / a ∉ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v x} := hm
    exact h3 (Set.indicator_of_notMem hm' _)
  have hva0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hyx1 : Valued.v (y - x) ≤ WithZero.exp N * Valued.v a := by
    have h := mul_le_mul_left h1' (Valued.v a)
    rwa [map_div₀, div_mul_cancel₀ _ hva0] at h
  have hyx3 : Valued.v (y - x) ≤ WithZero.exp c * Valued.v x * Valued.v a := by
    have h := mul_le_mul_left h3' (Valued.v a)
    rwa [map_div₀, div_mul_cancel₀ _ hva0] at h
  have hy0 : y ≠ 0 := fun h => WithZero.exp_ne_zero (hy.symm.trans (by rw [h, map_zero]))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, zero_mul, sub_zero, hy] at hyx3
    exact WithZero.exp_ne_zero (le_zero_iff.mp hyx3)
  have hva : Valued.v a = WithZero.exp (WithZero.log (Valued.v a)) := (WithZero.exp_log hva0).symm
  have hvx : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx0)).symm
  set α := WithZero.log (Valued.v a) with hαdef
  set i := WithZero.log (Valued.v x) with hidef
  have hαN : α ≤ N := WithZero.exp_le_exp.mp (by rw [← hva]; exact haN)
  have hle := coupledKernel_fibreWeightAt_le_inv v N c a y x
  rcases eq_or_ne i j with hij | hij
  ·
    have hxy : Valued.v x = Valued.v y := by rw [hvx, hij, hy]
    have hmem : x ∈ {z : v.adicCompletion ℚ | Valued.v (y - z) ≤ Valued.v (coupledKernel_scale v c * a * y)} := by
      show Valued.v (y - x) ≤ Valued.v (coupledKernel_scale v c * a * y)
      rw [map_mul, map_mul, coupledKernel_valued_scale, ← hxy]
      calc Valued.v (y - x) ≤ WithZero.exp c * Valued.v x * Valued.v a := hyx3
        _ = WithZero.exp c * Valued.v a * Valued.v x := mul_right_comm _ _ _
    rw [coupledKernel_modulus_eq_of_valued_eq v hx0 hy0 hxy] at hle
    have hB : coupledKernel_ballTerm v c a y x = (modulus y : ENNReal)⁻¹ := by
      simp only [coupledKernel_ballTerm, Set.indicator_of_mem hmem, mul_one]
    rw [hB]
    exact le_self_add.trans' hle
  ·
    have hi_mem : i ∈ coupledKernel_shellIndices N c j α := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      ·
        have hsub : Valued.v (y - x) = Valued.v y :=
          Valuation.map_sub_eq_of_lt_left _ (by rw [hvx, hy]; exact WithZero.exp_lt_exp.mpr hlt)
        rw [hsub, hy, hvx, hva, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_le_exp] at hyx3
        rw [coupledKernel_shellIndices_of_nonneg (by omega)]
        exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)
      ·
        have hsub : Valued.v (y - x) = Valued.v x :=
          Valuation.map_sub_eq_of_lt_right _ (by rw [hvx, hy]; exact WithZero.exp_lt_exp.mpr hgt)
        rw [hsub, hvx, hva, ← WithZero.exp_add, WithZero.exp_le_exp] at hyx1
        rw [hsub, hvx, hva, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_le_exp] at hyx3
        rw [coupledKernel_shellIndices_of_nonneg (by omega)]
        exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨hgt, by omega⟩)
    have hxi : Valued.v x = Valued.v (coupledKernel_scale v i) := by rw [coupledKernel_valued_scale, hvx]
    have hball : x ∈ coupledKernel_ball v (coupledKernel_scale v i) := hxi.le
    have hterm : coupledKernel_fibreWeightAt v N c a y x ≤ coupledKernel_shellTerm v i x := by
      simp only [coupledKernel_shellTerm, Set.indicator_of_mem hball, mul_one]
      rw [← coupledKernel_modulus_eq_of_valued_eq v hx0 (coupledKernel_scale_ne_zero v i) hxi]
      exact hle
    refine hterm.trans (le_add_self.trans' ?_)
    exact Finset.single_le_sum (fun j _ => (zero_le : (0 : ENNReal) ≤ coupledKernel_shellTerm v j x)) hi_mem

private theorem coupledKernel_scale_neg_mul (n : ℤ) : coupledKernel_scale v (-n) * coupledKernel_scale v n = 1 := by
  simp only [coupledKernel_scale, neg_neg, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

private noncomputable def coupledKernel_ballMeasure (c : ℤ) : ENNReal :=
  (modulus (coupledKernel_scale v c) : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1)

private theorem coupledKernel_ballMeasure_ne_top (c : ℤ) : coupledKernel_ballMeasure v c ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top (coupledKernel_measure_ball_one_ne_top v)

private theorem coupledKernel_one_le_of_nonneg {c : ℤ} {a : v.adicCompletion ℚ} (ha : a ≠ 0)
    (h : 0 ≤ c + WithZero.log (Valued.v a)) :
    (1 : ENNReal) ≤ (modulus a : ENNReal) * (modulus (coupledKernel_scale v c) : ENNReal) := by
  have hva0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hval : Valued.v (coupledKernel_scale v (-c)) ≤ Valued.v a := by
    rw [coupledKernel_valued_scale, ← WithZero.exp_log hva0]
    exact WithZero.exp_le_exp.mpr (by omega)
  have h1 := mul_le_mul_left (coupledKernel_modulus_le_of_valued_le v ha hval) (modulus (coupledKernel_scale v c))
  rw [← modulus_mul, coupledKernel_scale_neg_mul, modulus_one] at h1
  exact_mod_cast h1

private theorem coupledKernel_unitBall_le_of_nonneg {c : ℤ} {a : v.adicCompletion ℚ} (ha : a ≠ 0)
    (h : 0 ≤ c + WithZero.log (Valued.v a)) :
    selfDualHaarAt ℚ v (coupledKernel_ball v 1) ≤ (modulus a : ENNReal) * coupledKernel_ballMeasure v c := by
  unfold coupledKernel_ballMeasure
  rw [← mul_assoc]
  calc selfDualHaarAt ℚ v (coupledKernel_ball v 1)
      = 1 * selfDualHaarAt ℚ v (coupledKernel_ball v 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left (coupledKernel_one_le_of_nonneg v ha h) _

private theorem coupledKernel_measurable_ballTerm (c : ℤ) {a y : v.adicCompletion ℚ} (ha : a ≠ 0) (hy : y ≠ 0) :
    Measurable (coupledKernel_ballTerm v c a y) :=
  (measurable_const.indicator (coupledKernel_measurableSet_ballAround v y
    (mul_ne_zero (mul_ne_zero (coupledKernel_scale_ne_zero v c) ha) hy))).const_mul _

private theorem coupledKernel_measurable_shellTerm (i : ℤ) : Measurable (coupledKernel_shellTerm v i) :=
  (measurable_const.indicator (coupledKernel_measurableSet_ball v (coupledKernel_scale_ne_zero v i))).const_mul _

private theorem coupledKernel_lintegral_ballTerm (c : ℤ) {a y : v.adicCompletion ℚ} (ha : a ≠ 0) (hy : y ≠ 0) :
    (∫⁻ x, coupledKernel_ballTerm v c a y x ∂(selfDualHaarAt ℚ v)) =
      (modulus a : ENNReal) * coupledKernel_ballMeasure v c := by
  have hR0 : coupledKernel_scale v c * a * y ≠ 0 :=
    mul_ne_zero (mul_ne_zero (coupledKernel_scale_ne_zero v c) ha) hy
  have hmy : (modulus y : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero hy)
  unfold coupledKernel_ballTerm coupledKernel_ballMeasure
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hmy),
    lintegral_indicator_const (coupledKernel_measurableSet_ballAround v y hR0), one_mul,
    coupledKernel_measure_ballAround v y hR0, modulus_mul, modulus_mul, ENNReal.coe_mul, ENNReal.coe_mul]
  calc _ = ((modulus y : ENNReal)⁻¹ * (modulus y : ENNReal)) *
        ((modulus a : ENNReal) *
          ((modulus (coupledKernel_scale v c) : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1))) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hmy ENNReal.coe_ne_top, one_mul]

private theorem coupledKernel_lintegral_shellTerm (i : ℤ) :
    (∫⁻ x, coupledKernel_shellTerm v i x ∂(selfDualHaarAt ℚ v)) = selfDualHaarAt ℚ v (coupledKernel_ball v 1) := by
  have hms : (modulus (coupledKernel_scale v i) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (modulus_ne_zero (coupledKernel_scale_ne_zero v i))
  unfold coupledKernel_shellTerm
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hms),
    lintegral_indicator_const (coupledKernel_measurableSet_ball v (coupledKernel_scale_ne_zero v i)), one_mul,
    coupledKernel_measure_ball v (coupledKernel_scale_ne_zero v i), ← mul_assoc,
    ENNReal.inv_mul_cancel hms ENNReal.coe_ne_top, one_mul]

private theorem coupledKernel_lintegral_fibreWeightAt_le (N c j : ℤ) {a y : v.adicCompletion ℚ} (ha : a ≠ 0)
    (hy : Valued.v y = WithZero.exp j) (haN : Valued.v a ≤ WithZero.exp N) :
    (∫⁻ x, coupledKernel_fibreWeightAt v N c a y x ∂(selfDualHaarAt ℚ v)) ≤
      (modulus a : ENNReal) *
        (coupledKernel_ballMeasure v c * (1 + ((2 * N - j).toNat : ENNReal) + ((c + N).toNat : ENNReal))) := by
  have hy0 : y ≠ 0 := fun h => WithZero.exp_ne_zero (hy.symm.trans (by rw [h, map_zero]))
  have hva0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hαN : WithZero.log (Valued.v a) ≤ N := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hva0]; exact haN
  set I := coupledKernel_shellIndices N c j (WithZero.log (Valued.v a)) with hI
  have hcount : (I.card : ENNReal) ≤ ((2 * N - j).toNat : ENNReal) + ((c + N).toNat : ENNReal) := by
    exact_mod_cast coupledKernel_shellIndices_count_le N c j _ hαN
  have hK : (I.card : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1) ≤
      (((2 * N - j).toNat : ENNReal) + ((c + N).toNat : ENNReal)) *
        ((modulus a : ENNReal) * coupledKernel_ballMeasure v c) := by
    by_cases halive : 0 ≤ c + WithZero.log (Valued.v a)
    · exact (mul_le_mul_left hcount _).trans (mul_le_mul_right (coupledKernel_unitBall_le_of_nonneg v ha halive) _)
    · simp [hI, coupledKernel_shellIndices, halive]
  calc (∫⁻ x, coupledKernel_fibreWeightAt v N c a y x ∂(selfDualHaarAt ℚ v))
      ≤ ∫⁻ x, (coupledKernel_ballTerm v c a y x + (∑ i ∈ I, coupledKernel_shellTerm v i x)) ∂(selfDualHaarAt ℚ v) :=
        lintegral_mono fun x => coupledKernel_fibreWeightAt_le v N c j ha hy haN x
    _ = (∫⁻ x, coupledKernel_ballTerm v c a y x ∂(selfDualHaarAt ℚ v)) +
          ∑ i ∈ I, ∫⁻ x, coupledKernel_shellTerm v i x ∂(selfDualHaarAt ℚ v) := by
        rw [lintegral_add_left (coupledKernel_measurable_ballTerm v c ha hy0),
          lintegral_finsetSum _ fun i _ => coupledKernel_measurable_shellTerm v i]
    _ = (modulus a : ENNReal) * coupledKernel_ballMeasure v c +
          (I.card : ENNReal) * selfDualHaarAt ℚ v (coupledKernel_ball v 1) := by
        rw [coupledKernel_lintegral_ballTerm v c ha hy0,
          Finset.sum_congr rfl fun i _ => coupledKernel_lintegral_shellTerm v i, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (modulus a : ENNReal) * coupledKernel_ballMeasure v c +
          (((2 * N - j).toNat : ENNReal) + ((c + N).toNat : ENNReal)) *
            ((modulus a : ENNReal) * coupledKernel_ballMeasure v c) :=
        add_le_add le_rfl hK
    _ = _ := by ring

private theorem lintegral_coupledKernel_fibreWeight_le (N c : ℤ) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ (j : ℤ) (y : v.adicCompletion ℚ), Valued.v y = WithZero.exp j →
      ∀ a : v.adicCompletion ℚ, a ≠ 0 → Valued.v a ≤ WithZero.exp N →
        ∫⁻ w, coupledKernel_fibreWeight v N c a y w ∂(selfDualHaarAt ℚ v) ≤
          C * (1 + ((2 * N - j).toNat : ENNReal)) := by
  refine ⟨coupledKernel_ballMeasure v c * (1 + ((c + N).toNat : ENNReal)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (coupledKernel_ballMeasure_ne_top v c)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.natCast_ne_top _⟩)
  · intro j y hy a ha haN
    rw [coupledKernel_lintegral_fibreWeight_eq v N c ha y]
    have hma : (modulus a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero ha)
    have hX := coupledKernel_lintegral_fibreWeightAt_le v N c j ha hy haN
    set P : ENNReal := ((2 * N - j).toNat : ENNReal) with hP
    set Q : ENNReal := ((c + N).toNat : ENNReal) with hQ
    have hPQ : 1 + P + Q ≤ (1 + Q) * (1 + P) :=
      calc 1 + P + Q ≤ 1 + P + Q + Q * P := le_self_add
        _ = _ := by ring
    calc (modulus a : ENNReal)⁻¹ * ∫⁻ x, coupledKernel_fibreWeightAt v N c a y x ∂(selfDualHaarAt ℚ v)
        ≤ (modulus a : ENNReal)⁻¹ * ((modulus a : ENNReal) * (coupledKernel_ballMeasure v c * (1 + P + Q))) :=
          mul_le_mul_right hX _
      _ = coupledKernel_ballMeasure v c * (1 + P + Q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hma ENNReal.coe_ne_top, one_mul]
      _ ≤ coupledKernel_ballMeasure v c * ((1 + Q) * (1 + P)) := mul_le_mul_right hPQ _
      _ = _ := by ring

private theorem coupledKernel_truncChar_eq_zero {c : ℤ} {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp c) :
    truncChar v c t = 0 := by
  simp only [truncChar, if_neg h]

private theorem coupledKernel_enorm_le_ofReal {z : ℂ} {M : ℝ} (h : ‖z‖ ≤ M) : ‖z‖ₑ ≤ ENNReal.ofReal M := by
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h

private theorem coupledKernel_enorm_le_majorant (N c : ℤ) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    {BΦ M₂ M₁ M₀ Bψ : ℝ} (hBΦ : ∀ q, ‖Φ q‖ ≤ BΦ)
    (hsupp : ∀ a y w : v.adicCompletion ℚ, Φ ![a, y, w] ≠ 0 →
      Valued.v a ≤ WithZero.exp N ∧ Valued.v y ≤ WithZero.exp N ∧ Valued.v w ≤ WithZero.exp N)
    (hM₂ : ∀ t, ‖charExt (ν 2 * χ)⁻¹ t‖ ≤ M₂) (hM₁ : ∀ t, ‖charExt (ν 1 * χ) t‖ ≤ M₁)
    (hM₀ : ∀ t, ‖charExt (ν 0 * (ν 1)⁻¹) t‖ ≤ M₀) (hψ : ∀ t, ‖truncChar v c t‖ ≤ Bψ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ‖(Φ ![p.1, p.2.1, p.2.2] *
        (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
        (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
        truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2)))‖ₑ ≤
      coupledKernel_majorant v N c (BΦ * M₂ * M₁ * M₀ * Bψ) s.re p.1 p.2.1 p.2.2 := by
  have hBΦ0 : 0 ≤ BΦ := (norm_nonneg _).trans (hBΦ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hψ 0)
  by_cases hx : p.2.1 - p.1 * p.2.2 = 0
  · rw [hx]; simp
  have h1 : ‖Φ ![p.1, p.2.1, p.2.2]‖ₑ ≤
      ENNReal.ofReal BΦ *
        {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.1 *
        {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.2.1 *
        {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.2.2 := by
    by_cases hΦ : Φ ![p.1, p.2.1, p.2.2] = 0
    · rw [hΦ, enorm_zero]; exact zero_le
    · obtain ⟨ha, hy, hw⟩ := hsupp _ _ _ hΦ
      have ha' : p.1 ∈ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N} := ha
      have hy' : p.2.1 ∈ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N} := hy
      have hw' : p.2.2 ∈ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N} := hw
      simp only [Set.indicator_of_mem ha', Set.indicator_of_mem hy', Set.indicator_of_mem hw', mul_one]
      exact coupledKernel_enorm_le_ofReal (hBΦ _)
  have h2 : ‖charExt (ν 2 * χ)⁻¹ p.1‖ₑ ≤ ENNReal.ofReal M₂ := coupledKernel_enorm_le_ofReal (hM₂ _)
  have h3 : ‖((modulus p.1 : ℝ) : ℂ) ^ (1 - s)‖ₑ = ENNReal.ofReal ((modulus p.1 : ℝ) ^ (1 - s.re)) := by
    have hre : (1 - s).re ≠ 0 := by rw [Complex.sub_re, Complex.one_re]; exact (sub_pos.mpr hs').ne'
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_nonneg (NNReal.coe_nonneg _) hre, Complex.sub_re,
      Complex.one_re]
  have h4 : ‖charExt (ν 1 * χ) p.2.1‖ₑ ≤ ENNReal.ofReal M₁ := coupledKernel_enorm_le_ofReal (hM₁ _)
  have h5 : ‖((modulus p.2.1 : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal ((modulus p.2.1 : ℝ) ^ s.re) := by
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_nonneg (NNReal.coe_nonneg _) hs.ne']
  have h6 : ‖charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2)‖ₑ ≤ ENNReal.ofReal M₀ :=
    coupledKernel_enorm_le_ofReal (hM₀ _)
  have h7 : ‖((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹‖ₑ = ((modulus (p.2.1 - p.1 * p.2.2) : ENNReal))⁻¹ := by
    have hpos : (0 : ℝ) < modulus (p.2.1 - p.1 * p.2.2) := NNReal.coe_pos.mpr (modulus_pos hx)
    have hne : ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [enorm_inv hne, ← ofReal_norm, Complex.norm_of_nonneg hpos.le, ENNReal.ofReal_coe_nnreal]
  have h8 : ‖truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))‖ₑ ≤
      ENNReal.ofReal Bψ *
        Set.indicator
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v (p.2.1 - p.1 * t)}
          (fun _ => (1 : ENNReal)) p.2.2 := by
    by_cases hw : p.2.2 ∈ {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v (p.2.1 - p.1 * t)}
    · simp only [Set.indicator_of_mem hw, mul_one]
      exact coupledKernel_enorm_le_ofReal (hψ _)
    · have h0 : truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2)) = 0 := by
        refine coupledKernel_truncChar_eq_zero v fun hdiv => hw ?_
        show Valued.v p.2.2 ≤ WithZero.exp c * Valued.v (p.2.1 - p.1 * p.2.2)
        have h := mul_le_mul_left hdiv (Valued.v (p.2.1 - p.1 * p.2.2))
        rwa [map_div₀, div_mul_cancel₀ _ ((Valuation.ne_zero_iff _).mpr hx)] at h
      rw [h0, enorm_zero]; exact zero_le
  calc _ = ‖Φ ![p.1, p.2.1, p.2.2]‖ₑ * (‖charExt (ν 2 * χ)⁻¹ p.1‖ₑ * ‖((modulus p.1 : ℝ) : ℂ) ^ (1 - s)‖ₑ) *
        (‖charExt (ν 1 * χ) p.2.1‖ₑ * ‖((modulus p.2.1 : ℝ) : ℂ) ^ s‖ₑ) *
        (‖charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2)‖ₑ * ‖((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹‖ₑ) *
        ‖truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))‖ₑ := by simp only [enorm_mul]
    _ ≤ ENNReal.ofReal BΦ *
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.1 *
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.2.1 *
          {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) p.2.2 *
        (ENNReal.ofReal M₂ * ENNReal.ofReal ((modulus p.1 : ℝ) ^ (1 - s.re))) *
        (ENNReal.ofReal M₁ * ENNReal.ofReal ((modulus p.2.1 : ℝ) ^ s.re)) *
        (ENNReal.ofReal M₀ * ((modulus (p.2.1 - p.1 * p.2.2) : ENNReal))⁻¹) *
        (ENNReal.ofReal Bψ *
          Set.indicator
            {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp c * Valued.v (p.2.1 - p.1 * t)}
            (fun _ => (1 : ENNReal)) p.2.2) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' h1 (mul_le_mul' h2 h3.le)) (mul_le_mul' h4 h5.le))
        (mul_le_mul' h6 h7.le)) h8
    _ = _ := by
      unfold coupledKernel_majorant coupledKernel_fibreWeight
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hBΦ0 hM₂0) hM₁0) hM₀0),
        ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hBΦ0 hM₂0) hM₁0), ENNReal.ofReal_mul (mul_nonneg hBΦ0 hM₂0),
        ENNReal.ofReal_mul hBΦ0]
      ring

private theorem coupledKernel_exists_norm_charExt_le (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : v.adicCompletion ℚ, ‖charExt η t‖ ≤ M := by
  obtain ⟨Mη, hMη⟩ := LaurentLocalZeta.exists_bound_charExt_unitShell v η hη
  refine ⟨max Mη 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t = 0
  · simp [ht]
  obtain ⟨j, hj⟩ := LaurentLocalZeta.exists_mem_shell v ht
  rw [← LaurentLocalZeta.image_unitShell_eq_shell] at hj
  obtain ⟨u, hu, rfl⟩ := hj
  rw [charExt_mul ℚ v, charExt_coe_units, map_zpow, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hη1,
    one_zpow, one_mul]
  exact (hMη u hu).trans (le_max_left _ _)

private theorem coupledKernel_isLocallyConstant_mul (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hχ : IsLocallyConstant χ) : IsLocallyConstant (η * χ) := by
  have h : (⇑(η * χ) : (v.adicCompletion ℚ)ˣ → ℂˣ) = fun x => η x * χ x := by
    funext x
    simp
  rw [h]
  exact hη.mul hχ

private theorem coupledKernel_norm_mul_inv_apply_uniformizerUnit (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ‖(((ν 0 * (ν 1)⁻¹) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
  have h0 := hu 0
  have h1 := hu 1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
    norm_inv] at h0 h1 ⊢
  have hχ : ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h
    rw [h, mul_zero] at h0
    exact zero_ne_one h0
  have h01 : ‖((ν 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ =
      ‖((ν 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ :=
    mul_right_cancel₀ hχ (h0.trans h1.symm)
  have h1ne : ‖((ν 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  rw [h01, mul_inv_cancel₀ h1ne]

private theorem coupledKernel_exists_norm_testFn_le (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin 3 → v.adicCompletion ℚ, ‖Φ x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hΦl.continuous.bounded_above_of_compact_support hΦc
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

private theorem coupledKernel_exists_forall_valued_le_of_testFn_ne_zero (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦc : HasCompactSupport Φ) :
    ∃ N : ℤ, ∀ x : Fin 3 → v.adicCompletion ℚ, Φ x ≠ 0 → ∀ i : Fin 3, Valued.v (x i) ≤ WithZero.exp N := by
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (one_lt_absNorm_real v)
  refine ⟨n, fun x hx i => valued_le_of_norm_le_zpow v ?_⟩
  calc ‖x i‖ ≤ R := hR x hx i
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (n : ℤ) := by rw [zpow_natCast]; exact hn.le

private theorem coupledKernel_exists_forall_valued_le_of_testFn_vec_ne_zero (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦc : HasCompactSupport Φ) :
    ∃ N : ℤ, ∀ a y w : v.adicCompletion ℚ, Φ ![a, y, w] ≠ 0 →
      Valued.v a ≤ WithZero.exp N ∧ Valued.v y ≤ WithZero.exp N ∧ Valued.v w ≤ WithZero.exp N := by
  obtain ⟨N, hN⟩ := coupledKernel_exists_forall_valued_le_of_testFn_ne_zero v Φ hΦc
  refine ⟨N, fun a y w h => ?_⟩
  have h' := hN _ h
  exact ⟨by simpa using h' 0, by simpa using h' 1, by simpa using h' 2⟩

private theorem coupledKernel_measurable_testFn (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) :
    Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => Φ ![p.1, p.2.1, p.2.2] := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  refine (hΦl.continuous.comp ?_).measurable
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd.fst
  · exact continuous_snd.snd

private theorem coupledKernel_measurable_truncChar (c : ℤ) : Measurable (truncChar v c) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold truncChar
  exact Measurable.ite (isClosed_valued_le v c).measurableSet
    (NumberField.StandardAddChar.continuous_psiLocal ℚ v).measurable measurable_const

private theorem coupledKernel_measurable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hν : ∀ i, IsLocallyConstant (ν i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (s : ℂ) (c : ℤ) :
    Measurable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Φ ![p.1, p.2.1, p.2.2] *
          (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
          (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
          (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
          truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have h2 : IsLocallyConstant (ν 2 * χ)⁻¹ :=
    LaurentLocalZeta.isLocallyConstant_inv v _ (coupledKernel_isLocallyConstant_mul v _ _ (hν 2) hχ)
  have h1 : IsLocallyConstant (ν 1 * χ) := coupledKernel_isLocallyConstant_mul v _ _ (hν 1) hχ
  have h0 : IsLocallyConstant (ν 0 * (ν 1)⁻¹) :=
    coupledKernel_isLocallyConstant_mul v _ _ (hν 0) (LaurentLocalZeta.isLocallyConstant_inv v _ (hν 1))
  have hx : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      p.2.1 - p.1 * p.2.2 :=
    (continuous_snd.fst.sub (continuous_fst.mul continuous_snd.snd)).measurable
  have hdiv : Measurable fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      p.2.2 / (p.2.1 - p.1 * p.2.2) := by
    simp only [div_eq_mul_inv]
    exact measurable_snd.snd.mul hx.inv
  refine ((((coupledKernel_measurable_testFn v Φ hΦl).mul ?_).mul ?_).mul ?_).mul
    ((coupledKernel_measurable_truncChar v c).comp hdiv)
  · exact ((LaurentLocalZeta.measurable_charExt v _ h2).comp measurable_fst).mul
      ((LaurentLocalZeta.measurable_modulus_cpow v (1 - s)).comp measurable_fst)
  · exact ((LaurentLocalZeta.measurable_charExt v _ h1).comp measurable_snd.fst).mul
      ((LaurentLocalZeta.measurable_modulus_cpow v s).comp measurable_snd.fst)
  · exact ((LaurentLocalZeta.measurable_charExt v _ h0).comp hx).mul
      (Complex.measurable_ofReal.comp ((LaurentLocalZeta.measurable_modulus v).comp hx)).inv

private theorem coupledKernel_exists_norm_truncChar_le (c : ℤ) :
    ∃ Bψ : ℝ, 0 ≤ Bψ ∧ ∀ t : v.adicCompletion ℚ, ‖truncChar v c t‖ ≤ Bψ := by
  set u : v.adicCompletion ℚ :=
    ((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-c) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) with hu_def
  have hu : Valued.v u = WithZero.exp c := by
    rw [hu_def, LaurentLocalZeta.valued_uniformizerUnit_zpow, neg_neg]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  set S : Set (v.adicCompletion ℚ) :=
    (fun x => u * x) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  have hScompact : IsCompact S := by
    have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [← coe_integersPositiveCompacts ℚ v]
      exact (integersPositiveCompacts ℚ v).isCompact
    exact hO.image (continuous_const.mul continuous_id)
  obtain ⟨Bψ, hBψ⟩ :=
    hScompact.exists_bound_of_continuousOn (NumberField.StandardAddChar.continuous_psiLocal ℚ v).continuousOn
  refine ⟨max Bψ 0, le_max_right _ _, fun t => ?_⟩
  unfold truncChar
  split_ifs with ht
  · refine (hBψ t ⟨u⁻¹ * t, ?_, ?_⟩).trans (le_max_left _ _)
    · rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hu]
      calc (WithZero.exp c)⁻¹ * Valued.v t ≤ (WithZero.exp c)⁻¹ * WithZero.exp c := by gcongr
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · show u * (u⁻¹ * t) = t
      rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  · simp

private theorem coupledKernel_mulMeasure_image (u : (v.adicCompletion ℚ)ˣ) (S : Set (v.adicCompletion ℚ))
    (hS : MeasurableSet ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) '' S)) :
    mulMeasure (selfDualHaarAt ℚ v) ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) '' S) =
      mulMeasure (selfDualHaarAt ℚ v) S := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hmeas : Measurable fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x :=
    (continuous_const.mul continuous_id).measurable
  have hinj : Function.Injective fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x :=
    mul_right_injective₀ u.ne_zero
  calc mulMeasure (selfDualHaarAt ℚ v) ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) '' S)
      = (Measure.map (fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) (mulMeasure (selfDualHaarAt ℚ v)))
          ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) '' S) := by
        rw [map_mul_left_mulMeasure ℚ v u]
    _ = mulMeasure (selfDualHaarAt ℚ v)
          ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) ⁻¹'
            ((fun x : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * x) '' S)) :=
        Measure.map_apply hmeas hS
    _ = mulMeasure (selfDualHaarAt ℚ v) S := by rw [Set.preimage_image_eq S hinj]

private theorem coupledKernel_mulMeasure_shell (j : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.shell v j) =
      mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) := by
  rw [← LaurentLocalZeta.image_unitShell_eq_shell v j]
  refine coupledKernel_mulMeasure_image v _ _ ?_
  rw [LaurentLocalZeta.image_unitShell_eq_shell v j]
  exact LaurentLocalZeta.measurableSet_shell v j

private theorem coupledKernel_mulMeasure_unitShell_ne_top :
    mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) ≠ ⊤ := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  rw [LaurentLocalZeta.mulMeasure_unitShell]
  exact (LaurentLocalZeta.isCompact_unitShell v).measure_lt_top.ne

private theorem coupledKernel_summable_geometric_mul_linear {A r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    Summable fun n : ℕ => A * (r ^ n * ((1 + K + n : ℕ) : ℝ)) := by
  have hgeo : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
  have hpow : Summable fun n : ℕ => (n : ℝ) ^ 1 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  refine (((hgeo.mul_left ((1 + K : ℕ) : ℝ)).add hpow).congr fun n => ?_).mul_left A
  push_cast
  ring

private theorem coupledKernel_cube_weight_le_of_mem_shell (N : ℤ) (τ : ℝ) (n : ℕ)
    {t : v.adicCompletion ℚ} (ht : t ∈ LaurentLocalZeta.shell v ((n : ℤ) - N)) :
    {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) t *
        ENNReal.ofReal ((modulus t : ℝ) ^ τ) ≤
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ ((N : ℝ) * τ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-τ)) ^ n) := by
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)
  have hreal : (modulus t : ℝ) ^ τ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ ((N : ℝ) * τ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-τ)) ^ n := by
    rw [LaurentLocalZeta.coe_modulus_eq_of_mem_shell v ht, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [hreal]
  unfold Set.indicator
  split_ifs <;> simp

private theorem lintegral_coupledKernel_le_of_forall_mem_shell_le (N : ℤ) {h : v.adicCompletion ℚ → ENNReal}
    (hsupp : ∀ t, h t ≠ 0 → t ≠ 0 ∧ Valued.v t ≤ WithZero.exp N) {K₀ : ENNReal} {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g)
    (hb : ∀ n : ℕ, ∀ t ∈ LaurentLocalZeta.shell v ((n : ℤ) - N), h t ≤ K₀ * ENNReal.ofReal (g n)) :
    (∫⁻ t, h t ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤
      K₀ * mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) * ENNReal.ofReal (∑' n, g n) := by
  have hsub : Function.support h ⊆ ⋃ n : ℕ, LaurentLocalZeta.shell v ((n : ℤ) - N) := by
    intro t ht
    obtain ⟨ht0, htN⟩ := hsupp t ht
    obtain ⟨j, hj⟩ := LaurentLocalZeta.exists_mem_shell v ht0
    have hjN : -j ≤ N := by
      have hj' : Valued.v t = WithZero.exp (-j) := hj
      rw [hj'] at htN
      exact WithZero.exp_le_exp.mp htN
    refine Set.mem_iUnion.mpr ⟨(j + N).toNat, ?_⟩
    have hn : (((j + N).toNat : ℕ) : ℤ) - N = j := by omega
    rw [hn]
    exact hj
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => LaurentLocalZeta.shell v ((n : ℤ) - N)) := by
    intro n m hnm
    change Disjoint (LaurentLocalZeta.shell v ((n : ℤ) - N)) (LaurentLocalZeta.shell v ((m : ℤ) - N))
    refine Set.disjoint_left.mpr fun t htn htm => hnm ?_
    have h1 : Valued.v t = WithZero.exp (-((n : ℤ) - N)) := htn
    have h2 : Valued.v t = WithZero.exp (-((m : ℤ) - N)) := htm
    have h12 := h1.symm.trans h2
    have hle := WithZero.exp_le_exp.mp h12.le
    have hge := WithZero.exp_le_exp.mp h12.ge
    omega
  calc (∫⁻ t, h t ∂(mulMeasure (selfDualHaarAt ℚ v)))
      = ∫⁻ t in ⋃ n : ℕ, LaurentLocalZeta.shell v ((n : ℤ) - N), h t ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
        (setLIntegral_eq_of_support_subset hsub).symm
    _ = ∑' n : ℕ, ∫⁻ t in LaurentLocalZeta.shell v ((n : ℤ) - N), h t ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
        lintegral_iUnion (fun n => LaurentLocalZeta.measurableSet_shell v _) hdisj h
    _ ≤ ∑' n : ℕ, K₀ * mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) * ENNReal.ofReal (g n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        calc (∫⁻ t in LaurentLocalZeta.shell v ((n : ℤ) - N), h t ∂(mulMeasure (selfDualHaarAt ℚ v)))
            ≤ ∫⁻ _ in LaurentLocalZeta.shell v ((n : ℤ) - N), K₀ * ENNReal.ofReal (g n)
                ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
              setLIntegral_mono measurable_const (hb n)
          _ = K₀ * ENNReal.ofReal (g n) * mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.shell v ((n : ℤ) - N)) :=
              setLIntegral_const _ _
          _ = K₀ * mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) * ENNReal.ofReal (g n) := by
              rw [coupledKernel_mulMeasure_shell]
              ring
    _ = K₀ * mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v) * ENNReal.ofReal (∑' n, g n) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hg0 hg]

private theorem coupledKernel_cube_weight_ne_top (N : ℤ) (x : ℝ) (t : v.adicCompletion ℚ) :
    {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) t *
      ENNReal.ofReal x ≠ ⊤ := by
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  unfold Set.indicator
  split_ifs <;> simp

private theorem coupledKernel_of_cube_weight_ne_zero (N : ℤ) {τ : ℝ} (hτ : τ ≠ 0) {t : v.adicCompletion ℚ}
    (ht : {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) t *
      ENNReal.ofReal ((modulus t : ℝ) ^ τ) ≠ 0) :
    t ≠ 0 ∧ Valued.v t ≤ WithZero.exp N := by
  refine ⟨fun h0 => ht ?_, ?_⟩
  · rw [h0, modulus_zero, NNReal.coe_zero, Real.zero_rpow hτ, ENNReal.ofReal_zero, mul_zero]
  · by_contra hN
    apply ht
    simp only [Set.indicator, Set.mem_setOf_eq, hN, if_false, zero_mul]

private theorem lintegral_coupledKernel_majorant_lt_top (N c : ℤ) (B : ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∫⁻ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
        coupledKernel_majorant v N c B σ p.1 p.2.1 p.2.2
      ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) <
      ⊤ := by
  haveI : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := sFinite_mulMeasure_selfDualHaarAt ℚ v
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  obtain ⟨C, hC, hCw⟩ := lintegral_coupledKernel_fibreWeight_le v N c
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  have hr0 : ∀ τ : ℝ, 0 ≤ q ^ (-τ) := fun τ => Real.rpow_nonneg hq0.le _
  have hr1 : ∀ τ : ℝ, 0 < τ → q ^ (-τ) < 1 := fun τ hτ =>
    Real.rpow_lt_one_of_one_lt_of_neg hq1 (neg_lt_zero.mpr hτ)
  set V : ENNReal := mulMeasure (selfDualHaarAt ℚ v) (LaurentLocalZeta.unitShell v)
  have hV : V ≠ ⊤ := coupledKernel_mulMeasure_unitShell_ne_top v

  set gy : ℕ → ℝ := fun n => q ^ ((N : ℝ) * σ) * ((q ^ (-σ)) ^ n * ((1 + N.toNat + n : ℕ) : ℝ)) with hgy_def
  have hgy0 : ∀ n, 0 ≤ gy n := fun n => by simp only [hgy_def]; positivity
  have hgy : Summable gy := coupledKernel_summable_geometric_mul_linear (hr0 σ) (hr1 σ hσ0) N.toNat

  set ga : ℕ → ℝ := fun n => q ^ ((N : ℝ) * (1 - σ)) * ((q ^ (-(1 - σ))) ^ n * ((1 + 0 + n : ℕ) : ℝ)) with hga_def
  have hga0 : ∀ n, 0 ≤ ga n := fun n => by simp only [hga_def]; positivity
  have hga : Summable ga :=
    coupledKernel_summable_geometric_mul_linear (hr0 (1 - σ)) (hr1 (1 - σ) (sub_pos.mpr hσ1)) 0

  set wa : v.adicCompletion ℚ → ENNReal := fun a =>
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) a *
      ENNReal.ofReal ((modulus a : ℝ) ^ (1 - σ))
  set wy : v.adicCompletion ℚ → ENNReal := fun y =>
    {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp N}.indicator (fun _ => (1 : ENNReal)) y *
      ENNReal.ofReal ((modulus y : ℝ) ^ σ)
  have hmaj : ∀ a y w, coupledKernel_majorant v N c B σ a y w =
      ENNReal.ofReal B * wa a * wy y * coupledKernel_fibreWeight v N c a y w := fun a y w => rfl

  have hstep1 : ∀ a y, (∫⁻ w, coupledKernel_majorant v N c B σ a y w ∂(selfDualHaarAt ℚ v)) =
      ENNReal.ofReal B * wa a * wy y * ∫⁻ w, coupledKernel_fibreWeight v N c a y w ∂(selfDualHaarAt ℚ v) := by
    intro a y
    simp_rw [hmaj]
    exact lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (coupledKernel_cube_weight_ne_top v N _ a))
        (coupledKernel_cube_weight_ne_top v N _ y))

  set Y : ENNReal := ENNReal.ofReal B * C * V * ENNReal.ofReal (∑' n, gy n) with hY_def
  have hY : Y ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hV) ENNReal.ofReal_ne_top
  have hstep2 : ∀ a, (∫⁻ y, ∫⁻ w, coupledKernel_majorant v N c B σ a y w ∂(selfDualHaarAt ℚ v)
      ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤ wa a * Y := by
    intro a
    by_cases ha : wa a = 0
    · simp_rw [hstep1, ha, mul_zero, zero_mul, lintegral_zero]
      exact zero_le
    obtain ⟨ha0, haN⟩ := coupledKernel_of_cube_weight_ne_zero v N (sub_ne_zero.mpr hσ1.ne') ha
    calc (∫⁻ y, ∫⁻ w, coupledKernel_majorant v N c B σ a y w ∂(selfDualHaarAt ℚ v)
            ∂(mulMeasure (selfDualHaarAt ℚ v)))
        ≤ ENNReal.ofReal B * wa a * C * V * ENNReal.ofReal (∑' n, gy n) := by
          refine lintegral_coupledKernel_le_of_forall_mem_shell_le v N (K₀ := ENNReal.ofReal B * wa a * C)
            (fun y hy => ?_) hgy0 hgy fun n y hy => ?_
          · refine coupledKernel_of_cube_weight_ne_zero v N hσ0.ne' fun h0 => hy ?_
            have hwy0 : wy y = 0 := h0
            rw [hstep1]
            simp only [hwy0, mul_zero, zero_mul]
          · rw [hstep1]
            have hfib := hCw (-((n : ℤ) - N)) y hy a ha0 haN
            have hlin : (1 + (((2 * N - -((n : ℤ) - N)).toNat : ℕ) : ENNReal)) ≤
                ENNReal.ofReal ((1 + N.toNat + n : ℕ) : ℝ) := by
              rw [ENNReal.ofReal_natCast]
              have hnat : 1 + (2 * N - -((n : ℤ) - N)).toNat ≤ 1 + N.toNat + n := by omega
              exact_mod_cast hnat
            have hwy : wy y ≤ ENNReal.ofReal (q ^ ((N : ℝ) * σ) * (q ^ (-σ)) ^ n) :=
              coupledKernel_cube_weight_le_of_mem_shell v N σ n hy
            calc ENNReal.ofReal B * wa a * wy y *
                  ∫⁻ w, coupledKernel_fibreWeight v N c a y w ∂(selfDualHaarAt ℚ v)
                ≤ ENNReal.ofReal B * wa a * ENNReal.ofReal (q ^ ((N : ℝ) * σ) * (q ^ (-σ)) ^ n) *
                    (C * ENNReal.ofReal ((1 + N.toNat + n : ℕ) : ℝ)) := by
                  exact mul_le_mul' (mul_le_mul' le_rfl hwy) (hfib.trans (mul_le_mul' le_rfl hlin))
              _ = ENNReal.ofReal B * wa a * C * ENNReal.ofReal (gy n) := by
                  simp only [hgy_def]
                  rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul]
                  · ring
                  all_goals positivity
      _ = wa a * Y := by
          rw [hY_def]
          ring

  have hstep3 : (∫⁻ a, ∫⁻ y, ∫⁻ w, coupledKernel_majorant v N c B σ a y w ∂(selfDualHaarAt ℚ v)
      ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v))) ≤
        Y * V * ENNReal.ofReal (∑' n, ga n) := by
    refine lintegral_coupledKernel_le_of_forall_mem_shell_le v N (K₀ := Y) (fun a ha => ?_) hga0 hga
      fun n a ha => ?_
    · refine coupledKernel_of_cube_weight_ne_zero v N (sub_ne_zero.mpr hσ1.ne') fun h0 => ha ?_
      have hwa0 : wa a = 0 := h0
      refine le_antisymm ((hstep2 a).trans ?_) zero_le
      simp only [hwa0, zero_mul, le_refl]
    · refine (hstep2 a).trans ?_
      have hwa : wa a ≤ ENNReal.ofReal (q ^ ((N : ℝ) * (1 - σ)) * (q ^ (-(1 - σ))) ^ n) :=
        coupledKernel_cube_weight_le_of_mem_shell v N (1 - σ) n ha
      calc wa a * Y ≤ ENNReal.ofReal (q ^ ((N : ℝ) * (1 - σ)) * (q ^ (-(1 - σ))) ^ n) * Y := mul_le_mul_left hwa Y
        _ ≤ Y * ENNReal.ofReal (ga n) := by
          rw [mul_comm]
          simp only [hga_def]
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) Y
          have hL : (1 : ℝ) ≤ ((1 + 0 + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 1 + 0 + n)
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hL) (by positivity)

  refine (lintegral_prod_le _).trans_lt ?_
  refine (lintegral_mono fun a => lintegral_prod_le _).trans_lt ?_
  refine hstep3.trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hY.lt_top hV.lt_top) ENNReal.ofReal_lt_top

private theorem integrable_coupledIntegrand
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (c : ℤ) :
    Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Φ ![p.1, p.2.1, p.2.2] *
          (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
          (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
          (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
          truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2)))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))) := by
  obtain ⟨BΦ, -, hBΦ⟩ := coupledKernel_exists_norm_testFn_le v Φ hΦl hΦc
  obtain ⟨N, hN⟩ := coupledKernel_exists_forall_valued_le_of_testFn_vec_ne_zero v Φ hΦc
  obtain ⟨M₂, -, hM₂⟩ := coupledKernel_exists_norm_charExt_le v _
    (LaurentLocalZeta.isLocallyConstant_inv v _ (coupledKernel_isLocallyConstant_mul v _ _ (hν 2) hχ))
    (norm_inv_apply_uniformizerUnit ℚ v (hu 2))
  obtain ⟨M₁, -, hM₁⟩ :=
    coupledKernel_exists_norm_charExt_le v _ (coupledKernel_isLocallyConstant_mul v _ _ (hν 1) hχ) (hu 1)
  obtain ⟨M₀, -, hM₀⟩ := coupledKernel_exists_norm_charExt_le v _
    (coupledKernel_isLocallyConstant_mul v _ _ (hν 0) (LaurentLocalZeta.isLocallyConstant_inv v _ (hν 1)))
    (coupledKernel_norm_mul_inv_apply_uniformizerUnit v ν χ hu)
  obtain ⟨Bψ, -, hBψ⟩ := coupledKernel_exists_norm_truncChar_le v c
  refine ⟨(coupledKernel_measurable v ν hν Φ hΦl χ hχ s c).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine (lintegral_mono fun p =>
      coupledKernel_enorm_le_majorant v N c ν Φ χ s hs hs' hBΦ hN hM₂ hM₁ hM₀ hBψ p).trans_lt ?_
  exact lintegral_coupledKernel_majorant_lt_top v N c _ hs hs'

end LanglandsTunnell.CubicInduction
end

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.LanglandsTunnell.TateLocal _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.LanglandsTunnell.CubicInduction in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (c : ℤ) :
    Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Φ ![p.1, p.2.1, p.2.2] *
          (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
          (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
          (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
          (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
            (NumberField.StandardAddChar.psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ) else 0))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))) :=
  integrable_coupledIntegrand v ν hν Φ hΦl hΦc χ hχ hu s hs hs' c

end S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand (solution)
