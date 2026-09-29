-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/438c179a-9e94-578d-816b-fb8f5d0dc442

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain
p2m_open "IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"

namespace DegreeOneCompletion

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

private theorem isScalarTower_int : IsScalarTower ℤ (𝓞 E) (𝓞 M) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private theorem moduleFinite_integers : Module.Finite (𝓞 E) (𝓞 M) :=
  haveI := isScalarTower_int (E := E) (M := M)
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) (𝓞 M)

private theorem isScalarTower_rat : IsScalarTower ℚ E M :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private theorem finiteDimensional : FiniteDimensional E M :=
  haveI := isScalarTower_rat (E := E) (M := M)
  Module.Finite.of_restrictScalars_finite ℚ E M

variable (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
  (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 1)

include he hf

private theorem finrank_eq_one : Module.finrank (v.adicCompletion E) (w.1.adicCompletion M) = 1 := by
  haveI := finiteDimensional (E := E) (M := M)
  haveI := moduleFinite_integers (E := E) (M := M)
  rw [← adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank (K := E) (L := M) (w := w), he, hf,
    mul_one]

private theorem bijective_algebraMap :
    Function.Bijective (algebraMap (v.adicCompletion E) (w.1.adicCompletion M)) :=
  (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp (finrank_eq_one v w he hf)

private theorem _root_.DegreeOneCompletion.norm_algebraMap (x : v.adicCompletion E) :
    Algebra.norm (v.adicCompletion E) (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x) = x := by
  rw [Algebra.norm_algebraMap, finrank_eq_one v w he hf, pow_one]

p2m_export "DegreeOneCompletion" "norm_algebraMap"
private theorem _root_.DegreeOneCompletion.trace_algebraMap (x : v.adicCompletion E) :
    Algebra.trace (v.adicCompletion E) (w.1.adicCompletion M)
      (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x) = x := by
  rw [Algebra.trace_algebraMap, finrank_eq_one v w he hf, one_smul]

p2m_export "DegreeOneCompletion" "trace_algebraMap"
private theorem algebraMap_norm (y : w.1.adicCompletion M) :
    algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (Algebra.norm (v.adicCompletion E) y) = y := by
  obtain ⟨x, rfl⟩ := (bijective_algebraMap v w he hf).2 y
  rw [norm_algebraMap v w he hf]

private theorem algebraMap_trace (y : w.1.adicCompletion M) :
    algebraMap (v.adicCompletion E) (w.1.adicCompletion M)
      (Algebra.trace (v.adicCompletion E) (w.1.adicCompletion M) y) = y := by
  obtain ⟨x, rfl⟩ := (bijective_algebraMap v w he hf).2 y
  rw [trace_algebraMap v w he hf]

private theorem comp_norm_map_algebraMap (μ : (v.adicCompletion E)ˣ →* ℂˣ) (x : (v.adicCompletion E)ˣ) :
    (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))
        (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) x) = μ x := by
  rw [MonoidHom.comp_apply]
  congr 1
  ext
  simp [norm_algebraMap v w he hf]

private theorem units_map_surjective :
    Function.Surjective
      (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M)) := by
  intro y
  refine ⟨Units.mk0 (Algebra.norm (v.adicCompletion E) (y : w.1.adicCompletion M)) ?_, ?_⟩
  · intro h
    have h' := algebraMap_norm v w he hf (y : w.1.adicCompletion M)
    rw [h, map_zero] at h'
    exact y.ne_zero h'.symm
  · ext
    simp [algebraMap_norm v w he hf]

private theorem valued_algebraMap (x : v.adicCompletion E) :
    Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x) = Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom E M x) = Valued.v x
  rw [w.valued_adicCompletionSemialgHom E M, w.2, he, pow_one]

private theorem map_mem_higherUnitsAt_iff (n : ℕ) (u : (v.adicCompletion E)ˣ) :
    Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) u
        ∈ higherUnitsAt M w.1 n ↔
      u ∈ higherUnitsAt E v n := by
  have h1 : ((Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) u :
      (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M) =
        algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (u : v.adicCompletion E) := rfl
  rw [mem_higherUnitsAt_iff, mem_higherUnitsAt_iff, h1, valued_algebraMap v w he hf,
    ← map_one (algebraMap (v.adicCompletion E) (w.1.adicCompletion M)), ← map_sub,
    valued_algebraMap v w he hf]

private theorem hasConductorExponentAt_comp_norm (μ : (v.adicCompletion E)ˣ →* ℂˣ) (c : ℕ)
    (hμc : HasConductorExponentAt E v μ c) :
    HasConductorExponentAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) c := by
  refine ⟨fun y hy => ?_, fun m hm => ?_⟩
  · obtain ⟨x, rfl⟩ := units_map_surjective v w he hf y
    rw [comp_norm_map_algebraMap v w he hf]
    exact hμc.1 x ((map_mem_higherUnitsAt_iff v w he hf c x).mp hy)
  · obtain ⟨x, hx, hne⟩ := hμc.2 m hm
    refine ⟨_, (map_mem_higherUnitsAt_iff v w he hf m x).mpr hx, ?_⟩
    rwa [comp_norm_map_algebraMap v w he hf]

private theorem apply_eq_apply_uniformizerUnit_of_zero (μ : (v.adicCompletion E)ˣ →* ℂˣ)
    (hμ0 : HasConductorExponentAt E v μ 0) (x : (v.adicCompletion E)ˣ)
    (hx : Valued.v (x : v.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    μ x = μ (uniformizerUnit E v) := by
  have hu : Valued.v (((uniformizerUnit E v)⁻¹ * x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit, hx,
      inv_mul_cancel₀ WithZero.exp_ne_zero]
  have h1 : μ ((uniformizerUnit E v)⁻¹ * x) = 1 := (hasConductorExponentAt_zero_iff E v).mp hμ0 _ hu
  calc μ x = μ (uniformizerUnit E v * ((uniformizerUnit E v)⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = μ (uniformizerUnit E v) := by rw [map_mul, h1, mul_one]

private theorem comp_norm_uniformizerUnit_of_zero (μ : (v.adicCompletion E)ˣ →* ℂˣ)
    (hμ0 : HasConductorExponentAt E v μ 0) :
    (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) (uniformizerUnit M w.1) =
      μ (uniformizerUnit E v) := by
  obtain ⟨x, hx⟩ := units_map_surjective v w he hf (uniformizerUnit M w.1)
  have hvx : Valued.v (x : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [← valued_algebraMap v w he hf]
    have := congrArg (fun y : (w.1.adicCompletion M)ˣ => Valued.v (y : w.1.adicCompletion M)) hx
    simpa [valued_uniformizerUnit] using this
  rw [← hx, comp_norm_map_algebraMap v w he hf, apply_eq_apply_uniformizerUnit_of_zero v w he hf μ hμ0 x hvx]

private theorem stdRootNumberAt_comp_norm_of_zero (μ : (v.adicCompletion E)ˣ →* ℂˣ)
    (hμ0 : HasConductorExponentAt E v μ 0) (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    stdRootNumberAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) =
      stdRootNumberAt E v μ := by
  have hE := stdRootNumberAt_mul_of_hasConductorExponentAt_zero E v 1 μ 0
    (hasConductorExponentAt_one_zero E v) hμ0 (by simp) hμ (psiLocal_ne_one E v)
  have hM := stdRootNumberAt_mul_of_hasConductorExponentAt_zero M w.1 1
    (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) 0 (hasConductorExponentAt_one_zero M w.1)
    (hasConductorExponentAt_comp_norm v w he hf μ 0 hμ0) (by simp)
    (by rw [comp_norm_uniformizerUnit_of_zero v w he hf μ hμ0]; exact hμ) (psiLocal_ne_one M w.1)
  have hE' : stdRootNumberAt E v μ = _ := (congrArg (stdRootNumberAt E v) (one_mul μ)).symm.trans hE
  have hM' : stdRootNumberAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) = _ :=
    (congrArg (stdRootNumberAt M w.1) (one_mul _)).symm.trans hM
  rw [hE', hM', stdRootNumberAt_one E v, stdRootNumberAt_one M w.1,
    comp_norm_uniformizerUnit_of_zero v w he hf μ hμ0,
    addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w he]

private theorem mem_integers_iff (x : v.adicCompletion E) :
    algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x ∈ w.1.adicCompletionIntegers M ↔
      x ∈ v.adicCompletionIntegers E := by
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, valued_algebraMap v w he hf]

private theorem coe_integers_algebraMap (x : v.adicCompletionIntegers E) :
    ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x : w.1.adicCompletionIntegers M) :
        w.1.adicCompletion M) =
      algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (x : v.adicCompletion E) := rfl

private theorem integers_algebraMap_bijective :
    Function.Bijective (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (bijective_algebraMap v w he hf).1
    rw [← coe_integers_algebraMap v w he hf, ← coe_integers_algebraMap v w he hf, hxy]
  · intro y
    obtain ⟨x, hx⟩ := (bijective_algebraMap v w he hf).2 (y : w.1.adicCompletion M)
    have hxI : x ∈ v.adicCompletionIntegers E := (mem_integers_iff v w he hf x).mp (hx ▸ y.2)
    exact ⟨⟨x, hxI⟩, Subtype.ext (by rw [coe_integers_algebraMap v w he hf]; exact hx)⟩

end DegreeOneCompletion

open MeasureTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open scoped Pointwise
open NumberField.AdelicHaar

set_option synthInstance.maxHeartbeats 1600000

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique hasConductorExponentAt_one_zero localEpsilonAt_of_not_hasConductorExponentAt_zero tateFourier charExt charExt_of_ne_zero localZeta stdRootNumberAt_mul_of_hasConductorExponentAt_zero stdRootNumberAt_one psiLocal_ne_one addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt stdRootNumberAt_ne_zero_of_hasConductorExponentAt forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers selfDualHaarAt_real_image_higherUnitsAt"
namespace UnitIntegral
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_pow (m : ℕ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-(m : ℤ)) := by
  rw [Units.val_pow_eq_pow_val, map_pow, valued_uniformizerUnit, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem _root_.LanglandsTunnell.TateLocal.UnitIntegral.valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

p2m_export "LanglandsTunnell.TateLocal.UnitIntegral" "valued_uniformizerUnit_zpow"
private theorem ball_eq_smul_integers (k : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ)
          • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hu : Valued.v ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp k := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  have hu' : Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp (-k) := valued_uniformizerUnit_zpow K v k
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, SetLike.mem_coe, mem_adicCompletionIntegers]
  constructor
  · intro hx
    refine ⟨((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x, ?_, ?_⟩
    · rw [map_mul, hu']
      calc WithZero.exp (-k) * Valued.v x ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_right hx _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one,
        one_mul]
  · rintro ⟨y, hy, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hu]
    calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul_right hy _
      _ = WithZero.exp k := mul_one _

private theorem isOpen_ball (k : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have hO : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := Valued.isOpen_valuationSubring _
  rw [ball_eq_smul_integers K v k]
  exact hO.smul _

private theorem setOf_valued_sub_le_eq_preimage (t : v.adicCompletion K) (k : ℤ) :
    {x : v.adicCompletion K | Valued.v (x - t) ≤ WithZero.exp k}
      = (fun x : v.adicCompletion K => -t + x) ⁻¹' {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub]

private theorem measurableSet_setOf_valued_sub_le [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (t : v.adicCompletion K) (k : ℤ) :
    MeasurableSet {x : v.adicCompletion K | Valued.v (x - t) ≤ WithZero.exp k} := by
  rw [setOf_valued_sub_le_eq_preimage]
  exact ((isOpen_ball K v k).preimage (continuous_const.add continuous_id)).measurableSet

private theorem measure_setOf_valued_sub_le [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (t : v.adicCompletion K) (k : ℤ) :
    μ {x : v.adicCompletion K | Valued.v (x - t) ≤ WithZero.exp k}
      = μ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  rw [setOf_valued_sub_le_eq_preimage, measure_preimage_add]

private theorem exp_neg_lt_one {a : ℕ} (ha : 1 ≤ a) :
    WithZero.exp (-(a : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by omega)

private theorem le_exp_neg_one_of_lt_one {x : v.adicCompletion K} (hx : Valued.v x < 1) :
    Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    exact WithZero.exp_le_exp.mpr (by omega)

private theorem image_higherUnitsAt {a : ℕ} (ha : 1 ≤ a) :
    ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a
      = {x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨-, h0 | h⟩ := (mem_higherUnitsAt_iff K v).mp hu
    · omega
    · exact h
  · intro hx
    have hlt : Valued.v (x - 1) < Valued.v (1 : v.adicCompletion K) := by
      rw [map_one]
      exact hx.trans_lt (exp_neg_lt_one ha)
    have hvx : Valued.v x = 1 := by
      have h := Valuation.map_eq_of_sub_lt _ hlt
      rwa [map_one] at h
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvx]; exact one_ne_zero)
    refine ⟨Units.mk0 x hx0, (mem_higherUnitsAt_iff K v).mpr ⟨?_, Or.inr ?_⟩, Units.val_mk0 hx0⟩
    · rw [Units.val_mk0, hvx]
    · rw [Units.val_mk0]
      exact hx

private theorem mem_maximalIdeal_pow_iff (a : ℕ) (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a
      ↔ Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(a : ℤ)) := by
  constructor
  · intro hx
    induction a generalizing x with
    | zero =>
      have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
      simpa using hx1
    | succ a ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro y hy z hz
        have hy' := ih y hy
        have hz' := le_exp_neg_one_of_lt_one K v ((mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v z).mp hz)
        calc Valued.v ((y * z : v.adicCompletionIntegers K) : v.adicCompletion K)
            = Valued.v (y : v.adicCompletion K) * Valued.v (z : v.adicCompletion K) := by
              rw [Subring.coe_mul, map_mul]
          _ ≤ WithZero.exp (-(a : ℤ)) * WithZero.exp (-1 : ℤ) := mul_le_mul' hy' hz'
          _ = WithZero.exp (-((a + 1 : ℕ) : ℤ)) := by
              rw [← WithZero.exp_add]
              congr 1
              push_cast
              ring
      · intro y z hy hz
        rw [Subring.coe_add]
        exact (Valuation.map_add _ _ _).trans (max_le hy hz)
  · intro hx

    set P : v.adicCompletion K := ((uniformizerUnit K v ^ a : (v.adicCompletion K)ˣ) : v.adicCompletion K) with hP
    have hPv : Valued.v P = WithZero.exp (-(a : ℤ)) := by rw [hP, valued_uniformizerUnit_pow]
    have hP0 : P ≠ 0 := Units.ne_zero _
    have hϖint : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K)
        ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, valued_uniformizerUnit, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    set ϖ : v.adicCompletionIntegers K := ⟨_, hϖint⟩ with hϖ
    have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
      rw [mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
      show Valued.v ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) < 1
      rw [valued_uniformizerUnit, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hyint : (x : v.adicCompletion K) / P ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, hPv, div_le_one₀ WithZero.exp_pos]
      exact hx
    set y : v.adicCompletionIntegers K := ⟨_, hyint⟩ with hy
    have hxy : x = ϖ ^ a * y := by
      apply Subtype.ext
      rw [Subring.coe_mul, SubmonoidClass.coe_pow]
      show (x : v.adicCompletion K) = P * ((x : v.adicCompletion K) / P)
      rw [mul_div_cancel₀ _ hP0]
    rw [hxy]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖmem a)

private theorem mk_eq_mk_iff (a : ℕ) (x y : v.adicCompletionIntegers K) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) y
      ↔ Valued.v ((x : v.adicCompletion K) - y) ≤ WithZero.exp (-(a : ℤ)) := by
  rw [Ideal.Quotient.eq, mem_maximalIdeal_pow_iff]
  exact Iff.rfl

private noncomputable def rep (a : ℕ)
    (r : v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) :
    v.adicCompletionIntegers K :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

private theorem
    mk_rep
    (a : ℕ) (r : v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (rep K v a r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

private theorem valued_eq_one_of_isUnit_mk {a : ℕ} (ha : 1 ≤ a) {x : v.adicCompletionIntegers K}
    (hx : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x)) :
    Valued.v (x : v.adicCompletion K) = 1 := by
  obtain ⟨r, hr⟩ := hx
  set y := rep K v a ↑(r⁻¹) with hy
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (x * y)
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) 1 := by
    rw [map_mul, map_one, hy, mk_rep, ← hr, Units.mul_inv]
  have hsub := (mk_eq_mk_iff K v a (x * y) 1).mp hmk
  rw [Subring.coe_mul, OneMemClass.coe_one] at hsub
  have hprod : Valued.v ((x : v.adicCompletion K) * y) = 1 := by
    have hlt : Valued.v ((x : v.adicCompletion K) * y - 1) < Valued.v (1 : v.adicCompletion K) := by
      rw [map_one]
      exact hsub.trans_lt (exp_neg_lt_one ha)
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  rw [map_mul] at hprod
  refine le_antisymm x.2 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (x : v.adicCompletion K) * Valued.v (y : v.adicCompletion K) :=
        hprod.symm
    _ ≤ Valued.v (x : v.adicCompletion K) := mul_le_of_le_one_right' y.2

private def
    coset
    (a : ℕ) (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    Set (v.adicCompletion K) :=
  {u | Valued.v (u - (rep K v a (r : _) : v.adicCompletion K)) ≤ WithZero.exp (-(a : ℤ))}

private theorem mem_coset_iff (a : ℕ)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    (u : v.adicCompletion K) :
    u ∈ coset K v a r ↔ Valued.v (u - (rep K v a (r : _) : v.adicCompletion K)) ≤ WithZero.exp (-(a : ℤ)) :=
  Iff.rfl

private theorem valued_rep {a : ℕ} (ha : 1 ≤ a)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    Valued.v (rep K v a (r : _) : v.adicCompletion K) = 1 :=
  valued_eq_one_of_isUnit_mk K v ha (by rw [mk_rep]; exact r.isUnit)

private theorem valued_eq_one_of_mem_coset {a : ℕ} (ha : 1 ≤ a)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    {u : v.adicCompletion K} (hu : u ∈ coset K v a r) : Valued.v u = 1 := by
  have hlt : Valued.v (u - (rep K v a (r : _) : v.adicCompletion K))
      < Valued.v (rep K v a (r : _) : v.adicCompletion K) := by
    rw [valued_rep K v ha r]
    exact lt_of_le_of_lt ((mem_coset_iff K v a r u).mp hu) (exp_neg_lt_one ha)
  rw [Valuation.map_eq_of_sub_lt _ hlt, valued_rep K v ha r]

private theorem mem_coset_of_mk_eq (a : ℕ)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    {x : v.adicCompletionIntegers K}
    (hx : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x = r) :
    (x : v.adicCompletion K) ∈ coset K v a r := by
  rw [mem_coset_iff]
  exact (mk_eq_mk_iff K v a x (rep K v a (r : _))).mp (by rw [hx, mk_rep])

private theorem exists_mem_coset {a : ℕ} {u : v.adicCompletion K} (hu : Valued.v u = 1) :
    ∃ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
      u ∈ coset K v a r := by
  have huint : u ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, hu]
  set x : v.adicCompletionIntegers K := ⟨u, huint⟩ with hxdef
  have hxunit : IsUnit x := adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  have hmk : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x) :=
    hxunit.map _
  refine ⟨hmk.unit, ?_⟩
  have := mem_coset_of_mk_eq K v a hmk.unit (x := x) hmk.unit_spec.symm
  simpa [hxdef] using this

private theorem setOf_valued_eq_one_eq_iUnion {a : ℕ} (ha : 1 ≤ a) :
    {u : v.adicCompletion K | Valued.v u = 1}
      = ⋃ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
          coset K v a r := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact ⟨fun hu => exists_mem_coset K v hu, fun ⟨r, hr⟩ => valued_eq_one_of_mem_coset K v ha r hr⟩

private theorem pairwise_disjoint_coset (a : ℕ) :
    Pairwise (Function.onFun Disjoint
      fun r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ =>
        coset K v a r) := by
  intro r r' hne
  show Disjoint (coset K v a r) (coset K v a r')
  refine Set.disjoint_left.mpr fun u hu hu' => hne ?_
  rw [mem_coset_iff] at hu hu'
  have hsub : Valued.v ((rep K v a (r : _) : v.adicCompletion K) - rep K v a (r' : _)) ≤ WithZero.exp (-(a : ℤ)) := by
    have h : (rep K v a (r : _) : v.adicCompletion K) - rep K v a (r' : _)
        = (u - rep K v a (r' : _)) - (u - rep K v a (r : _)) := by ring
    rw [h]
    exact Valuation.map_sub_le _ hu' hu
  have hmk := (mk_eq_mk_iff K v a _ _).mpr hsub
  rw [mk_rep, mk_rep] at hmk
  exact Units.ext hmk

private theorem measurableSet_coset [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (a : ℕ)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    MeasurableSet (coset K v a r) :=
  measurableSet_setOf_valued_sub_le K v _ _

private theorem measure_coset [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {a : ℕ} (ha : 1 ≤ a)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    μ (coset K v a r) = μ (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) := by
  rw [image_higherUnitsAt K v ha, coset, measure_setOf_valued_sub_le, measure_setOf_valued_sub_le]

private theorem measure_coset_ne_top [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {a : ℕ} (ha : 1 ≤ a)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    μ (coset K v a r) ≠ ⊤ := by
  have hsub : coset K v a r ⊆ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun u hu =>
    (mem_adicCompletionIntegers (𝓞 K) K v).mpr (valued_eq_one_of_mem_coset K v ha r hu).le
  have hO : μ (integersPositiveCompacts K v : Set (v.adicCompletion K)) < ⊤ :=
    (integersPositiveCompacts K v).isCompact.measure_lt_top
  rw [coe_integersPositiveCompacts] at hO
  exact ne_top_of_le_ne_top hO.ne (measure_mono hsub)

private theorem psi_mul_eq_of_mem_coset (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) {c : v.adicCompletion K} {a : ℕ}
    (hc : Valued.v c ≤ WithZero.exp (n + a))
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    {u : v.adicCompletion K} (hu : u ∈ coset K v a r) :
    ψ (c * u) = ψ (c * (rep K v a (r : _) : v.adicCompletion K)) := by
  have hsplit : c * u = c * (rep K v a (r : _) : v.adicCompletion K) + c * (u - rep K v a (r : _)) := by ring
  have hint : Valued.v (c * (u - (rep K v a (r : _) : v.adicCompletion K))) ≤ WithZero.exp n := by
    rw [map_mul]
    calc Valued.v c * Valued.v (u - (rep K v a (r : _) : v.adicCompletion K))
        ≤ WithZero.exp (n + a) * WithZero.exp (-(a : ℤ)) := mul_le_mul' hc ((mem_coset_iff K v a r u).mp hu)
      _ = WithZero.exp n := by rw [← WithZero.exp_add, add_neg_cancel_right]
  rw [hsplit, AddChar.map_add_eq_mul, hψ _ hint, mul_one]

private theorem charExt_inv_eq_of_mem_coset (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    {u : v.adicCompletion K} (hu : u ∈ coset K v a r) :
    charExt χ⁻¹ u = charExt χ⁻¹ (rep K v a (r : _) : v.adicCompletion K) := by
  have hvu : Valued.v u = 1 := valued_eq_one_of_mem_coset K v ha r hu
  have hvt : Valued.v (rep K v a (r : _) : v.adicCompletion K) = 1 := valued_rep K v ha r
  have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvu]; exact one_ne_zero)
  have ht0 : (rep K v a (r : _) : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hvt]; exact one_ne_zero)
  rw [charExt_of_ne_zero _ hu0, charExt_of_ne_zero _ ht0]
  set w : (v.adicCompletion K)ˣ := Units.mk0 u hu0 * (Units.mk0 _ ht0)⁻¹ with hw
  have hwval : (w : v.adicCompletion K) = u * (rep K v a (r : _) : v.adicCompletion K)⁻¹ := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  have hw1 : Valued.v (w : v.adicCompletion K) = 1 := by
    rw [hwval, map_mul, map_inv₀, hvu, hvt, inv_one, mul_one]
  have hw2 : Valued.v ((w : v.adicCompletion K) - 1) ≤ WithZero.exp (-(a : ℤ)) := by
    have h : (w : v.adicCompletion K) - 1
        = (u - rep K v a (r : _)) * (rep K v a (r : _) : v.adicCompletion K)⁻¹ := by
      rw [hwval, sub_mul, mul_inv_cancel₀ ht0]
    rw [h, map_mul, map_inv₀, hvt, inv_one, mul_one]
    exact (mem_coset_iff K v a r u).mp hu
  have hwmem : w ∈ higherUnitsAt K v a := (mem_higherUnitsAt_iff K v).mpr ⟨hw1, Or.inr hw2⟩
  have hdecomp : Units.mk0 u hu0 = w * Units.mk0 _ ht0 := by
    rw [hw, inv_mul_cancel_right]
  have hχw : χ⁻¹ w = 1 := by
    rw [MonoidHom.inv_apply, hχ w hwmem, inv_one]
  rw [hdecomp, map_mul, hχw, one_mul]

private theorem summand_eq_of_mk_eq (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    {a : ℕ} (ha : 1 ≤ a) (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1) {c : v.adicCompletion K}
    (hc : Valued.v c ≤ WithZero.exp (n + a))
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    {x : v.adicCompletionIntegers K}
    (hx : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x = r) :
    ψ (c * x) * charExt χ⁻¹ x
      = ψ (c * (rep K v a (r : _) : v.adicCompletion K)) * charExt χ⁻¹ (rep K v a (r : _) : v.adicCompletion K) := by
  have hmem := mem_coset_of_mk_eq K v a r hx
  rw [psi_mul_eq_of_mem_coset K v ψ hψ hc r hmem, charExt_inv_eq_of_mem_coset K v χ ha hχ r hmem]

private theorem setIntegral_eq_measure_image_higherUnitsAt_mul_finsum [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    {a : ℕ} (ha : 1 ≤ a) (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1) {c : v.adicCompletion K}
    (hc : Valued.v c ≤ WithZero.exp (n + a))
    [Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)] :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ⁻¹ u ∂μ)
      = ((μ.real (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ)
          * ∑ᶠ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
              ψ (c * (rep K v a (r : _) : v.adicCompletion K))
                * charExt χ⁻¹ (rep K v a (r : _) : v.adicCompletion K) := by
  classical
  haveI : Fintype (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ :=
    Fintype.ofFinite _
  have hconst : ∀ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
      Set.EqOn (fun u => ψ (c * u) * charExt χ⁻¹ u)
        (fun _ => ψ (c * (rep K v a (r : _) : v.adicCompletion K))
          * charExt χ⁻¹ (rep K v a (r : _) : v.adicCompletion K)) (coset K v a r) := by
    intro r u hu
    show ψ (c * u) * charExt χ⁻¹ u
      = ψ (c * (rep K v a (r : _) : v.adicCompletion K)) * charExt χ⁻¹ (rep K v a (r : _) : v.adicCompletion K)
    rw [psi_mul_eq_of_mem_coset K v ψ hψ hc r hu, charExt_inv_eq_of_mem_coset K v χ ha hχ r hu]
  have hint : IntegrableOn (fun u => ψ (c * u) * charExt χ⁻¹ u)
      (⋃ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
        coset K v a r) μ := by
    refine integrableOn_finite_iUnion.mpr fun r => ?_
    exact (integrableOn_congr_fun (hconst r) (measurableSet_coset K v a r)).mpr
      (integrableOn_const (measure_coset_ne_top K v μ ha r))
  rw [setOf_valued_eq_one_eq_iUnion K v ha,
    integral_iUnion (fun r => measurableSet_coset K v a r) (pairwise_disjoint_coset K v a) hint, tsum_fintype,
    finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [setIntegral_congr_fun (measurableSet_coset K v a r) (hconst r), setIntegral_const, Complex.real_smul,
    measureReal_def, measureReal_def, measure_coset K v μ ha r]

private theorem norm_apply_eq_one_of_valued_eq_one (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ}
    (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1)
    [Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)]
    {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have huint : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, hu]
  set x : v.adicCompletionIntegers K := ⟨u, huint⟩ with hxdef
  have hxunit : IsUnit x := adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  have hmk : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x) :=
    hxunit.map _
  haveI : Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ :=
    Finite.of_injective _ Units.val_injective
  set m : ℕ := Nat.card (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ
    with hm
  have hm0 : m ≠ 0 := Nat.card_pos.ne'
  have hpow : hmk.unit ^ m = 1 := pow_card_eq_one'
  have hmkpow : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (x ^ m)
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) 1 := by
    have h := congrArg Units.val hpow
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h
    rw [map_pow, map_one]
    exact h
  have hval : Valued.v (((x ^ m : v.adicCompletionIntegers K) : v.adicCompletion K) - 1)
      ≤ WithZero.exp (-(a : ℤ)) := by
    have h := (mk_eq_mk_iff K v a (x ^ m) 1).mp hmkpow
    simpa using h
  have hmem : u ^ m ∈ higherUnitsAt K v a := by
    refine (mem_higherUnitsAt_iff K v).mpr ⟨?_, Or.inr ?_⟩
    · rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow]
    · rw [Units.val_pow_eq_pow_val]
      simpa [hxdef] using hval
  have hχpow : ((χ u : ℂˣ) : ℂ) ^ m = 1 := by
    have h := hχ _ hmem
    rw [map_pow] at h
    have h' := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
  have hnorm : ‖((χ u : ℂˣ) : ℂ)‖ ^ m = 1 := by
    rw [← norm_pow, hχpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hnorm

end LanglandsTunnell.TateLocal.UnitIntegral

open MeasureTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open scoped Pointwise
open NumberField.AdelicHaar

namespace QuadraticGaussLift

variable {R : Type} [CommRing R]

private def IsIdealPrimitive (ψ : AddChar R ℂ) : Prop :=
  ∀ x : R, x ≠ 0 → ∃ y : R, ψ (x * y) ≠ 1

private def addCharOfLaws {A : Type} [AddMonoid A] (f : A → ℂ) (h0 : f 0 = 1)
    (hadd : ∀ x y : A, f (x + y) = f x * f y) : AddChar A ℂ where
  toFun := f
  map_zero_eq_one' := h0
  map_add_eq_mul' := hadd

private theorem addCharOfLaws_apply {A : Type} [AddMonoid A] (f : A → ℂ) (h0 : f 0 = 1)
    (hadd : ∀ x y : A, f (x + y) = f x * f y) (x : A) : addCharOfLaws f h0 hadd x = f x :=
  rfl

variable [Fintype R] [DecidableEq R]

private noncomputable def gaussSum (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) : ℂ :=
  ∑ u : Rˣ, ((Χ u : ℂˣ) : ℂ) * ψ u

end QuadraticGaussLift

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique hasConductorExponentAt_one_zero localEpsilonAt_of_not_hasConductorExponentAt_zero tateFourier charExt charExt_of_ne_zero localZeta stdRootNumberAt_mul_of_hasConductorExponentAt_zero stdRootNumberAt_one psiLocal_ne_one addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt stdRootNumberAt_ne_zero_of_hasConductorExponentAt forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers selfDualHaarAt_real_image_higherUnitsAt"
namespace UnitIntegral
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def uniformizerInt : v.adicCompletionIntegers K :=
  ⟨uniformizerUnit K v, by
    rw [mem_adicCompletionIntegers, valued_uniformizerUnit, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)⟩

@[scoped simp] private theorem coe_uniformizerInt :
    (uniformizerInt K v : v.adicCompletion K) = (uniformizerUnit K v : (v.adicCompletion K)ˣ) :=
  rfl

private theorem valued_uniformizerInt : Valued.v (uniformizerInt K v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizerUnit K v

private theorem maximalIdeal_eq_span_uniformizerInt :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {uniformizerInt K v} := by
  have hϖ0 : (uniformizerInt K v : v.adicCompletion K) ≠ 0 := by
    rw [coe_uniformizerInt]
    exact Units.ne_zero _
  apply le_antisymm
  · intro x hx
    have hle := le_exp_neg_one_of_lt_one K v ((mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v x).mp hx)
    have hyint : (x : v.adicCompletion K) / uniformizerInt K v ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, valued_uniformizerInt, div_le_one₀ WithZero.exp_pos]
      exact hle
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hyint⟩, Subtype.ext ?_⟩
    show (x : v.adicCompletion K) / uniformizerInt K v * uniformizerInt K v = x
    exact div_mul_cancel₀ _ hϖ0
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v,
      valued_uniformizerInt, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

section AddModel

variable (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}
  (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
  {a : ℕ} (c : v.adicCompletion K) (hc : Valued.v c ≤ WithZero.exp (n + a))

include hψ hc in

private theorem psi_mul_eq_of_mk_eq {x y : v.adicCompletionIntegers K}
    (hxy : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) y) :
    ψ (c * x) = ψ (c * y) := by
  have hval : Valued.v (c * ((x : v.adicCompletion K) - y)) ≤ WithZero.exp n := by
    rw [map_mul]
    calc Valued.v c * Valued.v ((x : v.adicCompletion K) - y)
        ≤ WithZero.exp (n + a) * WithZero.exp (-(a : ℤ)) := mul_le_mul' hc ((mk_eq_mk_iff K v a x y).mp hxy)
      _ = WithZero.exp n := by rw [← WithZero.exp_add, add_neg_cancel_right]
  have hsplit : c * (x : v.adicCompletion K) = c * y + c * ((x : v.adicCompletion K) - y) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, hψ _ hval, mul_one]

include hψ hc in

private theorem psi_mul_rep_zero : ψ (c * (rep K v a 0 : v.adicCompletion K)) = 1 := by
  have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (rep K v a 0)
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) 0 := by
    rw [mk_rep, map_zero]
  rw [psi_mul_eq_of_mk_eq K v ψ hψ c hc h0, ZeroMemClass.coe_zero, mul_zero, AddChar.map_zero_eq_one]

include hψ hc in

private theorem psi_mul_rep_add
    (r s : v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) :
    ψ (c * (rep K v a (r + s) : v.adicCompletion K))
      = ψ (c * (rep K v a r : v.adicCompletion K)) * ψ (c * (rep K v a s : v.adicCompletion K)) := by
  have hrs : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (rep K v a (r + s))
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)
          (rep K v a r + rep K v a s) := by
    rw [mk_rep, map_add, mk_rep, mk_rep]
  rw [psi_mul_eq_of_mk_eq K v ψ hψ c hc hrs, Subring.coe_add, mul_add, AddChar.map_add_eq_mul]

private noncomputable def modelAddChar : AddChar (v.adicCompletionIntegers K ⧸
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) ℂ :=
  QuadraticGaussLift.addCharOfLaws (fun r => ψ (c * (rep K v a r : v.adicCompletion K)))
    (psi_mul_rep_zero K v ψ hψ c hc) (psi_mul_rep_add K v ψ hψ c hc)

private theorem modelAddChar_apply
    (r : v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) :
    modelAddChar K v ψ hψ c hc r = ψ (c * (rep K v a r : v.adicCompletion K)) :=
  rfl

private theorem modelAddChar_mk (x : v.adicCompletionIntegers K) :
    modelAddChar K v ψ hψ c hc (Ideal.Quotient.mk _ x) = ψ (c * x) := by
  rw [modelAddChar_apply]
  exact psi_mul_eq_of_mk_eq K v ψ hψ c hc (mk_rep K v a _)

private theorem modelAddChar_mul (s : v.adicCompletionIntegers K)
    (hcs : Valued.v (c * (s : v.adicCompletion K)) ≤ WithZero.exp (n + a)) :
    modelAddChar K v ψ hψ (c * (s : v.adicCompletion K)) hcs
      = (modelAddChar K v ψ hψ c hc).mulShift (Ideal.Quotient.mk _ s) := by
  refine AddChar.ext _ _ fun r => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [AddChar.mulShift_apply, ← map_mul, modelAddChar_mk, modelAddChar_mk, Subring.coe_mul, mul_assoc]

private theorem exp_one_sub_le_valued_of_not_mem {x : v.adicCompletionIntegers K}
    (hx : x ∉ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) :
    WithZero.exp (1 - (a : ℤ)) ≤ Valued.v (x : v.adicCompletion K) := by
  rw [mem_maximalIdeal_pow_iff, not_le] at hx
  have h0 : Valued.v (x : v.adicCompletion K) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
  rw [← WithZero.exp_log h0] at hx ⊢
  rw [WithZero.exp_lt_exp] at hx
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem isIdealPrimitive_modelAddChar (hceq : Valued.v c = WithZero.exp (n + a))
    (hz : ∃ z : v.adicCompletion K, Valued.v z ≤ WithZero.exp (n + 1) ∧ ψ z ≠ 1) :
    QuadraticGaussLift.IsIdealPrimitive (modelAddChar K v ψ hψ c hc) := by
  intro r hr
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨z, hzv, hzψ⟩ := hz
  have hxmem : x ∉ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a := fun hmem =>
    hr (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hxv := exp_one_sub_le_valued_of_not_mem K v hxmem
  have hx0 : (x : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (ne_of_gt (lt_of_lt_of_le WithZero.exp_pos hxv))
  have hc0 : c ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hceq]; exact WithZero.exp_ne_zero)
  have hpos : 0 < Valued.v (c * (x : v.adicCompletion K)) := (Valuation.pos_iff _).mpr (mul_ne_zero hc0 hx0)

  have hyint : z / (c * x) ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, map_div₀, div_le_one₀ hpos, map_mul, hceq]
    calc Valued.v z ≤ WithZero.exp (n + 1) := hzv
      _ = WithZero.exp (n + a) * WithZero.exp (1 - (a : ℤ)) := by rw [← WithZero.exp_add]; congr 1; ring
      _ ≤ WithZero.exp (n + a) * Valued.v (x : v.adicCompletion K) := mul_le_mul' le_rfl hxv
  refine ⟨Ideal.Quotient.mk _ ⟨_, hyint⟩, ?_⟩
  rw [← map_mul, modelAddChar_mk, Subring.coe_mul]
  show ψ (c * ((x : v.adicCompletion K) * (z / (c * x)))) ≠ 1
  rwa [← mul_assoc, mul_div_cancel₀ _ (mul_ne_zero hc0 hx0)]

end AddModel

section MulModel

variable (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a) (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1)

private noncomputable def
    unitOfValuedEqOne
    (x : v.adicCompletionIntegers K) (hx : Valued.v (x : v.adicCompletion K) = 1) :
    (v.adicCompletion K)ˣ :=
  Units.mk0 (x : v.adicCompletion K) ((Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero))

@[scoped simp] private theorem
    val_unitOfValuedEqOne
    (x : v.adicCompletionIntegers K) (hx : Valued.v (x : v.adicCompletion K) = 1) :
    (unitOfValuedEqOne K v x hx : v.adicCompletion K) = x :=
  rfl

include hχ in

private theorem apply_unitOfValuedEqOne_eq_of_mk_eq {x y : v.adicCompletionIntegers K}
    (hx : Valued.v (x : v.adicCompletion K) = 1) (hy : Valued.v (y : v.adicCompletion K) = 1)
    (hxy : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) y) :
    χ (unitOfValuedEqOne K v x hx) = χ (unitOfValuedEqOne K v y hy) := by
  have hy0 : (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hy]; exact one_ne_zero)
  set w : (v.adicCompletion K)ˣ := unitOfValuedEqOne K v x hx * (unitOfValuedEqOne K v y hy)⁻¹ with hw
  have hwval : (w : v.adicCompletion K) = x * (y : v.adicCompletion K)⁻¹ := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, val_unitOfValuedEqOne, val_unitOfValuedEqOne]
  have hw1 : Valued.v (w : v.adicCompletion K) = 1 := by
    rw [hwval, map_mul, map_inv₀, hx, hy, inv_one, mul_one]
  have hw2 : Valued.v ((w : v.adicCompletion K) - 1) ≤ WithZero.exp (-(a : ℤ)) := by
    have h : (w : v.adicCompletion K) - 1 = ((x : v.adicCompletion K) - y) * (y : v.adicCompletion K)⁻¹ := by
      rw [hwval, sub_mul, mul_inv_cancel₀ hy0]
    rw [h, map_mul, map_inv₀, hy, inv_one, mul_one]
    exact (mk_eq_mk_iff K v a x y).mp hxy
  have hwmem : w ∈ higherUnitsAt K v a := (mem_higherUnitsAt_iff K v).mpr ⟨hw1, Or.inr hw2⟩
  have hdecomp : unitOfValuedEqOne K v x hx = w * unitOfValuedEqOne K v y hy := by
    rw [hw, inv_mul_cancel_right]
  rw [hdecomp, map_mul, hχ w hwmem, one_mul]

include ha in

private theorem valued_rep_units
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    Valued.v (rep K v a (r : _) : v.adicCompletion K) = 1 :=
  valued_eq_one_of_isUnit_mk K v ha (by rw [mk_rep]; exact r.isUnit)

include ha hχ in

private theorem apply_unitOfValuedEqOne_rep_mul
    (r s : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    χ (unitOfValuedEqOne K v (rep K v a ↑(r * s)) (valued_rep_units K v ha (r * s)))
      = χ (unitOfValuedEqOne K v (rep K v a (r : _)) (valued_rep_units K v ha r))
        * χ (unitOfValuedEqOne K v (rep K v a (s : _)) (valued_rep_units K v ha s)) := by
  have hmul : Valued.v ((rep K v a (r : _) * rep K v a (s : _) : v.adicCompletionIntegers K) : v.adicCompletion K)
      = 1 := by
    rw [Subring.coe_mul, map_mul, valued_rep_units K v ha r, valued_rep_units K v ha s, mul_one]
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) (rep K v a ↑(r * s))
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)
          (rep K v a (r : _) * rep K v a (s : _)) := by
    rw [mk_rep,
      map_mul (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)) (rep K v a (r : _))
        (rep K v a (s : _)),
      mk_rep, mk_rep, Units.val_mul]
  rw [apply_unitOfValuedEqOne_eq_of_mk_eq K v χ hχ (valued_rep_units K v ha (r * s)) hmul hmk, ← map_mul]
  exact congrArg χ (Units.ext (by
    rw [val_unitOfValuedEqOne, Units.val_mul, val_unitOfValuedEqOne, val_unitOfValuedEqOne, Subring.coe_mul]))

private noncomputable def modelMulChar :
    (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun r => χ (unitOfValuedEqOne K v (rep K v a (r : _)) (valued_rep_units K v ha r)))
    (apply_unitOfValuedEqOne_rep_mul K v χ ha hχ)

private theorem modelMulChar_apply
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ) :
    modelMulChar K v χ ha hχ r = χ (unitOfValuedEqOne K v (rep K v a (r : _)) (valued_rep_units K v ha r)) :=
  rfl

private theorem modelMulChar_apply_eq {x : v.adicCompletionIntegers K} (hx : Valued.v (x : v.adicCompletion K) = 1)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    (hxr : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x = r) :
    modelMulChar K v χ ha hχ r = χ (unitOfValuedEqOne K v x hx) := by
  rw [modelMulChar_apply]
  exact apply_unitOfValuedEqOne_eq_of_mk_eq K v χ hχ _ hx (by rw [mk_rep, hxr])

private theorem charExt_eq_modelMulChar {x : v.adicCompletionIntegers K} (hx : Valued.v (x : v.adicCompletion K) = 1)
    (r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ)
    (hxr : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x = r) :
    charExt χ (x : v.adicCompletion K) = ((modelMulChar K v χ ha hχ r : ℂˣ) : ℂ) := by
  have hx0 : (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
  rw [charExt_of_ne_zero _ hx0, modelMulChar_apply_eq K v χ ha hχ hx r hxr]
  rfl

private theorem exists_sub_one_mem_and_modelMulChar_ne_one (hmin : ∃ u ∈ higherUnitsAt K v (a - 1), χ u ≠ 1) :
    ∃ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
      (r : v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) - 1 ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (a - 1)).map
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)) ∧
        modelMulChar K v χ ha hχ r ≠ 1 := by
  obtain ⟨u, hu, hχu⟩ := hmin
  obtain ⟨hu1, hball⟩ := (mem_higherUnitsAt_iff K v).mp hu
  have huint : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, hu1]
  set x : v.adicCompletionIntegers K := ⟨u, huint⟩ with hxdef
  have hx1 : Valued.v (x : v.adicCompletion K) = 1 := hu1
  have hxunit : IsUnit x := adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hx1
  have hmkunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a) x) :=
    hxunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a))
  refine ⟨hmkunit.unit, ?_, ?_⟩
  ·
    have hsub : x - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (a - 1) := by
      rcases hball with h0 | hle
      · rw [h0, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · rw [mem_maximalIdeal_pow_iff, AddSubgroupClass.coe_sub, OneMemClass.coe_one]
        exact hle
    rw [IsUnit.unit_spec hmkunit,
      ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)),
      ← map_sub (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)) x 1]
    exact Ideal.mem_map_of_mem _ hsub
  · intro h1
    apply hχu
    have happ := modelMulChar_apply_eq K v χ ha hχ hx1 hmkunit.unit (IsUnit.unit_spec hmkunit).symm
    rw [h1] at happ
    have hux : unitOfValuedEqOne K v x hx1 = u := Units.ext rfl
    have h := happ.symm
    rwa [hux] at h

end MulModel

section Bridge

variable (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}
  (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
  (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a) (hχ : ∀ w ∈ higherUnitsAt K v a, χ w = 1)
  (c : v.adicCompletion K) (hc : Valued.v c ≤ WithZero.exp (n + a))

private theorem finsum_eq_gaussSum
    [Fintype (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)]
    [DecidableEq (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)] :
    (∑ᶠ r : (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)ˣ,
        ψ (c * (rep K v a (r : _) : v.adicCompletion K)) * charExt χ (rep K v a (r : _) : v.adicCompletion K))
      = QuadraticGaussLift.gaussSum (modelMulChar K v χ ha hχ) (modelAddChar K v ψ hψ c hc) := by
  rw [finsum_eq_sum_of_fintype, QuadraticGaussLift.gaussSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [charExt_eq_modelMulChar K v χ ha hχ (valued_rep_units K v ha r) r (mk_rep K v a _)]
  exact mul_comm _ _

end Bridge

end LanglandsTunnell.TateLocal.UnitIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell"

namespace QuadraticGaussLift

open Finset

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R]

private theorem gaussSum_transport {S : Type} [CommRing S] [Fintype S] [DecidableEq S] (e : R ≃+* S) (Χ : Rˣ →* ℂˣ)
    (ψ : AddChar R ℂ) :
    gaussSum (Χ.comp (Units.map (e.symm : S ≃+* R).toMonoidHom))
        (ψ.compAddMonoidHom (e.symm : S ≃+* R).toAddMonoidHom)
      = gaussSum Χ ψ := by
  unfold QuadraticGaussLift.gaussSum
  refine Fintype.sum_equiv (Units.mapEquiv (e.symm : S ≃+* R).toMulEquiv).toEquiv _ _ fun u => ?_
  have hu : Units.map (e.symm : S ≃+* R).toMonoidHom u
      = (Units.mapEquiv (e.symm : S ≃+* R).toMulEquiv).toEquiv u :=
    Units.ext rfl
  rw [MonoidHom.coe_comp, Function.comp_apply, AddChar.compAddMonoidHom_apply, hu]
  rfl

end QuadraticGaussLift
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

namespace QuadraticGaussLift

open Finset

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R]

private theorem apply_mul_gaussSum_mulShift (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t : Rˣ) :
    ((Χ t : ℂˣ) : ℂ) * gaussSum Χ (ψ.mulShift (t : R)) = gaussSum Χ ψ := by
  simp only [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← Units.val_mul, ← map_mul]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective t) _ _ fun _ => rfl

private theorem gaussSum_mulShift_unit (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t : Rˣ) :
    gaussSum Χ (ψ.mulShift (t : R)) = (((Χ t)⁻¹ : ℂˣ) : ℂ) * gaussSum Χ ψ := by
  rw [← apply_mul_gaussSum_mulShift Χ ψ t, ← mul_assoc, Units.inv_mul, one_mul]

private theorem gaussSum_mulShift_unit_pow (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t : Rˣ) (m : ℕ) :
    gaussSum Χ (ψ.mulShift ((t ^ m : Rˣ) : R)) = (((Χ t)⁻¹ : ℂˣ) : ℂ) ^ m * gaussSum Χ ψ := by
  rw [gaussSum_mulShift_unit, map_pow, ← inv_pow, Units.val_pow_eq_pow_val]

private theorem gaussSum_mulShift_unit_inv (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t : Rˣ) :
    gaussSum Χ (ψ.mulShift ((t⁻¹ : Rˣ) : R)) = ((Χ t : ℂˣ) : ℂ) * gaussSum Χ ψ := by
  rw [gaussSum_mulShift_unit, map_inv, inv_inv]

private theorem gaussSum_mulShift_unit_pow_inv (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t : Rˣ) (m : ℕ) :
    gaussSum Χ (ψ.mulShift (((t ^ m)⁻¹ : Rˣ) : R)) = ((Χ t : ℂˣ) : ℂ) ^ m * gaussSum Χ ψ := by
  rw [gaussSum_mulShift_unit_inv, map_pow, Units.val_pow_eq_pow_val]

private theorem gaussSum_mulShift_mul_pow_inv (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (t u₀ : Rˣ) (m : ℕ) :
    gaussSum Χ (ψ.mulShift ((((t * u₀) ^ m)⁻¹ : Rˣ) : R)) =
      ((Χ u₀ : ℂˣ) : ℂ) ^ m * gaussSum Χ (ψ.mulShift (((t ^ m)⁻¹ : Rˣ) : R)) := by
  rw [gaussSum_mulShift_unit_pow_inv, gaussSum_mulShift_unit_pow_inv, map_mul, Units.val_mul, mul_pow, mul_assoc,
    mul_left_comm]

end QuadraticGaussLift
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique hasConductorExponentAt_one_zero localEpsilonAt_of_not_hasConductorExponentAt_zero tateFourier charExt charExt_of_ne_zero localZeta stdRootNumberAt_mul_of_hasConductorExponentAt_zero stdRootNumberAt_one psiLocal_ne_one addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt stdRootNumberAt_ne_zero_of_hasConductorExponentAt forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers selfDualHaarAt_real_image_higherUnitsAt"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem one_lt_absNorm_asIdeal : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem norm_inv_uniformizer_mul_absNorm_cpow_lt_one (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hq : 1 < Ideal.absNorm v.asIdeal := one_lt_absNorm_asIdeal K v
  rw [norm_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul,
    Complex.norm_natCast_cpow_of_pos (by omega)]
  have hre : (-(1 - (1 / 2 : ℂ))).re = -(1 / 2 : ℝ) := by norm_num
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by norm_num)

private theorem stdRootNumberAt_eq_of_hasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ)
    (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    letI := localBorel K v
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              psiLocal K v
                  (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
                      v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  have hnot0 : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
    have := hasConductorExponentAt_unique K v hχ h0
    omega
  have hnum := localZeta_tateFourier_stdTestFunAt K v χ a ha hχ (1 / 2)
    (norm_inv_uniformizer_mul_absNorm_cpow_lt_one K v χ hu)
  have hden := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v χ a ha hχ (1 / 2)
  have hne := stdRootNumberAt_ne_zero_of_hasConductorExponentAt K v χ a ha hχ hu
  have hform : stdRootNumberAt K v χ
      = localZeta (selfDualHaarAt K v)
            (tateFourier (psiLocal K v) (selfDualHaarAt K v) (stdTestFunAt K v χ)) χ⁻¹ (1 - 1 / 2)
          / localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ (1 / 2) := by
    rw [stdRootNumberAt, stdEpsilonAt]
    rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v (selfDualHaarAt K v) (psiLocal K v)
      (stdTestFunAt K v χ) hnot0 (1 / 2)]
    rfl
  rw [hform, hnum, hden]
  have hvol : (((selfDualHaarAt K v).real
      (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    apply hne
    rw [hform, hnum, hden, h0, div_zero]
  rw [div_eq_iff hvol, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  ring

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

open MeasureTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.StandardAddChar
open scoped NNReal

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdTestFunAt stdEpsilonAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_zero_iff hasConductorExponentAt_unique hasConductorExponentAt_one_zero localEpsilonAt_of_not_hasConductorExponentAt_zero tateFourier charExt charExt_of_ne_zero localZeta stdRootNumberAt_mul_of_hasConductorExponentAt_zero stdRootNumberAt_one psiLocal_ne_one addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one localZeta_tateFourier_stdTestFunAt localZeta_stdTestFunAt_eq_real_image_higherUnitsAt stdRootNumberAt_ne_zero_of_hasConductorExponentAt forall_eq_one_and_exists_ne_one_of_addCharLevel psiLocal_eq_one_of_mem_integers selfDualHaarAt_real_image_higherUnitsAt"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem isAddHaarMeasure_selfDualHaarAt :
    @Measure.IsAddHaarMeasure (v.adicCompletion K) _ _ (localBorel K v) (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero h0
  have hc : (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) ≠ 0 :=
    (NNReal.rpow_pos hq).ne'
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ hc

private theorem valued_uniformizerUnit_zpow (k : ℤ) :
    Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]

private theorem valued_uniformizerUnit_zpow_neg_le (n : ℤ) (a : ℕ) :
    Valued.v ((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      ≤ WithZero.exp (n + a) := by
  rw [valued_uniformizerUnit_zpow, neg_neg]

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

namespace QuadraticLocalConstants

section NormalForm

p2m_open "NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def c (a : ℕ) : v.adicCompletion K :=
  ((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K)

private theorem valued_c (a : ℕ) : Valued.v (c K v a) ≤ WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ) :=
  valued_uniformizerUnit_zpow_neg_le K v (addCharLevel (psiLocal K v)) a

private theorem hψlevel :
    ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v)) → psiLocal K v x = 1 :=
  (forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v)
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (by rw [WithZero.exp_zero] at hx; exact hx))⟩
    (psiLocal_ne_one K v)).1

private noncomputable def Cst (a : ℕ) : ℝ :=
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ)) ^ (1 / 2 : ℝ)
    * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(a : ℤ))
        * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2))

private theorem inv_apply_eq_one_of_hasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : ∀ u ∈ higherUnitsAt K v a, χ⁻¹ u = 1 := fun u hu => by
  rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]

private theorem stdRootNumberAt_eq_const_mul_gaussSum (χ : (v.adicCompletion K)ˣ →* ℂˣ) {a : ℕ} (ha1 : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1)
    [Fintype (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)]
    [DecidableEq (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ a)] :
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) * (Cst K v a : ℂ)
          * QuadraticGaussLift.gaussSum
              (UnitIntegral.modelMulChar K v χ⁻¹ ha1 (inv_apply_eq_one_of_hasConductorExponentAt K v χ hχ))
              (UnitIntegral.modelAddChar K v (psiLocal K v) (hψlevel K v) (c K v a) (valued_c K v a)) := by
  letI := localBorel K v
  haveI := borelSpace_localBorel K v
  haveI := isAddHaarMeasure_selfDualHaarAt K v
  have hB2 := stdRootNumberAt_eq_of_hasConductorExponentAt K v χ a ha1 hχ hu
  have hB4 := UnitIntegral.setIntegral_eq_measure_image_higherUnitsAt_mul_finsum K v (selfDualHaarAt K v)
    (psiLocal K v) (hψlevel K v) χ ha1 hχ.1 (valued_c K v a)
  have hM3 := UnitIntegral.finsum_eq_gaussSum K v (psiLocal K v) (hψlevel K v) χ⁻¹ ha1
    (inv_apply_eq_one_of_hasConductorExponentAt K v χ hχ) (c K v a) (valued_c K v a)
  have hvol := selfDualHaarAt_real_image_higherUnitsAt K v a ha1
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) :=
    zpow_nonneg (Nat.cast_nonneg _) _
  have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  simp only [c] at hB4 hM3 ⊢
  rw [hB2, hB4, hM3, hvol]
  simp only [Cst, Complex.ofReal_mul]
  rw [Complex.ofReal_cpow hq0, h12]
  ring

end NormalForm
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

end QuadraticLocalConstants
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

namespace QuadraticLocalConstants

section ScalingElement

p2m_open "NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_c_eq (a : ℕ) : Valued.v (c K v a) = WithZero.exp (addCharLevel (psiLocal K v) + a : ℤ) := by
  simp only [c]
  rw [LanglandsTunnell.TateLocal.valued_uniformizerUnit_zpow K v, neg_neg]

private theorem valued_zpow_eq_one (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) (k : ℤ) :
    Valued.v ((u ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, one_zpow]

end ScalingElement
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

section ConstantCongruence

p2m_open "NumberField NumberField.StandardAddChar IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"

variable {K₁ : Type} [Field K₁] [NumberField K₁] {v₁ : HeightOneSpectrum (𝓞 K₁)}
  {K₂ : Type} [Field K₂] [NumberField K₂] {v₂ : HeightOneSpectrum (𝓞 K₂)}

private theorem Cst_eq_of_absNorm_eq_of_level_eq (hq : (Ideal.absNorm v₂.asIdeal : ℝ) = Ideal.absNorm v₁.asIdeal)
    (hn : addCharLevel (psiLocal K₂ v₂) = addCharLevel (psiLocal K₁ v₁)) (a : ℕ) : Cst K₂ v₂ a = Cst K₁ v₁ a := by
  unfold Cst
  rw [hq, hn]

private theorem Cst_eq_sq_of_absNorm_eq_sq_of_level_eq
    (hq : (Ideal.absNorm v₂.asIdeal : ℝ) = (Ideal.absNorm v₁.asIdeal : ℝ) ^ 2)
    (hn : addCharLevel (psiLocal K₂ v₂) = addCharLevel (psiLocal K₁ v₁)) (a : ℕ) :
    Cst K₂ v₂ a = Cst K₁ v₁ a ^ 2 := by
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v₁.asIdeal : ℝ) := Nat.cast_nonneg _
  have hz0 : (0 : ℝ) ≤ (Ideal.absNorm v₁.asIdeal : ℝ) ^ (addCharLevel (psiLocal K₁ v₁) + a : ℤ) :=
    zpow_nonneg hq0 _
  unfold Cst
  rw [hq, hn, sq (Ideal.absNorm v₁.asIdeal : ℝ), mul_zpow, mul_zpow, Real.mul_rpow hq0 hq0, Real.mul_rpow hz0 hz0]
  ring

end ConstantCongruence
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

section TwoFields

p2m_open "NumberField NumberField.AdelicLevel NumberField.StandardAddChar IsDedekindDomain LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal"

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

private theorem moduleFinite_ringOfIntegers : Module.Finite (𝓞 E) (𝓞 M) :=
  haveI : IsScalarTower ℤ (𝓞 E) (𝓞 M) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) (𝓞 M)

private theorem absNorm_extension_eq_sq (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 2) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
  haveI := moduleFinite_ringOfIntegers E M
  have hunder : Ideal.under (𝓞 E) w.1.asIdeal = v.asIdeal := congrArg HeightOneSpectrum.asIdeal w.2
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨hunder.symm⟩
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hf]

private theorem Cst_upstairs_eq_sq (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 2) {a : ℕ} : Cst M w.1 a = Cst E v a ^ 2 :=
  Cst_eq_sq_of_absNorm_eq_sq_of_level_eq (by rw [absNorm_extension_eq_sq E M v w hf, Nat.cast_pow])
    (addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w he) a

private theorem c_upstairs_eq (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (u₀ : (w.1.adicCompletion M)ˣ)
    (hu₀ : uniformizerUnit M w.1
      = Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
            v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v) * u₀)
    {a : ℕ} :
    c M w.1 a
      = algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (c E v a)
          * ((u₀ ^ (-(addCharLevel (psiLocal E v) + a : ℤ)) : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M) := by
  have hι : ((Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v) : (w.1.adicCompletion M)ˣ) :
          w.1.adicCompletion M)
      = algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (uniformizerUnit E v : v.adicCompletion E) := rfl
  simp only [c]
  rw [addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w he, hu₀, mul_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, hι, map_zpow₀]

private theorem zpow_comp_norm_uniformizerUnit (μ : (v.adicCompletion E)ˣ →* ℂˣ) (u₀ : (w.1.adicCompletion M)ˣ)
    (hu₀ : uniformizerUnit M w.1
      = Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
            v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v) * u₀)
    (hN : (μ.comp (Units.map (Algebra.norm (v.adicCompletion E) :
              w.1.adicCompletion M →* v.adicCompletion E)))
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
                v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v))
          = μ (uniformizerUnit E v) ^ 2)
    (m : ℤ) :
    ((μ.comp (Units.map (Algebra.norm (v.adicCompletion E) : w.1.adicCompletion M →* v.adicCompletion E)))
          (uniformizerUnit M w.1) : ℂ) ^ m
      = ((μ (uniformizerUnit E v) : ℂ) ^ m) ^ 2
          * ((μ.comp (Units.map (Algebra.norm (v.adicCompletion E) :
                w.1.adicCompletion M →* v.adicCompletion E))) u₀ : ℂ) ^ m := by
  rw [hu₀, map_mul, hN, Units.val_mul, Units.val_pow_eq_pow_val, sq ((μ (uniformizerUnit E v) : ℂˣ) : ℂ), mul_zpow,
    mul_zpow]
  ring

private theorem norm_comp_norm_uniformizerUnit_eq_one (μ : (v.adicCompletion E)ˣ →* ℂˣ) (u₀ : (w.1.adicCompletion M)ˣ)
    (hu₀ : uniformizerUnit M w.1
      = Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
            v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v) * u₀)
    (hN : (μ.comp (Units.map (Algebra.norm (v.adicCompletion E) :
              w.1.adicCompletion M →* v.adicCompletion E)))
            (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
                v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v))
          = μ (uniformizerUnit E v) ^ 2)
    (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1)
    (hu₀1 : ‖((μ.comp (Units.map (Algebra.norm (v.adicCompletion E) :
        w.1.adicCompletion M →* v.adicCompletion E))) u₀ : ℂ)‖ = 1) :
    ‖((μ.comp (Units.map (Algebra.norm (v.adicCompletion E) : w.1.adicCompletion M →* v.adicCompletion E)))
        (uniformizerUnit M w.1) : ℂ)‖ = 1 := by
  have h := zpow_comp_norm_uniformizerUnit E M v w μ u₀ hu₀ hN 1
  simp only [zpow_one] at h
  rw [h, norm_mul, norm_pow, hμ, one_pow, one_mul, hu₀1]

end TwoFields
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

end QuadraticLocalConstants
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

namespace DegreeOneCompletion

open LanglandsTunnell.TateLocal.UnitIntegral QuadraticGaussLift

private theorem modelAddChar_congr {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (u.adicCompletion K) ℂ) {n₁ n₂ : ℤ}
    (hψ₁ : ∀ x : u.adicCompletion K, Valued.v x ≤ WithZero.exp n₁ → ψ x = 1)
    (hψ₂ : ∀ x : u.adicCompletion K, Valued.v x ≤ WithZero.exp n₂ → ψ x = 1) {a : ℕ}
    {c₁ c₂ : u.adicCompletion K} (hc₁ : Valued.v c₁ ≤ WithZero.exp (n₁ + a))
    (hc₂ : Valued.v c₂ ≤ WithZero.exp (n₂ + a)) (h : c₁ = c₂) :
    modelAddChar K u ψ hψ₁ c₁ hc₁ = modelAddChar K u ψ hψ₂ c₂ hc₂ := by
  subst h
  ext r
  rfl

private theorem gaussSum_eq_of_forall {R S : Type} [CommRing R] [Fintype R] [DecidableEq R] [CommRing S] [Fintype S]
    [DecidableEq S] (e : R ≃+* S) (Χ : Rˣ →* ℂˣ) (ψ : AddChar R ℂ) (Χ' : Sˣ →* ℂˣ) (ψ' : AddChar S ℂ)
    (hΧ : ∀ u : Sˣ, Χ' u = Χ (Units.map (e.symm : S ≃+* R).toMonoidHom u))
    (hψ : ∀ s : S, ψ' s = ψ (e.symm s)) :
    gaussSum Χ' ψ' = gaussSum Χ ψ := by
  rw [← gaussSum_transport e Χ ψ]
  unfold QuadraticGaussLift.gaussSum
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hΧ u, hψ, MonoidHom.comp_apply, AddChar.compAddMonoidHom_apply]
  rfl

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
  (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 1)

include he hf

private noncomputable def integersEquiv : v.adicCompletionIntegers E ≃+* w.1.adicCompletionIntegers M :=
  RingEquiv.ofBijective (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M))
    (integers_algebraMap_bijective v w he hf)

private theorem integersEquiv_apply (x : v.adicCompletionIntegers E) :
    integersEquiv v w he hf x = algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x := rfl

private theorem maximalIdeal_pow_eq_map (a : ℕ) :
    IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a =
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a).map
        (integersEquiv v w he hf : v.adicCompletionIntegers E →+* w.1.adicCompletionIntegers M) := by
  rw [Ideal.map_comap_of_equiv]
  ext y
  rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff, mem_maximalIdeal_pow_iff]
  obtain ⟨x, rfl⟩ := (integersEquiv v w he hf).surjective y
  rw [RingEquiv.symm_apply_apply, integersEquiv_apply, coe_integers_algebraMap v w he hf,
    valued_algebraMap v w he hf]

private noncomputable def modelEquiv (a : ℕ) :
    (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a) ≃+*
      (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a) :=
  Ideal.quotientEquiv _ _ (integersEquiv v w he hf) (maximalIdeal_pow_eq_map v w he hf a)

private theorem modelEquiv_mk (a : ℕ) (x : v.adicCompletionIntegers E) :
    modelEquiv v w he hf a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

private theorem unitOfValuedEqOne_map (x : v.adicCompletionIntegers E) (hx : Valued.v (x : v.adicCompletion E) = 1)
    (hx' : Valued.v ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x :
        w.1.adicCompletionIntegers M) : w.1.adicCompletion M) = 1) :
    unitOfValuedEqOne M w.1 (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x) hx' =
      Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) (unitOfValuedEqOne E v x hx) :=
  Units.ext rfl

private theorem modelMulChar_comp_norm_inv_apply (μ : (v.adicCompletion E)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hμ : ∀ u ∈ higherUnitsAt E v a, μ⁻¹ u = 1)
    (hμM : ∀ u ∈ higherUnitsAt M w.1 a, (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))⁻¹ u = 1)
    (s : (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)ˣ) :
    modelMulChar M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))⁻¹ ha hμM s =
      modelMulChar E v μ⁻¹ ha hμ
        (Units.map ((modelEquiv v w he hf a).symm : _ ≃+* _).toMonoidHom s) := by
  set r := Units.map ((modelEquiv v w he hf a).symm : _ ≃+* _).toMonoidHom s with hr
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (r : v.adicCompletionIntegers E ⧸
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)
  have hxv : Valued.v (x : v.adicCompletion E) = 1 :=
    valued_eq_one_of_isUnit_mk E v ha (by rw [hx]; exact r.isUnit)
  have hxv' : Valued.v ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x :
      w.1.adicCompletionIntegers M) : w.1.adicCompletion M) = 1 := by
    rw [coe_integers_algebraMap v w he hf, valued_algebraMap v w he hf, hxv]
  have hs : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)
      (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x) = s := by
    rw [← modelEquiv_mk v w he hf a, hx]
    show modelEquiv v w he hf a ((modelEquiv v w he hf a).symm s) = s
    exact (modelEquiv v w he hf a).apply_symm_apply s
  rw [modelMulChar_apply_eq M w.1 _ ha hμM hxv' s hs, modelMulChar_apply_eq E v μ⁻¹ ha hμ hxv r hx,
    unitOfValuedEqOne_map v w he hf x hxv hxv', MonoidHom.inv_apply, MonoidHom.inv_apply,
    comp_norm_map_algebraMap v w he hf]

private theorem modelAddChar_psiLocal_map_apply {n : ℤ}
    (hψE : ∀ x : v.adicCompletion E, Valued.v x ≤ WithZero.exp n → psiLocal E v x = 1)
    (hψM : ∀ x : w.1.adicCompletion M, Valued.v x ≤ WithZero.exp n → psiLocal M w.1 x = 1)
    {a : ℕ} (c : v.adicCompletion E) (hc : Valued.v c ≤ WithZero.exp (n + a))
    (hc' : Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) ≤ WithZero.exp (n + a))
    (s : w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a) :
    modelAddChar M w.1 (psiLocal M w.1) hψM (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) hc' s =
      modelAddChar E v (psiLocal E v) hψE c hc ((modelEquiv v w he hf a).symm s) := by

  have hy := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy⟩ := hy
  have hx := (integersEquiv v w he hf).surjective y
  obtain ⟨x, hx⟩ := hx
  have hs : s = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)
      (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x) := by
    rw [← hy, ← hx, integersEquiv_apply]
  have hsym : (modelEquiv v w he hf a).symm s =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a) x := by
    rw [hs]
    exact (modelEquiv v w he hf a).symm_apply_eq.mpr (modelEquiv_mk v w he hf a x).symm
  have hval : psiLocal M w.1 (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c *
        ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x : w.1.adicCompletionIntegers M) :
          w.1.adicCompletion M)) =
      psiLocal E v (c * (x : v.adicCompletion E)) := by
    rw [coe_integers_algebraMap v w he hf x,
      ← map_mul (algebraMap (v.adicCompletion E) (w.1.adicCompletion M)) c (x : v.adicCompletion E),
      psiLocal_eq_psiLocal_trace E M v w, trace_algebraMap v w he hf]
  calc modelAddChar M w.1 (psiLocal M w.1) hψM (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) hc' s
      = modelAddChar M w.1 (psiLocal M w.1) hψM (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) hc'
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)
            (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x)) :=
        congrArg (fun z => modelAddChar M w.1 (psiLocal M w.1) hψM
          (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) hc' z) hs
    _ = psiLocal M w.1 (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c *
          ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x :
            w.1.adicCompletionIntegers M) : w.1.adicCompletion M)) :=
        modelAddChar_mk M w.1 (psiLocal M w.1) hψM _ hc' _
    _ = psiLocal E v (c * (x : v.adicCompletion E)) := hval
    _ = modelAddChar E v (psiLocal E v) hψE c hc
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a) x) :=
        (modelAddChar_mk E v (psiLocal E v) hψE c hc x).symm
    _ = modelAddChar E v (psiLocal E v) hψE c hc ((modelEquiv v w he hf a).symm s) :=
        congrArg (fun z => modelAddChar E v (psiLocal E v) hψE c hc z) hsym.symm

private theorem gaussSum_model_map (μ : (v.adicCompletion E)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hμ : ∀ u ∈ higherUnitsAt E v a, μ⁻¹ u = 1)
    (hμM : ∀ u ∈ higherUnitsAt M w.1 a, (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))⁻¹ u = 1)
    {n : ℤ} (hψE : ∀ x : v.adicCompletion E, Valued.v x ≤ WithZero.exp n → psiLocal E v x = 1)
    (hψM : ∀ x : w.1.adicCompletion M, Valued.v x ≤ WithZero.exp n → psiLocal M w.1 x = 1)
    (c : v.adicCompletion E) (hc : Valued.v c ≤ WithZero.exp (n + a))
    (hc' : Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) ≤ WithZero.exp (n + a))
    [Fintype (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)]
    [DecidableEq (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)]
    [Fintype (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)]
    [DecidableEq (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)] :
    gaussSum (modelMulChar M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))⁻¹ ha hμM)
        (modelAddChar M w.1 (psiLocal M w.1) hψM (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) hc') =
      gaussSum (modelMulChar E v μ⁻¹ ha hμ) (modelAddChar E v (psiLocal E v) hψE c hc) := by
  exact gaussSum_eq_of_forall (modelEquiv v w he hf a) _ _ _ _
    (modelMulChar_comp_norm_inv_apply v w he hf μ ha hμ hμM)
    (modelAddChar_psiLocal_map_apply v w he hf hψE hψM c hc hc')

end DegreeOneCompletion
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

namespace DegreeOneCompletion

open LanglandsTunnell.TateLocal.UnitIntegral QuadraticGaussLift QuadraticLocalConstants

private theorem finite_model {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)) (a : ℕ) :
    Finite (u.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (u.adicCompletionIntegers K) ^ a) := by
  haveI : Finite (u.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (u.adicCompletionIntegers K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (u.adicCompletionIntegers K)))
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) a

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
  (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 1)

private theorem absNorm_asIdeal_eq (hf₁ : v.asIdeal.inertiaDeg' w.1.asIdeal = 1) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal := by
  haveI := moduleFinite_ringOfIntegers E M
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hf₁, pow_one]

include he hf

private theorem exists_uniformizer_factor :
    ∃ u₀ : (v.adicCompletion E)ˣ, Valued.v (u₀ : v.adicCompletion E) = 1 ∧
      Valued.v ((uniformizerUnit E v * u₀ : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧
      Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
        v.adicCompletion E →* w.1.adicCompletion M) (uniformizerUnit E v * u₀) =
        uniformizerUnit M w.1 := by
  obtain ⟨x₀, hx₀⟩ := units_map_surjective v w he hf (uniformizerUnit M w.1)
  have hx₀v : Valued.v (x₀ : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    have h : algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (x₀ : v.adicCompletion E) =
        (uniformizerUnit M w.1 : w.1.adicCompletion M) := by
      rw [← hx₀]; rfl
    rw [← valued_algebraMap v w he hf, h, valued_uniformizerUnit]
  refine ⟨(uniformizerUnit E v)⁻¹ * x₀, ?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit, hx₀v,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · rw [mul_inv_cancel_left, hx₀v]
  · rw [mul_inv_cancel_left, hx₀]

private theorem gaussSum_upstairs_eq_transport (μ : (v.adicCompletion E)ˣ →* ℂˣ) {a : ℕ} (ha1 : 1 ≤ a)
    (hμa : HasConductorExponentAt E v μ a)
    (hμM : HasConductorExponentAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a)
    (x₀ : (v.adicCompletion E)ˣ)
    (hx₀ : Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) :
      v.adicCompletion E →* w.1.adicCompletion M) x₀ = uniformizerUnit M w.1)
    (hc' : Valued.v ((x₀ ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)
      ≤ WithZero.exp (addCharLevel (psiLocal M w.1) + a))
    (hψE' : ∀ x : v.adicCompletion E, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal M w.1)) → psiLocal E v x = 1)
    [Fintype (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)]
    [DecidableEq (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)]
    [Fintype (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)]
    [DecidableEq (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a)] :
    gaussSum (modelMulChar M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E))))⁻¹ ha1
          (inv_apply_eq_one_of_hasConductorExponentAt M w.1 _ hμM))
        (modelAddChar M w.1 (psiLocal M w.1) (hψlevel M w.1) (c M w.1 a) (valued_c M w.1 a)) =
      gaussSum (modelMulChar E v μ⁻¹ ha1 (inv_apply_eq_one_of_hasConductorExponentAt E v μ hμa))
        (modelAddChar E v (psiLocal E v) hψE'
          ((x₀ ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) hc') := by
  have hcM : c M w.1 a = algebraMap (v.adicCompletion E) (w.1.adicCompletion M)
      ((x₀ ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    show ((uniformizerUnit M w.1 ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) : (w.1.adicCompletion M)ˣ) :
      w.1.adicCompletion M) = _
    rw [← hx₀, ← map_zpow, Units.coe_map]
    rfl
  have hcι : Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M)
      ((x₀ ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E))
      ≤ WithZero.exp (addCharLevel (psiLocal M w.1) + a) := by
    rw [valued_algebraMap v w he hf]; exact hc'
  rw [modelAddChar_congr w.1 (psiLocal M w.1) (hψlevel M w.1) (hψlevel M w.1) (valued_c M w.1 a) hcι hcM]
  exact gaussSum_model_map v w he hf μ ha1 (inv_apply_eq_one_of_hasConductorExponentAt E v μ hμa) _ hψE'
    (hψlevel M w.1) _ hc' hcι

private theorem gaussSum_shift_eq (μ : (v.adicCompletion E)ˣ →* ℂˣ) {a : ℕ} (ha1 : 1 ≤ a)
    (hμa : HasConductorExponentAt E v μ a) (u₀ : (v.adicCompletion E)ˣ)
    (hu₀v : Valued.v (u₀ : v.adicCompletion E) = 1) {n : ℤ} (hn : n = addCharLevel (psiLocal E v))
    (hψE' : ∀ x : v.adicCompletion E, Valued.v x ≤ WithZero.exp n → psiLocal E v x = 1)
    (hc' : Valued.v (((uniformizerUnit E v * u₀) ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)
      ≤ WithZero.exp (n + a))
    [Fintype (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)]
    [DecidableEq (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)] :
    gaussSum (modelMulChar E v μ⁻¹ ha1 (inv_apply_eq_one_of_hasConductorExponentAt E v μ hμa))
        (modelAddChar E v (psiLocal E v) hψE'
          (((uniformizerUnit E v * u₀) ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) hc') =
      ((μ u₀ ^ (-(n + a : ℤ)) : ℂˣ) : ℂ) *
        gaussSum (modelMulChar E v μ⁻¹ ha1 (inv_apply_eq_one_of_hasConductorExponentAt E v μ hμa))
          (modelAddChar E v (psiLocal E v) (hψlevel E v) (c E v a) (valued_c E v a)) := by

  set s : v.adicCompletionIntegers E :=
    ⟨((u₀ ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
      rw [mem_adicCompletionIntegers, Units.val_zpow_eq_zpow_val, map_zpow₀, hu₀v, one_zpow]⟩ with hs
  set s' : v.adicCompletionIntegers E :=
    ⟨((u₀ ^ (n + a : ℤ) : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
      rw [mem_adicCompletionIntegers, Units.val_zpow_eq_zpow_val, map_zpow₀, hu₀v, one_zpow]⟩ with hs'
  have hss' : s * s' = 1 := by
    apply Subtype.ext
    show ((u₀ ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
      ((u₀ ^ (n + a : ℤ) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one]
  have hsplit : (((uniformizerUnit E v * u₀) ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      ((uniformizerUnit E v ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (s : v.adicCompletion E) := by
    rw [mul_zpow, Units.val_mul]
  have hcE : c E v a = ((uniformizerUnit E v ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    show ((uniformizerUnit E v ^ (-(addCharLevel (psiLocal E v) + a : ℤ)) : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = _
    rw [hn]
  have hbase : Valued.v (((uniformizerUnit E v ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E))
      ≤ WithZero.exp (n + a) :=
    LanglandsTunnell.TateLocal.valued_uniformizerUnit_zpow_neg_le E v n a
  have hcs : Valued.v (((uniformizerUnit E v ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
      (s : v.adicCompletion E)) ≤ WithZero.exp (n + a) := by
    rw [← hsplit]; exact hc'
  rw [modelAddChar_congr v (psiLocal E v) hψE' hψE' hc' hcs hsplit,
    modelAddChar_mul E v (psiLocal E v) hψE' _ hbase s hcs]
  set t : (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)ˣ :=
    ⟨Ideal.Quotient.mk _ s, Ideal.Quotient.mk _ s',
      by rw [← map_mul (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)) s s', hss',
        map_one],
      by rw [← map_mul (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a)) s' s,
        mul_comm, hss', map_one]⟩ with ht
  have htval : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a) s) = (t : _) := rfl
  rw [htval, gaussSum_mulShift_unit]
  have hsv : Valued.v (s : v.adicCompletion E) = 1 := by
    show Valued.v ((u₀ ^ (-(n + a : ℤ)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu₀v, one_zpow]
  have hΧt : modelMulChar E v μ⁻¹ ha1 (inv_apply_eq_one_of_hasConductorExponentAt E v μ hμa) t =
      (μ u₀ ^ (-(n + a : ℤ)))⁻¹ := by
    rw [modelMulChar_apply_eq E v μ⁻¹ ha1 _ hsv t rfl, MonoidHom.inv_apply, ← map_zpow]

    exact congrArg (fun z : (v.adicCompletion E)ˣ => (μ z)⁻¹) (Units.ext (val_unitOfValuedEqOne E v s hsv))
  rw [modelAddChar_congr v (psiLocal E v) hψE' (hψlevel E v) hbase (valued_c E v a) hcE.symm, hΧt, inv_inv]

private theorem stdRootNumberAt_comp_norm_of_pos (μ : (v.adicCompletion E)ˣ →* ℂˣ) {a : ℕ} (ha1 : 1 ≤ a)
    (hμa : HasConductorExponentAt E v μ a) (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    stdRootNumberAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) = stdRootNumberAt E v μ := by

  have hfac := exists_uniformizer_factor v w he hf
  obtain ⟨u₀, hu₀v, hx₀v, hu₀⟩ := hfac
  have hμM : HasConductorExponentAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a :=
    hasConductorExponentAt_comp_norm v w he hf μ a hμa
  haveI := finite_model v a
  haveI := finite_model w.1 a
  have hμu₀ : ‖(μ u₀ : ℂ)‖ = 1 := norm_apply_eq_one_of_valued_eq_one E v μ hμa.1 hu₀v
  have hpre : (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) (uniformizerUnit M w.1) =
      μ (uniformizerUnit E v) * μ u₀ := by
    rw [← hu₀, comp_norm_map_algebraMap v w he hf, map_mul]
  have huM : ‖(((μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) (uniformizerUnit M w.1) : ℂˣ) : ℂ)‖
      = 1 := by
    rw [hpre, Units.val_mul, norm_mul, hμ, hμu₀, one_mul]
  have hlev := addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w he
  have hc' : Valued.v (((uniformizerUnit E v * u₀) ^ (-(addCharLevel (psiLocal M w.1) + a : ℤ)) :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ WithZero.exp (addCharLevel (psiLocal M w.1) + a) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hx₀v, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg]
  have hψE' : ∀ x : v.adicCompletion E, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal M w.1)) →
      psiLocal E v x = 1 := fun x hx => hψlevel E v x (by rw [← hlev]; exact hx)
  classical
  letI : Fintype (v.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) ^ a) :=
    Fintype.ofFinite _
  letI : Fintype (w.1.adicCompletionIntegers M ⧸ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) ^ a) :=
    Fintype.ofFinite _
  rw [stdRootNumberAt_eq_const_mul_gaussSum M w.1 _ ha1 hμM huM,
    stdRootNumberAt_eq_const_mul_gaussSum E v μ ha1 hμa hμ,
    Cst_eq_of_absNorm_eq_of_level_eq (by exact_mod_cast absNorm_asIdeal_eq v w hf) hlev a,
    gaussSum_upstairs_eq_transport v w he hf μ ha1 hμa hμM _ hu₀ hc' hψE',
    gaussSum_shift_eq v w he hf μ ha1 hμa u₀ hu₀v hlev hψE' hc', hpre, hlev]

  have hU : (μ (uniformizerUnit E v) * μ u₀) ^ (addCharLevel (psiLocal E v) + a : ℤ) *
        μ u₀ ^ (-(addCharLevel (psiLocal E v) + a : ℤ)) =
      μ (uniformizerUnit E v) ^ (addCharLevel (psiLocal E v) + a : ℤ) := by
    rw [mul_zpow, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hUc : (((μ (uniformizerUnit E v) * μ u₀) ^ (addCharLevel (psiLocal E v) + a : ℤ) : ℂˣ) : ℂ) *
      ((μ u₀ ^ (-(addCharLevel (psiLocal E v) + a : ℤ)) : ℂˣ) : ℂ) =
      ((μ (uniformizerUnit E v) ^ (addCharLevel (psiLocal E v) + a : ℤ) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, hU]
  rw [← Units.val_zpow_eq_zpow_val, ← Units.val_zpow_eq_zpow_val, mul_mul_mul_comm, hUc, ← mul_assoc]

private theorem head (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : HasConductorExponentAt E v μ a)
    (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    HasConductorExponentAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a ∧
      stdRootNumberAt M w.1 (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) = stdRootNumberAt E v μ := by
  refine ⟨hasConductorExponentAt_comp_norm v w he hf μ a ha, ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · exact stdRootNumberAt_comp_norm_of_zero v w he hf μ ha hμ
  · exact stdRootNumberAt_comp_norm_of_pos v w he hf μ ha1 ha hμ

end DegreeOneCompletion
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal.UnitIntegral"

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one.LanglandsTunnell.TateLocal in

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 1)
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : HasConductorExponentAt E v μ a)
    (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    HasConductorExponentAt M w.1
        (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a ∧
      stdRootNumberAt M w.1
          (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) =
        stdRootNumberAt E v μ := by
  exact DegreeOneCompletion.head v w he hf μ a ha hμ

end S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one (solution)
