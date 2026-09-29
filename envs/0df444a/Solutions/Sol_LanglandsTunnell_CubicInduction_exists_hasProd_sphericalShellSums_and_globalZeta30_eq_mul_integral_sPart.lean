-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9a5ac1c9-ebe1-51dc-8007-8b712de71d97

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "globalZeta30 IsGL3PsiWhittakerFn psiLoc AdelicGL embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 LocalGL3 varpi cNormQ diagUnitGL2 coe_diagUnitGL2 diagHom_apply ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue HasSphericalTorusValuesAt eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn"
namespace EulerProductOutsideS
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem norm_sphericalTorusValue_le (e₁ e₂ e₃ : ℂ) (B : ℝ) (hB : 1 ≤ B) (h₁ : ‖e₁‖ ≤ B)
    (h₂ : ‖e₂‖ ≤ B) (h₃ : ‖e₃‖ ≤ B) (n : ℕ) : ‖sphericalTorusValue e₁ e₂ e₃ n‖ ≤ (3 * B) ^ n := by
  have h3B : (1 : ℝ) ≤ 3 * B := by linarith
  have key : ∀ n : ℕ, ‖sphericalTorusValue e₁ e₂ e₃ n‖ ≤ (3 * B) ^ n ∧
      ‖sphericalTorusValue e₁ e₂ e₃ (n + 1)‖ ≤ (3 * B) ^ (n + 1) ∧
      ‖sphericalTorusValue e₁ e₂ e₃ (n + 2)‖ ≤ (3 * B) ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [sphericalTorusValue]
      · simp only [sphericalTorusValue, zero_add, pow_one]; linarith
      · simp only [sphericalTorusValue, zero_add]
        calc ‖e₁ ^ 2 - e₂‖ ≤ ‖e₁ ^ 2‖ + ‖e₂‖ := norm_sub_le _ _
          _ = ‖e₁‖ ^ 2 + ‖e₂‖ := by rw [norm_pow]
          _ ≤ B ^ 2 + B := by gcongr
          _ ≤ (3 * B) ^ 2 := by nlinarith
    | succ k ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have hrec : sphericalTorusValue e₁ e₂ e₃ (k + 1 + 2) =
          e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1) +
            e₃ * sphericalTorusValue e₁ e₂ e₃ k := by
        simp [sphericalTorusValue]
      have hX : (0 : ℝ) ≤ (3 * B) ^ k := by positivity
      have hpoly : B * (3 * B) ^ (k + 2) + B * (3 * B) ^ (k + 1) + B * (3 * B) ^ k ≤ (3 * B) ^ (k + 1 + 2) := by
        have e1 : (3 * B) ^ (k + 1) = (3 * B) ^ k * (3 * B) := by ring
        have e2 : (3 * B) ^ (k + 2) = (3 * B) ^ k * (3 * B) ^ 2 := by ring
        have e3 : (3 * B) ^ (k + 1 + 2) = (3 * B) ^ k * (3 * B) ^ 3 := by ring
        rw [e1, e2, e3]
        nlinarith [mul_nonneg hX (by linarith : (0 : ℝ) ≤ B), mul_nonneg (mul_nonneg hX (by linarith : (0 : ℝ) ≤ B))
          (by linarith : (0 : ℝ) ≤ B - 1)]
      rw [hrec]
      calc ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1) +
              e₃ * sphericalTorusValue e₁ e₂ e₃ k‖
          ≤ ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1)‖ +
              ‖e₃ * sphericalTorusValue e₁ e₂ e₃ k‖ := norm_add_le _ _
        _ ≤ ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2)‖ + ‖e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1)‖ +
              ‖e₃ * sphericalTorusValue e₁ e₂ e₃ k‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖e₁‖ * ‖sphericalTorusValue e₁ e₂ e₃ (k + 2)‖ + ‖e₂‖ * ‖sphericalTorusValue e₁ e₂ e₃ (k + 1)‖ +
              ‖e₃‖ * ‖sphericalTorusValue e₁ e₂ e₃ k‖ := by simp only [norm_mul]
        _ ≤ B * (3 * B) ^ (k + 2) + B * (3 * B) ^ (k + 1) + B * (3 * B) ^ k := by gcongr
        _ ≤ (3 * B) ^ (k + 1 + 2) := hpoly
  exact (key n).1

private def shellTermN (e₁ e₂ e₃ x : ℂ) (n : ℕ) : ℂ := sphericalTorusValue e₁ e₂ e₃ n * x ^ n

private def shellTerm (e₁ e₂ e₃ x : ℂ) (m : ℤ) : ℂ := if 0 ≤ m then shellTermN e₁ e₂ e₃ x m.toNat else 0

private theorem shellTerm_of_neg (e₁ e₂ e₃ x : ℂ) {m : ℤ} (hm : m < 0) : shellTerm e₁ e₂ e₃ x m = 0 := by
  simp [shellTerm, not_le.mpr hm]

private theorem shellTerm_natCast (e₁ e₂ e₃ x : ℂ) (n : ℕ) : shellTerm e₁ e₂ e₃ x n = shellTermN e₁ e₂ e₃ x n := by
  simp [shellTerm]

private theorem shellTermN_zero (e₁ e₂ e₃ x : ℂ) : shellTermN e₁ e₂ e₃ x 0 = 1 := by
  simp [shellTermN, sphericalTorusValue]

private theorem norm_shellTermN_le (e₁ e₂ e₃ x : ℂ) (B : ℝ) (hB : 1 ≤ B) (h₁ : ‖e₁‖ ≤ B) (h₂ : ‖e₂‖ ≤ B)
    (h₃ : ‖e₃‖ ≤ B) (n : ℕ) : ‖shellTermN e₁ e₂ e₃ x n‖ ≤ (3 * B * ‖x‖) ^ n := by
  rw [shellTermN, norm_mul, norm_pow, mul_pow]
  gcongr
  exact norm_sphericalTorusValue_le e₁ e₂ e₃ B hB h₁ h₂ h₃ n

private theorem summable_norm_shellTermN_and_norm_tsum_sub_one_le (e₁ e₂ e₃ x : ℂ) (B : ℝ) (hB : 1 ≤ B)
    (h₁ : ‖e₁‖ ≤ B) (h₂ : ‖e₂‖ ≤ B) (h₃ : ‖e₃‖ ≤ B) (hr : 3 * B * ‖x‖ ≤ 1 / 2) :
    (Summable fun n : ℕ => ‖shellTermN e₁ e₂ e₃ x n‖) ∧
      ‖(∑' n : ℕ, shellTermN e₁ e₂ e₃ x n) - 1‖ ≤ 2 * (3 * B * ‖x‖) ∧
      ∑' n : ℕ, ‖shellTermN e₁ e₂ e₃ x n‖ ≤ 1 + 2 * (3 * B * ‖x‖) := by
  set r : ℝ := 3 * B * ‖x‖ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by linarith
  have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
  have hle : ∀ n : ℕ, ‖shellTermN e₁ e₂ e₃ x n‖ ≤ r ^ n := norm_shellTermN_le e₁ e₂ e₃ x B hB h₁ h₂ h₃
  have hnorm : Summable fun n : ℕ => ‖shellTermN e₁ e₂ e₃ x n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgeom
  have hinv_le : (1 - r)⁻¹ ≤ 1 + 2 * r := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨hnorm, ?_, ?_⟩
  swap
  · calc ∑' n : ℕ, ‖shellTermN e₁ e₂ e₃ x n‖ ≤ ∑' n : ℕ, r ^ n := hnorm.tsum_le_tsum hle hgeom
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
      _ ≤ 1 + 2 * r := hinv_le
  have hsum : Summable fun n : ℕ => shellTermN e₁ e₂ e₃ x n := hnorm.of_norm
  rw [hsum.tsum_eq_zero_add, shellTermN_zero, add_sub_cancel_left]
  have hnorm' : Summable fun n : ℕ => ‖shellTermN e₁ e₂ e₃ x (n + 1)‖ := (summable_nat_add_iff 1).mpr hnorm
  have hgeom' : Summable fun n : ℕ => r ^ (n + 1) := (summable_nat_add_iff 1).mpr hgeom
  calc ‖∑' n : ℕ, shellTermN e₁ e₂ e₃ x (n + 1)‖
      ≤ ∑' n : ℕ, ‖shellTermN e₁ e₂ e₃ x (n + 1)‖ := norm_tsum_le_tsum_norm hnorm'
    _ ≤ ∑' n : ℕ, r ^ (n + 1) := hnorm'.tsum_le_tsum (fun n => hle (n + 1)) hgeom'
    _ = r * (1 - r)⁻¹ := by
        simp only [pow_succ']
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ r * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    _ = 2 * r := mul_comm _ _

end LanglandsTunnell.CubicInduction.EulerProductOutsideS

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "globalZeta30 IsGL3PsiWhittakerFn psiLoc AdelicGL embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 LocalGL3 varpi cNormQ diagUnitGL2 coe_diagUnitGL2 diagHom_apply ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue HasSphericalTorusValuesAt eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn"
namespace EulerProductOutsideS
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

noncomputable section

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

private theorem hasSum_int_of_hasSum_nat {f : ℤ → ℂ} (hf : ∀ m : ℤ, m < 0 → f m = 0) {L : ℂ}
    (h : HasSum (fun n : ℕ => f n) L) : HasSum f L := by
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp h
  intro m hm
  refine hf m (lt_of_not_ge fun h0 => hm ?_)
  exact ⟨m.toNat, Int.toNat_of_nonneg h0⟩

private theorem hasSum_int_of_hasSum_nat_real {f : ℤ → ℝ} (hf : ∀ m : ℤ, m < 0 → f m = 0) {L : ℝ}
    (h : HasSum (fun n : ℕ => f n) L) : HasSum f L := by
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp h
  intro m hm
  refine hf m (lt_of_not_ge fun h0 => hm ?_)
  exact ⟨m.toNat, Int.toNat_of_nonneg h0⟩

section B4Passage

open MeasureTheory Filter Topology

section Passage

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : ℕ → Set α}

private theorem lintegral_eq_iSup_setLIntegral (hT : Monotone T) (hU : ⋃ n, T n = Set.univ)
    (g : α → ENNReal) : ∫⁻ x, g x ∂μ = ⨆ n, ∫⁻ x in T n, g x ∂μ := by
  have hd : Directed (· ⊆ ·) T := fun m n =>
    ⟨max m n, hT (le_max_left m n), hT (le_max_right m n)⟩
  calc ∫⁻ x, g x ∂μ = ∫⁻ x in Set.univ, g x ∂μ := by rw [Measure.restrict_univ]
    _ = ∫⁻ x in ⋃ n, T n, g x ∂μ := by rw [hU]
    _ = ⨆ n, ∫⁻ x in T n, g x ∂μ := setLIntegral_iUnion_of_directed g hd

private theorem setLIntegral_mono_nat (hT : Monotone T) (g : α → ENNReal) :
    Monotone fun n => ∫⁻ x in T n, g x ∂μ := fun _ _ hmn =>
  lintegral_mono' (Measure.restrict_mono (hT hmn) le_rfl) le_rfl

private theorem tendsto_setLIntegral_toReal (hT : Monotone T) (hU : ⋃ n, T n = Set.univ)
    {g : α → ENNReal} (hg : ∫⁻ x, g x ∂μ ≠ ⊤) :
    Tendsto (fun n => (∫⁻ x in T n, g x ∂μ).toReal) atTop (𝓝 (∫⁻ x, g x ∂μ).toReal) := by
  have h := tendsto_atTop_iSup (setLIntegral_mono_nat (μ := μ) hT g)
  rw [← lintegral_eq_iSup_setLIntegral hT hU g] at h
  exact (ENNReal.tendsto_toReal hg).comp h

private theorem tendsto_setIntegral_real (hT : Monotone T) (hU : ⋃ n, T n = Set.univ)
    {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x in T n, g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hpos : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hg.2.ne (lintegral_ofReal_le_lintegral_enorm g)
  have hneg : ∫⁻ x, ENNReal.ofReal (-g x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hg.neg.2.ne (lintegral_ofReal_le_lintegral_enorm (fun x => -g x))
  have h := (tendsto_setLIntegral_toReal hT hU hpos).sub (tendsto_setLIntegral_toReal hT hU hneg)
  rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg] at h
  refine h.congr fun n => ?_
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg.restrict).symm

private theorem integrable_and_tendsto_setIntegral_of_monotone_of_iUnion_eq_univ {f : α → ℂ}
    (hT : Monotone T) (hU : ⋃ n, T n = Set.univ) (hf : ∀ n, IntegrableOn f (T n) μ) {M : ℝ}
    (hM : ∀ n, ∫ x in T n, ‖f x‖ ∂μ ≤ M) :
    Integrable f μ ∧ Tendsto (fun n => ∫ x in T n, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hint : Integrable f μ := by
    refine ⟨?_, ?_⟩
    · have h : AEStronglyMeasurable f (μ.restrict (⋃ n, T n)) :=
        aestronglyMeasurable_iUnion_iff.mpr fun n => (hf n).aestronglyMeasurable
      rwa [hU, Measure.restrict_univ] at h
    · rw [HasFiniteIntegral, lintegral_eq_iSup_setLIntegral hT hU]
      refine lt_of_le_of_lt (iSup_le fun n => ?_) ENNReal.ofReal_lt_top (b := ENNReal.ofReal M)
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
      exact ENNReal.ofReal_le_ofReal (hM n)
  refine ⟨hint, ?_⟩
  have hre := tendsto_setIntegral_real hT hU hint.re
  have him := tendsto_setIntegral_real hT hU hint.im
  have key : ∀ ν : Measure α, Integrable f ν →
      ((∫ x, RCLike.re (f x) ∂ν : ℝ) : ℂ) + (∫ x, RCLike.im (f x) ∂ν : ℝ) * Complex.I =
        ∫ x, f x ∂ν := fun ν hν => integral_re_add_im hν
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  rw [Function.comp_def, Function.comp_def] at h
  simp only at h
  rw [key μ hint] at h
  refine h.congr fun n => key _ hint.restrict

end Passage

section Products

variable {ι : Type*}

private theorem finite_setOf_le_of_summable_rpow_neg {N : ι → ℕ} (hN : ∀ i, 1 ≤ N i) {σ : ℝ}
    (hs : Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ)) (n : ℕ) : {i | N i ≤ n}.Finite := by
  rcases le_or_gt σ 0 with hσ | hσ
  ·
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (zero_lt_one' ℝ))
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i _ => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    have h1 : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
    exact Real.one_le_rpow h1 (neg_nonneg.mpr hσ)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine Set.finite_empty.subset fun i hi => ?_
      have := hN i
      simp only [Set.mem_setOf_eq, nonpos_iff_eq_zero] at hi
      omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hε : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hnpos _
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    have hNi : (0 : ℝ) < N i := by exact_mod_cast (hN i)
    have hle : ((N i : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
    exact Real.rpow_le_rpow_of_nonpos hNi hle (neg_nonpos.mpr hσ.le)

private theorem prod_one_add_le_exp_tsum {c : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c)
    (s : Finset ι) : ∏ i ∈ s, (1 + c i) ≤ Real.exp (∑' i, c i) := by
  calc ∏ i ∈ s, (1 + c i) ≤ ∏ i ∈ s, Real.exp (c i) :=
        Finset.prod_le_prod (fun i _ => by linarith [hc0 i]) fun i _ => by
          linarith [Real.add_one_le_exp (c i)]
    _ = Real.exp (∑ i ∈ s, c i) := (Real.exp_sum s c).symm
    _ ≤ Real.exp (∑' i, c i) := Real.exp_le_exp.mpr (hc.sum_le_tsum s fun i _ => hc0 i)

private theorem tendsto_prod_toList_filter_of_hasProd (p : ι → Prop) [DecidablePred p] (g : ι → ℂ) {L : ℂ}
    (hL : HasProd (fun i : {i // p i} => g i.1) L) (N : ι → ℕ) (hfin : ∀ n, {i | N i ≤ n}.Finite) :
    Tendsto (fun n => ((((hfin n).toFinset.filter p).toList.map g).prod)) atTop (𝓝 L) := by
  have hF : Tendsto (fun n => ((hfin n).toFinset.subtype p)) atTop (atTop : Filter (Finset {i // p i})) := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b.sup fun i => N i.1, fun n hn i hi => ?_⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact le_trans (Finset.le_sup (f := fun i : {i // p i} => N i.1) hi) hn
  have h := hL.comp hF
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Finset.prod_subtype_eq_prod_filter, Finset.prod_map_toList]

end Products

end B4Passage

section Remint

open NumberField.AdeleRing NumberField.TateGlobal

private theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem ideleNorm_zpow {F : Type} [Field F] [NumberField F] (x : (AdeleRing (𝓞 F) F)ˣ) (m : ℤ) :
    ideleNorm F (x ^ m) = ideleNorm F x ^ m := by
  simp only [ideleNorm, map_zpow, NNReal.coe_zpow]

private theorem ideleNorm_map_prod {F : Type} [Field F] [NumberField F] {ι : Type*} (l : List ι)
    (g : ι → (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (l.map g).prod = (l.map fun i => ideleNorm F (g i)).prod := by
  induction l with
  | nil => simp [ideleNorm]
  | cons i l ih => simp [ideleNorm_mul, ih]

private theorem units_val_map_prod {ι : Type*} (l : List ι) (g : ι → ℂˣ) :
    (((l.map g).prod : ℂˣ) : ℂ) = (l.map fun i => ((g i : ℂˣ) : ℂ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem ofReal_map_prod {ι : Type*} (l : List ι) (g : ι → ℝ) :
    (((l.map g).prod : ℝ) : ℂ) = (l.map fun i => ((g i : ℝ) : ℂ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem ofReal_map_prod_cpow {ι : Type*} (l : List ι) (g : ι → ℝ) (hg : ∀ i ∈ l, 0 ≤ g i) (z : ℂ) :
    ((((l.map g).prod : ℝ) : ℂ)) ^ z = (l.map fun i => ((g i : ℝ) : ℂ) ^ z).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : 0 ≤ g i := hg i (by simp)
    have hl : 0 ≤ (l.map g).prod := List.prod_nonneg fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hg j (by simp [hj])
    rw [List.map_cons, List.prod_cons, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hi hl,
      ih fun j hj => hg j (by simp [hj]), List.map_cons, List.prod_cons]

private theorem iUnion_coe_unitIdelesOutside_eq_univ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Lf : ℕ → List (HeightOneSpectrum (𝓞 F)))
    (hcov : ∀ n : ℕ, ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → Ideal.absNorm v.asIdeal ≤ n → v ∈ Lf n) :
    ⋃ n : ℕ, (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 F) F)ˣ) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_

  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (finitePartUnits (𝓞 F) F x : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F ∧
        (((finitePartUnits (𝓞 F) F x)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
          v.adicCompletionIntegers F := by
    filter_upwards [(finitePartUnits (𝓞 F) F x : FiniteAdeleRing (𝓞 F) F).2,
      (((finitePartUnits (𝓞 F) F x)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2] with v h1 h2
    exact ⟨h1, h2⟩
  rw [Filter.eventually_cofinite] at hev

  obtain ⟨n, hn⟩ := (hev.image fun v => Ideal.absNorm v.asIdeal).bddAbove
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro v hv
  by_contra hbad
  have hle : Ideal.absNorm v.asIdeal ≤ n := hn ⟨v, hbad, rfl⟩
  exact hv (Set.mem_union_right _ (hcov n v (fun hvS => hv (Set.mem_union_left _ hvS)) hle))

private theorem monotone_coe_unitIdelesOutside (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Lf : ℕ → List (HeightOneSpectrum (𝓞 F)))
    (hmono : ∀ n : ℕ, Lf n ⊆ Lf (n + 1)) :
    Monotone fun n : ℕ =>
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hmon : Monotone fun k : ℕ => ({v | v ∈ Lf k} : Set (HeightOneSpectrum (𝓞 F))) :=
    monotone_nat_of_le_succ fun k v hv => hmono k hv
  intro m n hmn x hx
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff] at hx ⊢
  exact IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_mono (R := 𝓞 F) (K := F)
    (Set.union_subset_union_right _ (hmon hmn)) hx

end Remint

section Valuations

open IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_natCast' (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

private theorem absNorm_span_intCast' (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast' (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast' (n : ℤ)

private theorem intValuation_absNorm' :
    v.intValuation (Ideal.absNorm v.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast'] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_ratPrimeAt' : Valued.v (ratPrimeAt v) = Valued.v (varpi v) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast', intValuation_absNorm']
  exact (AdelicLevel.valued_uniformizerUnit ℚ v).symm

private theorem valued_varpi_lt_one' : Valued.v (varpi v) < 1 := by
  show Valued.v (AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) < 1
  rw [AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private def primeOverUniformizer : (v.adicCompletion ℚ)ˣ := (AdelicLevel.uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v

private theorem ratPrimeUnit_eq : ratPrimeUnit v = AdelicLevel.uniformizerUnit ℚ v * primeOverUniformizer v := by
  rw [primeOverUniformizer, mul_inv_cancel_left]

private theorem valued_primeOverUniformizer :
    Valued.v ((primeOverUniformizer v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  have hϖ : Valued.v (varpi v) ≠ 0 := by
    rw [AdelicLevel.valued_uniformizerUnit]; exact WithZero.exp_ne_zero
  rw [primeOverUniformizer, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  change (Valued.v (varpi v))⁻¹ * Valued.v (ratPrimeAt v) = 1
  rw [valued_ratPrimeAt', inv_mul_cancel₀ hϖ]

private theorem valued_primeOverUniformizer_inv :
    Valued.v (((primeOverUniformizer v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, valued_primeOverUniformizer, inv_one]

end Valuations

section Matrices

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_iotaGL_diagUnitGL2 {A : Type*} [CommRing A] (u : Aˣ) :
    ((iotaGL (diagUnitGL2 u) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal ![(u : A), 1, 1] := by
  rw [coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem coe_iotaGL_diagUnitGL2_inv {A : Type*} [CommRing A] (u : Aˣ) :
    (((iotaGL (diagUnitGL2 u))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.diagonal ![((u⁻¹ : Aˣ) : A), 1, 1] := by
  show embedMat2 !![((u⁻¹ : Aˣ) : A), 0; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem valued_diagonal_entry_le_one {a : v.adicCompletion ℚ} (ha : Valued.v a ≤ 1) (i j : Fin 3) :
    Valued.v (Matrix.diagonal ![a, 1, 1] i j) ≤ 1 := by
  rw [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    fin_cases i
    · simpa using ha
    · simp
    · simp
  · simp

private theorem iotaGL_diagUnitGL2_mem {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) ≤ 1)
    (hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1) :
    iotaGL (diagUnitGL2 u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, coe_iotaGL_diagUnitGL2, coe_iotaGL_diagUnitGL2_inv]
  exact ⟨valued_diagonal_entry_le_one v hu, valued_diagonal_entry_le_one v hu'⟩

private theorem iotaGL_diagUnitGL2_mul {A : Type*} [CommRing A] (x y : Aˣ) :
    iotaGL (diagUnitGL2 (x * y)) = iotaGL (diagUnitGL2 x) * iotaGL (diagUnitGL2 y) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, map_mul, map_mul]

private theorem iotaGL_diagUnitGL2_one {A : Type*} [CommRing A] : iotaGL (diagUnitGL2 (1 : Aˣ)) = 1 := by
  rw [← diagHom_apply, map_one, map_one]

private theorem iotaGL_diagUnitGL2_uniformizer_pow (n : ℕ) :
    iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n)) =
      iotaTorusLocal v n * iotaGL (diagUnitGL2 ((primeOverUniformizer v ^ n)⁻¹)) := by
  rw [iotaTorusLocal, diagHom_apply, ratPrimeUnit_eq, mul_pow, iotaGL_diagUnitGL2_mul, mul_assoc,
    ← iotaGL_diagUnitGL2_mul, mul_inv_cancel, iotaGL_diagUnitGL2_one, mul_one]

private theorem iotaGL_diagUnitGL2_primeOverUniformizer_pow_inv_mem (n : ℕ) :
    iotaGL (diagUnitGL2 ((primeOverUniformizer v ^ n)⁻¹)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine iotaGL_diagUnitGL2_mem v ?_ ?_
  · rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, valued_primeOverUniformizer,
      one_pow, inv_one]
  · rw [inv_inv, Units.val_pow_eq_pow_val, map_pow, valued_primeOverUniformizer, one_pow]

end Matrices

section Components

private abbrev evalAt (v : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* v.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem evalAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : evalAt v a = a.2 v := rfl

private theorem componentAt3_eq_map (v : HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v x = Matrix.GeneralLinearGroup.map (evalAt v) x := rfl

private abbrev evalUnits (v : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (v.adicCompletion ℚ)ˣ :=
  Units.map (evalAt v : AdeleRing (𝓞 ℚ) ℚ →* v.adicCompletion ℚ)

private abbrev archUnits : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (InfiniteAdeleRing ℚ)ˣ :=
  Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ : AdeleRing (𝓞 ℚ) ℚ →* InfiniteAdeleRing ℚ)

private theorem coe_evalUnits (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((evalUnits v a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (a : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl

private theorem coe_evalUnits_inv (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((evalUnits v a)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v := by
  rw [← map_inv]; rfl

private theorem coe_archUnits (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((archUnits a : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (a : AdeleRing (𝓞 ℚ) ℚ).1 := rfl

private theorem map_iotaGL_diagUnitGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (Units.map (f : A →* B) a)) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, MonoidHom.coe_coe, coe_iotaGL_diagUnitGL2]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hij]

private theorem componentAt3_iotaGL_diagUnitGL2_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a) * g) =
      iotaGL (diagUnitGL2 (evalUnits v a)) * componentAt3 (𝓞 ℚ) ℚ v g := by
  rw [map_mul, componentAt3_eq_map, map_iotaGL_diagUnitGL2, componentAt3_eq_map]

private theorem archComponent3_iotaGL_diagUnitGL2_mul (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a) * g) =
      iotaGL (diagUnitGL2 (archUnits a)) * archComponent3 (𝓞 ℚ) ℚ g := by
  rw [map_mul]
  congr 1
  exact map_iotaGL_diagUnitGL2 _ a

private theorem iotaGL_diagUnitGL2_units_map_mem (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h1 : (a : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ)
    (h2 : ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ) :
    iotaGL (diagUnitGL2 (evalUnits v a)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine iotaGL_diagUnitGL2_mem v ?_ ?_
  · rw [coe_evalUnits]; exact h1
  · rw [coe_evalUnits_inv]; exact h2

end Components

section LocalValues

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem wloc_uniformizer_pow (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (Wv : LocalGL3 v → ℂ) (hK : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wv (y * k) = Wv y)
    (hsph : HasSphericalTorusValuesAt c v Wv) (n : ℕ) :
    Wv (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n))) =
      (cNormQ v)⁻¹ ^ n *
        sphericalTorusValue (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v)
          (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v) (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v) n := by
  rw [iotaGL_diagUnitGL2_uniformizer_pow, hK _ (iotaGL_diagUnitGL2_primeOverUniformizer_pow_inv_mem v n)]
  exact hsph.1 n

private theorem wloc_uniformizer_zpow_of_neg (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (Wv : LocalGL3 v → ℂ) (hK : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wv (y * k) = Wv y)
    (hlaw : IsGL3PsiWhittakerFn ψv Wv) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    {m : ℤ} (hm : m < 0) : Wv (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ m))) = 0 := by
  refine eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv Wv (fun y k hk => hK k hk y) hlaw hψ1
    _ ![((AdelicLevel.uniformizerUnit ℚ v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1, 1]
    (coe_iotaGL_diagUnitGL2 _) (Or.inl ?_)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_one]
  rw [valued_uniformizerUnit_zpow, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem wloc_uniformizer_zpow_mul (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (Wv : LocalGL3 v → ℂ)
    (hK : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wv (y * k) = Wv y)
    (hlaw : IsGL3PsiWhittakerFn ψv Wv) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (hsph : HasSphericalTorusValuesAt c v Wv) (χϖ : ℂˣ) (s : ℂ) (m : ℤ) :
    Wv (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ m))) * ((χϖ ^ m : ℂˣ) : ℂ) *
        ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m : ℝ) : ℂ) ^ (s - 1) =
      shellTerm (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v) (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v)
        (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v) ((χϖ : ℂ) * cNormQ v ^ (-s)) m := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [wloc_uniformizer_zpow_of_neg v ψv Wv hK hlaw hψ1 hm, shellTerm_of_neg _ _ _ _ hm, zero_mul, zero_mul]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    rw [zpow_natCast, wloc_uniformizer_pow c v Wv hK hsph n, shellTerm_natCast, shellTermN, zpow_natCast, zpow_natCast]
    have hNpos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < Ideal.absNorm v.asIdeal by have := two_le_absNorm v; omega)
    have hinv : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
    have hcpow : ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ n : ℝ)) : ℂ) ^ (s - 1)) =
        (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ^ (s - 1)) ^ n := by
      rw [← Real.rpow_natCast, ← Complex.cpow_mul_ofReal_nonneg hinv, Complex.ofReal_natCast, Complex.cpow_nat_mul]
    have hbase : (cNormQ v)⁻¹ * ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ^ (s - 1) = cNormQ v ^ (-s) := by
      have hN0 : cNormQ v ≠ 0 := by
        rw [cNormQ]; exact_mod_cast (show (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 by have := two_le_absNorm v; omega)
      have harg : (cNormQ v).arg ≠ Real.pi := by
        rw [cNormQ, ← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
        exact Real.pi_ne_zero.symm
      have hcoe : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = (cNormQ v)⁻¹ := by
        rw [cNormQ]; push_cast; rfl
      rw [hcoe, Complex.inv_cpow _ _ harg, Complex.cpow_sub _ _ hN0, Complex.cpow_one, Complex.cpow_neg,
        div_eq_mul_inv, mul_inv, inv_inv, mul_left_comm, inv_mul_cancel₀ hN0, mul_one]
    rw [hcpow, Units.val_pow_eq_pow_val, ← hbase]
    simp only [mul_pow]
    ring
end LocalValues

section UniformizerComponents

private theorem coe_uniformizerIdele_snd (v w : HeightOneSpectrum (𝓞 ℚ)) :
    ((uniformizerIdele ℚ v : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v (AdelicLevel.uniformizerUnit ℚ v) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w := rfl

private theorem coe_uniformizerIdele_fst (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((uniformizerIdele ℚ v : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl

private theorem evalUnits_uniformizerIdele_self (v : HeightOneSpectrum (𝓞 ℚ)) :
    evalUnits v (uniformizerIdele ℚ v) = AdelicLevel.uniformizerUnit ℚ v := by
  apply Units.ext
  rw [coe_evalUnits, coe_uniformizerIdele_snd, AdelicLevel.localUnit_apply_self]

private theorem evalUnits_uniformizerIdele_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    evalUnits w (uniformizerIdele ℚ v) = 1 := by
  apply Units.ext
  rw [coe_evalUnits, coe_uniformizerIdele_snd, AdelicLevel.localUnit_apply_of_ne _ _ _ _ hw, Units.val_one]

private theorem archUnits_uniformizerIdele (v : HeightOneSpectrum (𝓞 ℚ)) : archUnits (uniformizerIdele ℚ v) = 1 := by
  apply Units.ext
  rw [coe_archUnits, coe_uniformizerIdele_fst, Units.val_one]

private theorem list_prod_map_eq_of_nodup {M : Type*} [CommMonoid M] (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (hL : L.Nodup) (f : HeightOneSpectrum (𝓞 ℚ) → M) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ L)
    (hf : ∀ v ∈ L, v ≠ w → f v = 1) : (L.map f).prod = f w := by
  induction L with
  | nil => simp at hw
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hw with rfl | hwL
    · rw [List.prod_eq_one fun x hx => ?_, mul_one]
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact hf u (List.mem_cons_of_mem _ hu) (fun h => hL.1 (h ▸ hu))
    · rw [ih hL.2 hwL (fun u hu hne => hf u (List.mem_cons_of_mem _ hu) hne), hf v (List.mem_cons_self ..)
        (fun h => hL.1 (h ▸ hwL)), one_mul]

private theorem list_prod_map_eq_one_of_forall {M : Type*} [CommMonoid M] (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (f : HeightOneSpectrum (𝓞 ℚ) → M) (hf : ∀ v ∈ L, f v = 1) : (L.map f).prod = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  exact hf u hu

private theorem evalUnits_uniformizer_prod_of_mem (L : List (HeightOneSpectrum (𝓞 ℚ))) (hL : L.Nodup)
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ L) :
    evalUnits w (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = AdelicLevel.uniformizerUnit ℚ w ^ m w := by
  rw [map_list_prod, List.map_map]
  rw [list_prod_map_eq_of_nodup L hL _ hw]
  · simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_self]
  · intro v _ hvw
    simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_of_ne (Ne.symm hvw), _root_.one_zpow]

private theorem evalUnits_uniformizer_prod_of_not_mem (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∉ L) :
    evalUnits w (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = 1 := by
  rw [map_list_prod, List.map_map]
  refine list_prod_map_eq_one_of_forall L _ fun v hv => ?_
  have hne : w ≠ v := fun h => hw (h ▸ hv)
  simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_of_ne hne, _root_.one_zpow]

private theorem archUnits_uniformizer_prod (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) :
    archUnits (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = 1 := by
  rw [map_list_prod, List.map_map]
  refine list_prod_map_eq_one_of_forall L _ fun v _ => ?_
  simp only [Function.comp_apply, map_zpow, archUnits_uniformizerIdele, _root_.one_zpow]

end UniformizerComponents

section Pointwise

open NumberField.TateGlobal

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem evalUnits_eq_one_of_coe_eq_one {w : HeightOneSpectrum (𝓞 ℚ)} {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hb : (b : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) : evalUnits w b = 1 :=
  Units.ext (by rw [coe_evalUnits, hb, Units.val_one])

private theorem archUnits_eq_one_of_coe_eq_one {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hb : (b : AdeleRing (𝓞 ℚ) ℚ).1 = 1) :
    archUnits b = 1 :=
  Units.ext (by rw [coe_archUnits, hb, Units.val_one])

private theorem iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdeles (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    iotaGL (diagUnitGL2 (evalUnits w u)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  rw [← IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_empty,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at hu
  obtain ⟨h1, h2⟩ := hu w (Set.notMem_empty w)
  refine iotaGL_diagUnitGL2_units_map_mem w u ?_ ?_
  · simpa using h1
  · have h__ := h2
    try simp at h__
    try simp
    exact h__

private theorem iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdelesOutside (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ T)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∉ T) :
    iotaGL (diagUnitGL2 (evalUnits w a)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at ha
  obtain ⟨h1, h2⟩ := ha w hw
  refine iotaGL_diagUnitGL2_units_map_mem w a ?_ ?_
  · simpa using h1
  · have h__ := h2
    try simp at h__
    try simp
    exact h__

private theorem whittaker_eq_mul_prod (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hone : ∀ v, v ∉ S → Wloc v 1 = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (m : HeightOneSpectrum (𝓞 ℚ) → ℤ)
    (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hb : ∀ v, v ∉ S → (b : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu1 : (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1) (huS : ∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1)
    (huU : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    W (iotaGL (diagUnitGL2 (b * (L.map fun v => uniformizerIdele ℚ v ^ m v).prod * u)) * g) =
      W (iotaGL (diagUnitGL2 b) * g) *
        (L.map fun v => Wloc v (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ m v)))).prod := by
  classical
  set P : (AdeleRing (𝓞 ℚ) ℚ)ˣ := (L.map fun v => uniformizerIdele ℚ v ^ m v).prod with hP
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := S ∪ L.toFinset with hT
  have hST : S ⊆ T := Finset.subset_union_left
  have hnotT : ∀ w, w ∉ T → w ∉ S ∧ w ∉ L := fun w hw => by
    rw [hT, Finset.mem_union, List.mem_toFinset] at hw
    exact ⟨fun h => hw (Or.inl h), fun h => hw (Or.inr h)⟩
  have hdisj : Disjoint S L.toFinset := Finset.disjoint_left.mpr fun w hwS hwL => hLS w (List.mem_toFinset.mp hwL) hwS

  have hcomp : ∀ w, componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 (b * P * u)) * g) =
      iotaGL (diagUnitGL2 (evalUnits w b)) * iotaGL (diagUnitGL2 (evalUnits w P)) *
        iotaGL (diagUnitGL2 (evalUnits w u)) * componentAt3 (𝓞 ℚ) ℚ w g := fun w => by
    rw [componentAt3_iotaGL_diagUnitGL2_mul, map_mul, map_mul, iotaGL_diagUnitGL2_mul, iotaGL_diagUnitGL2_mul]
  have hcomp' : ∀ w, componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 b) * g) =
      iotaGL (diagUnitGL2 (evalUnits w b)) * componentAt3 (𝓞 ℚ) ℚ w g := fun w =>
    componentAt3_iotaGL_diagUnitGL2_mul w b g
  have hb' : ∀ w, w ∉ S → evalUnits w b = 1 := fun w hw => evalUnits_eq_one_of_coe_eq_one (hb w hw)
  have huS' : ∀ w ∈ S, evalUnits w u = 1 := fun w hw => evalUnits_eq_one_of_coe_eq_one (huS w hw)

  have hoff : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 (b * P * u)) * g) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ w := fun w hw => by
    obtain ⟨hwS, hwL⟩ := hnotT w hw
    rw [hcomp, hb' w hwS, hP, evalUnits_uniformizer_prod_of_not_mem L m hwL, iotaGL_diagUnitGL2_one, one_mul, one_mul]
    exact Subgroup.mul_mem _ (iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdeles w huU) (hg w hwS)
  have hoff' : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 b) * g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w :=
    fun w hw => by
      rw [hcomp', hb' w (hnotT w hw).1, iotaGL_diagUnitGL2_one, one_mul]
      exact hg w (hnotT w hw).1

  have harch : archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 (b * P * u)) * g) =
      archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 b) * g) := by
    have hA : archUnits (b * P * u) = archUnits b := by
      rw [map_mul, map_mul, hP, archUnits_uniformizer_prod, archUnits_eq_one_of_coe_eq_one hu1, mul_one, mul_one]
    rw [archComponent3_iotaGL_diagUnitGL2_mul, archComponent3_iotaGL_diagUnitGL2_mul, hA]

  have hS_factor : ∀ w ∈ S, Wloc w (componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 (b * P * u)) * g)) =
      Wloc w (componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 b) * g)) := fun w hw => by
    have hwL : w ∉ L := fun h => hLS w h hw
    rw [hcomp, hcomp', hP, evalUnits_uniformizer_prod_of_not_mem L m hwL, huS' w hw, iotaGL_diagUnitGL2_one, mul_one,
      mul_one]
  have hL_factor : ∀ w ∈ L, Wloc w (componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 (b * P * u)) * g)) =
      Wloc w (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ w ^ m w))) := fun w hw => by
    have hwS : w ∉ S := hLS w hw
    rw [hcomp, hb' w hwS, iotaGL_diagUnitGL2_one, one_mul, hP, evalUnits_uniformizer_prod_of_mem L hL m hw, mul_assoc]
    exact hK w hwS _ (Subgroup.mul_mem _ (iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdeles w huU) (hg w hwS)) _
  have hL_factor' : ∀ w ∈ L, Wloc w (componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 b) * g)) = 1 := fun w hw => by
    have hwS : w ∉ S := hLS w hw
    rw [hcomp', hb' w hwS, iotaGL_diagUnitGL2_one, hK w hwS _ (hg w hwS) 1]
    exact hone w hwS

  rw [hfac _ T hST hoff, hfac _ T hST hoff', harch, hT, Finset.prod_union hdisj, Finset.prod_union hdisj,
    Finset.prod_congr rfl (fun w hw => hS_factor w hw),
    Finset.prod_congr rfl (fun w hw => hL_factor w (List.mem_toFinset.mp hw)),
    Finset.prod_congr rfl (fun w hw => hL_factor' w (List.mem_toFinset.mp hw)), Finset.prod_const_one, mul_one,
    List.prod_toFinset _ hL, mul_assoc]

private theorem char_eq_mul_prod (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) (b u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : χ u = 1) :
    ((χ (b * (L.map fun v => uniformizerIdele ℚ v ^ m v).prod * u) : ℂˣ) : ℂ) =
      ((χ b : ℂˣ) : ℂ) * (L.map fun v => ((χ (uniformizerIdele ℚ v) ^ m v : ℂˣ) : ℂ)).prod := by
  rw [map_mul, map_mul, hu, mul_one, map_list_prod, List.map_map, Units.val_mul, units_val_map_prod]
  congr 1
  exact congrArg List.prod (List.map_congr_left fun v _ => by simp only [Function.comp_apply, map_zpow])

private theorem norm_cpow_eq_mul_prod (L : List (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℤ)
    (b u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : ideleNorm ℚ u = 1) (s : ℂ) :
    ((ideleNorm ℚ (b * (L.map fun v => uniformizerIdele ℚ v ^ m v).prod * u) : ℝ) : ℂ) ^ (s - 1) =
      ((ideleNorm ℚ b : ℝ) : ℂ) ^ (s - 1) *
        (L.map fun v => (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v : ℝ) : ℂ) ^ (s - 1))).prod := by
  have hprod : ideleNorm ℚ (L.map fun v => uniformizerIdele ℚ v ^ m v).prod =
      (L.map fun v => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v : ℝ)).prod := by
    rw [ideleNorm_map_prod]
    exact congrArg List.prod (List.map_congr_left fun v _ => by rw [ideleNorm_zpow, ideleNorm_uniformizerIdele])
  have hnn : ∀ v ∈ L, (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v := fun v _ =>
    zpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _
  rw [ideleNorm_mul, ideleNorm_mul, hu, mul_one, hprod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos b).le (List.prod_nonneg fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact hnn v hv), ofReal_map_prod_cpow L _ hnn]

end Pointwise

section Integrand

open NumberField.TateGlobal

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private def zetaFn (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)

private def shellAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) : ℂ :=
  shellTerm (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v) (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v)
    (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v) (((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)) m

private theorem zetaFn_eq_mul_prod_shellAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v))
    (hψ1 : ∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)
    (hsph : ∀ v, v ∉ S → HasSphericalTorusValuesAt c v (Wloc v))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)) (s : ℂ)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) :
    zetaFn W χ s g a = zetaFn W χ s g (Hν.projS a) * (L.map fun v => shellAt c χ s v (Hν.ord v a)).prod := by
  obtain ⟨u, hu1, huS, huU, hau⟩ := Hν.decomp L hLS hL a ha
  have hone : ∀ v, v ∉ S → Wloc v 1 = 1 := fun v hv => by
    have h := (hsph v hv).1 0
    rwa [iotaTorusLocal_zero, pow_zero, one_mul, show sphericalTorusValue _ _ _ 0 = 1 from rfl] at h
  have hW := whittaker_eq_mul_prod S W Warch Wloc hfac hK hone g hg L hLS hL (fun v => Hν.ord v a) (Hν.projS a)
    (fun v hv => Hν.projS_off a v hv) u hu1 huS huU
  have hχ := char_eq_mul_prod χ L (fun v => Hν.ord v a) (Hν.projS a) u (hχU u hu1 huS huU)
  have hN := norm_cpow_eq_mul_prod L (fun v => Hν.ord v a) (Hν.projS a) u
    (ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ u hu1 huU) s
  have hshell : ∀ v ∈ L,
      Wloc v (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ Hν.ord v a))) *
          ((χ (uniformizerIdele ℚ v) ^ Hν.ord v a : ℂˣ) : ℂ) *
          (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ Hν.ord v a : ℝ) : ℂ) ^ (s - 1)) =
        shellAt c χ s v (Hν.ord v a) := fun v hv =>
    wloc_uniformizer_zpow_mul c v (psiLoc ψ v) (Wloc v) (hK v (hLS v hv)) (hlaw v (hLS v hv)) (hψ1 v (hLS v hv))
      (hsph v (hLS v hv)) (χ (uniformizerIdele ℚ v)) s (Hν.ord v a)
  have hcomb : (L.map fun v => shellAt c χ s v (Hν.ord v a)).prod =
      (L.map fun v => Wloc v (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ Hν.ord v a)))).prod *
          (L.map fun v => ((χ (uniformizerIdele ℚ v) ^ Hν.ord v a : ℂˣ) : ℂ)).prod *
        (L.map fun v => (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ Hν.ord v a : ℝ) : ℂ) ^ (s - 1))).prod := by
    rw [← List.prod_map_mul, ← List.prod_map_mul]
    exact congrArg List.prod (List.map_congr_left fun v hv => (hshell v hv).symm)
  calc zetaFn W χ s g a
      = zetaFn W χ s g (Hν.projS a * (L.map fun v => uniformizerIdele ℚ v ^ Hν.ord v a).prod * u) := by rw [← hau]
    _ = zetaFn W χ s g (Hν.projS a) * (L.map fun v => shellAt c χ s v (Hν.ord v a)).prod := by
        simp only [zetaFn]
        rw [hW, hχ, hN, hcomb]
        ring

end Integrand

section Analytic

open NumberField.TateGlobal

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private def shellN (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : ℂ :=
  shellTermN (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v) (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v)
    (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v) (((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)) n

private theorem shellAt_natCast (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : shellAt c χ s v n = shellN c χ s v n :=
  shellTerm_natCast _ _ _ _ n

private theorem shellAt_of_neg (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℤ} (hm : m < 0) : shellAt c χ s v m = 0 :=
  shellTerm_of_neg _ _ _ _ hm

private def placeBound (v : HeightOneSpectrum (𝓞 ℚ)) : ℝ := 6 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(4 : ℝ))

private theorem placeBound_nonneg (v : HeightOneSpectrum (𝓞 ℚ)) : 0 ≤ placeBound v := by
  unfold placeBound; positivity

private theorem summable_placeBound : Summable placeBound :=
  (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ (by norm_num : (1 : ℝ) < 4)).mul_left 6

private theorem shell_data (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (τ : ℝ)
    (hτ : ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (s : ℂ) (hs : κ + τ + 4 ≤ s.re) :
    (Summable fun n : ℕ => ‖shellN c χ s v n‖) ∧
      ‖(∑' n : ℕ, shellN c χ s v n) - 1‖ ≤ placeBound v ∧
      ∑' n : ℕ, ‖shellN c χ s v n‖ ≤ 1 + placeBound v := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hN] at hτ hκ
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast two_le_absNorm v
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hB1 : (1 : ℝ) ≤ N ^ κ := Real.one_le_rpow hN1 hκ0
  have hx : ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)‖ ≤ N ^ (τ - s.re) := by
    rw [norm_mul, cNormQ, Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm v; omega), ← hN, Complex.neg_re,
      Real.rpow_sub hNpos, Real.rpow_neg hNpos.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hτ (inv_nonneg.mpr (Real.rpow_nonneg hNpos.le _))
  have hratio : 3 * N ^ κ * ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)‖ ≤ 3 * N ^ (-(4 : ℝ)) := by
    calc 3 * N ^ κ * ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)‖ ≤ 3 * N ^ κ * N ^ (τ - s.re) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 3 * N ^ (κ + (τ - s.re)) := by rw [Real.rpow_add hNpos, mul_assoc]
      _ ≤ 3 * N ^ (-(4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
  have hsmall : 3 * N ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_ofNat]
    have h16 : (16 : ℝ) ≤ N ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ N ^ 4 := by gcongr
    have hpos : (0 : ℝ) < N ^ 4 := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  obtain ⟨h1, h2, h3⟩ := summable_norm_shellTermN_and_norm_tsum_sub_one_le _ _ _ _ (N ^ κ) hB1 hκ.1 hκ.2.1 hκ.2.2
    (hratio.trans hsmall)
  have hpb : 2 * (3 * N ^ κ * ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * cNormQ v ^ (-s)‖) ≤ placeBound v := by
    unfold placeBound
    rw [← hN]
    linarith
  exact ⟨h1, h2.trans hpb, h3.trans (by linarith)⟩

private theorem summable_norm_shellAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : Summable fun n : ℕ => ‖shellN c χ s v n‖) :
    Summable fun m : ℤ => ‖shellAt c χ s v m‖ := by
  have h1 : HasSum (fun n : ℕ => ‖shellAt c χ s v (n : ℤ)‖) (∑' n : ℕ, ‖shellN c χ s v n‖) := by
    simpa only [shellAt_natCast] using h.hasSum
  have h0 : ∀ m : ℤ, m < 0 → ‖shellAt c χ s v m‖ = 0 := fun m hm => by rw [shellAt_of_neg c χ s v hm, norm_zero]
  exact (hasSum_int_of_hasSum_nat_real (f := fun m : ℤ => ‖shellAt c χ s v m‖) h0 h1).summable

private theorem tsum_norm_shellAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : Summable fun n : ℕ => ‖shellN c χ s v n‖) :
    ∑' m : ℤ, ‖shellAt c χ s v m‖ = ∑' n : ℕ, ‖shellN c χ s v n‖ := by
  have h1 : HasSum (fun n : ℕ => ‖shellAt c χ s v (n : ℤ)‖) (∑' n : ℕ, ‖shellN c χ s v n‖) := by
    simpa only [shellAt_natCast] using h.hasSum
  have h0 : ∀ m : ℤ, m < 0 → ‖shellAt c χ s v m‖ = 0 := fun m hm => by rw [shellAt_of_neg c χ s v hm, norm_zero]
  exact (hasSum_int_of_hasSum_nat_real (f := fun m : ℤ => ‖shellAt c χ s v m‖) h0 h1).tsum_eq

private theorem tsum_shellAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : Summable fun n : ℕ => ‖shellN c χ s v n‖) :
    ∑' m : ℤ, shellAt c χ s v m = ∑' n : ℕ, shellN c χ s v n := by
  have h1 : HasSum (fun n : ℕ => shellAt c χ s v (n : ℤ)) (∑' n : ℕ, shellN c χ s v n) := by
    simpa only [shellAt_natCast] using h.of_norm.hasSum
  exact (hasSum_int_of_hasSum_nat (f := fun m : ℤ => shellAt c χ s v m) (fun m hm => shellAt_of_neg c χ s v hm)
    h1).tsum_eq

private theorem multipliable_subtype_of_summable {ι : Type*} (p : ι → Prop) {g : ι → ℂ} {b : ι → ℝ}
    (hb : Summable b) (hg : ∀ i, p i → ‖g i - 1‖ ≤ b i) : Multipliable fun i : {i // p i} => g i.1 := by
  have hfun : (fun i : {i // p i} => g i.1) = fun i : {i // p i} => 1 + (g i.1 - 1) := by
    funext i; ring
  rw [hfun]
  refine Complex.multipliable_one_add_of_summable ?_
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hg i.1 i.2) ?_
  exact hb.subtype {i | p i}

end Analytic

section Passage

open NumberField.TateGlobal

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private structure PassageData (c : HeightOneSpectrum (𝓞 K) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)) (s : ℂ) : Prop where
  pointwise : ∀ (L : List (HeightOneSpectrum (𝓞 ℚ))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}),
      zetaFn W χ s g a = zetaFn W χ s g (Hν.projS a) * (L.map fun v => shellAt c χ s v (Hν.ord v a)).prod
  integrableS : Integrable (zetaFn W χ s g) Hν.νS
  shell : ∀ v, v ∉ S → (Summable fun n : ℕ => ‖shellN c χ s v n‖) ∧
    ‖(∑' n : ℕ, shellN c χ s v n) - 1‖ ≤ placeBound v ∧ ∑' n : ℕ, ‖shellN c χ s v n‖ ≤ 1 + placeBound v

private theorem integrableOn_and_setIntegral_eq {c : HeightOneSpectrum (𝓞 K) → ℂ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    {Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)} {s : ℂ}
    (D : PassageData c S W χ g Hν s) (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) :
    IntegrableOn (zetaFn W χ s g)
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
        (NumberField.Idele.idelicHaar ℚ) ∧
      (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
          zetaFn W χ s g a ∂(NumberField.Idele.idelicHaar ℚ)) =
        (Hν.c : ℂ) * (∫ a, zetaFn W χ s g a ∂Hν.νS) * (L.map fun v => ∑' n : ℕ, shellN c χ s v n).prod := by
  have hφ : ∀ v ∈ L, Summable fun m : ℤ => ‖shellAt c χ s v m‖ :=
    fun v hv => summable_norm_shellAt c χ s v (D.shell v (hLS v hv)).1
  have htone := Hν.tonelli L hLS hL (zetaFn W χ s g) (fun v m => shellAt c χ s v m) D.integrableS hφ
  have hmeas := Hν.measurableSet L hLS hL
  have heq : Set.EqOn (fun a => zetaFn W χ s g (Hν.projS a) * (L.map fun v => shellAt c χ s v (Hν.ord v a)).prod)
      (zetaFn W χ s g)
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    fun a ha => (D.pointwise L hLS hL a ha).symm
  refine ⟨htone.1.congr_fun heq hmeas, ((setIntegral_congr_fun hmeas heq).symm.trans htone.2).trans ?_⟩
  congr 1
  refine congrArg List.prod (List.map_congr_left fun v hv => ?_)
  exact tsum_shellAt c χ s v (D.shell v (hLS v hv)).1

private theorem setIntegral_norm_le {c : HeightOneSpectrum (𝓞 K) → ℂ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    {Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)} {s : ℂ}
    (D : PassageData c S W χ g Hν s) (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) :
    (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        ‖zetaFn W χ s g a‖ ∂(NumberField.Idele.idelicHaar ℚ)) ≤
      Hν.c * (∫ a, ‖zetaFn W χ s g a‖ ∂Hν.νS) * Real.exp (∑' v : HeightOneSpectrum (𝓞 ℚ), placeBound v) := by
  classical
  have hmeas := Hν.measurableSet L hLS hL
  have hpt : Set.EqOn (fun a => ((‖zetaFn W χ s g a‖ : ℝ) : ℂ))
      (fun a => ((‖zetaFn W χ s g (Hν.projS a)‖ : ℝ) : ℂ) *
        (L.map fun v => ((‖shellAt c χ s v (Hν.ord v a)‖ : ℝ) : ℂ)).prod)
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro a ha
    dsimp only
    rw [D.pointwise L hLS hL a ha, norm_mul, List.norm_prod, Complex.ofReal_mul, ofReal_map_prod]
    simp only [List.map_map, Function.comp_def]
  have hφ : ∀ v ∈ L, Summable fun m : ℤ => ‖((‖shellAt c χ s v m‖ : ℝ) : ℂ)‖ := by
    intro v hv
    simpa using summable_norm_shellAt c χ s v (D.shell v (hLS v hv)).1
  have htone := Hν.tonelli L hLS hL (fun a => ((‖zetaFn W χ s g a‖ : ℝ) : ℂ))
    (fun v m => ((‖shellAt c χ s v m‖ : ℝ) : ℂ)) D.integrableS.norm.ofReal hφ
  have hC : ((∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ‖zetaFn W χ s g a‖ ∂(NumberField.Idele.idelicHaar ℚ) : ℝ) : ℂ) =
      (Hν.c : ℂ) * ((∫ a, ‖zetaFn W χ s g a‖ ∂Hν.νS : ℝ) : ℂ) *
        (L.map fun v => ((∑' m : ℤ, ‖shellAt c χ s v m‖ : ℝ) : ℂ)).prod :=
    calc ((∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ‖zetaFn W χ s g a‖ ∂(NumberField.Idele.idelicHaar ℚ) : ℝ) : ℂ)
        = ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ((‖zetaFn W χ s g a‖ : ℝ) : ℂ) ∂(NumberField.Idele.idelicHaar ℚ) :=
          integral_ofReal.symm
      _ = ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), (((‖zetaFn W χ s g (Hν.projS a)‖ : ℝ) : ℂ) *
              (L.map fun v => ((‖shellAt c χ s v (Hν.ord v a)‖ : ℝ) : ℂ)).prod) ∂(NumberField.Idele.idelicHaar ℚ) :=
          setIntegral_congr_fun hmeas hpt
      _ = (Hν.c : ℂ) * (∫ a, ((‖zetaFn W χ s g a‖ : ℝ) : ℂ) ∂Hν.νS) *
            (L.map fun v => ∑' m : ℤ, ((‖shellAt c χ s v m‖ : ℝ) : ℂ)).prod := htone.2
      _ = (Hν.c : ℂ) * ((∫ a, ‖zetaFn W χ s g a‖ ∂Hν.νS : ℝ) : ℂ) *
            (L.map fun v => ((∑' m : ℤ, ‖shellAt c χ s v m‖ : ℝ) : ℂ)).prod := by
          simp only [integral_complex_ofReal, Complex.ofReal_tsum]
  have hreal : (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ‖zetaFn W χ s g a‖ ∂(NumberField.Idele.idelicHaar ℚ)) =
      Hν.c * (∫ a, ‖zetaFn W χ s g a‖ ∂Hν.νS) * (L.map fun v => ∑' m : ℤ, ‖shellAt c χ s v m‖).prod := by
    apply Complex.ofReal_injective
    rw [hC, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_map_prod]
  have hbound : (L.map fun v => ∑' m : ℤ, ‖shellAt c χ s v m‖).prod ≤
      Real.exp (∑' v : HeightOneSpectrum (𝓞 ℚ), placeBound v) := by
    rw [← List.prod_toFinset _ hL]
    refine (Finset.prod_le_prod (fun v _ => tsum_nonneg fun m => norm_nonneg _) fun v hv => ?_).trans
      (prod_one_add_le_exp_tsum placeBound_nonneg summable_placeBound _)
    have hvL : v ∈ L := List.mem_toFinset.1 hv
    rw [tsum_norm_shellAt c χ s v (D.shell v (hLS v hvL)).1]
    exact (D.shell v (hLS v hvL)).2.2
  rw [hreal]
  exact mul_le_mul_of_nonneg_left hbound (mul_nonneg Hν.c_pos.le (integral_nonneg fun a => norm_nonneg _))

private theorem hasProd_and_integrable_and_integral_eq {c : HeightOneSpectrum (𝓞 K) → ℂ}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} {Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)} {s : ℂ}
    (D : PassageData c S W χ g Hν s) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => ∑' n : ℕ, shellN c χ s v.1 n)
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∑' n : ℕ, shellN c χ s v.1 n) ∧
      Integrable (zetaFn W χ s g) (NumberField.Idele.idelicHaar ℚ) ∧
      (∫ a, zetaFn W χ s g a ∂(NumberField.Idele.idelicHaar ℚ)) =
        (Hν.c : ℂ) * (∫ a, zetaFn W χ s g a ∂Hν.νS) *
          ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∑' n : ℕ, shellN c χ s v.1 n := by
  classical
  have hplaces : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
    NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ (by norm_num)
  have hN1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), 1 ≤ Ideal.absNorm v.asIdeal :=
    fun v => le_trans one_le_two (two_le_absNorm v)
  have hfin : ∀ n : ℕ, {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ≤ n}.Finite :=
    finite_setOf_le_of_summable_rpow_neg hN1 hplaces
  set Lf : ℕ → List (HeightOneSpectrum (𝓞 ℚ)) :=
    fun n => ((hfin n).toFinset.filter fun v => v ∉ S).toList with hLf
  have hmem : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)), v ∈ Lf n ↔ Ideal.absNorm v.asIdeal ≤ n ∧ v ∉ S := by
    intro n v
    simp only [hLf, Finset.mem_toList, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hLS : ∀ n : ℕ, ∀ v ∈ Lf n, v ∉ S := fun n v hv => ((hmem n v).1 hv).2
  have hLnd : ∀ n : ℕ, (Lf n).Nodup := fun n => Finset.nodup_toList _
  have hcov : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ S → Ideal.absNorm v.asIdeal ≤ n → v ∈ Lf n :=
    fun n v hvS hle => (hmem n v).2 ⟨hle, hvS⟩
  have hmono : ∀ n : ℕ, Lf n ⊆ Lf (n + 1) := by
    intro n v hv
    exact (hmem (n + 1) v).2 ⟨((hmem n v).1 hv).1.trans (Nat.le_succ n), ((hmem n v).1 hv).2⟩
  have hTmono := monotone_coe_unitIdelesOutside ℚ S Lf hmono
  have hUn := iUnion_coe_unitIdelesOutside_eq_univ ℚ S Lf hcov
  have hmult : Multipliable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => ∑' n : ℕ, shellN c χ s v.1 n :=
    multipliable_subtype_of_summable (fun v => v ∉ S) summable_placeBound fun v hv => (D.shell v hv).2.1
  have hprod := hmult.hasProd
  have hpass := integrable_and_tendsto_setIntegral_of_monotone_of_iUnion_eq_univ hTmono hUn
    (fun n => (integrableOn_and_setIntegral_eq D (Lf n) (hLS n) (hLnd n)).1)
    (fun n => setIntegral_norm_le D (Lf n) (hLS n) (hLnd n))
  have hlim : Filter.Tendsto
      (fun n : ℕ => ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), zetaFn W χ s g a ∂(NumberField.Idele.idelicHaar ℚ)) Filter.atTop
      (nhds ((Hν.c : ℂ) * (∫ a, zetaFn W χ s g a ∂Hν.νS) *
        ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∑' n : ℕ, shellN c χ s v.1 n)) := by
    simp only [fun n => (integrableOn_and_setIntegral_eq D (Lf n) (hLS n) (hLnd n)).2]
    exact (tendsto_prod_toList_filter_of_hasProd (fun v => v ∉ S) (fun v => ∑' n : ℕ, shellN c χ s v n) hprod
      (fun v => Ideal.absNorm v.asIdeal) hfin).const_mul _
  exact ⟨hprod, hpass.1, tendsto_nhds_unique hpass.2 hlim⟩

end Passage

end
end LanglandsTunnell.CubicInduction.EulerProductOutsideS

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart.LanglandsTunnell.CubicInduction in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
theorem solution
    {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v))
    (hψ0 : ∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)
    (hsph : ∀ v, v ∉ S → HasSphericalTorusValuesAt c v (Wloc v))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (τ : ℝ)
    (hτ : ∀ v, v ∉ S →
      ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v, v ∉ S →
      ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (hS : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        Hν.νS) :
    ∃ L : ℂ → ℂ, ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          (∑' n : ℕ,
            sphericalTorusValue (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v.1)
                (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v.1)
                (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v.1) n *
              (((χ (uniformizerIdele ℚ v.1) : ℂˣ) : ℂ) * cNormQ v.1 ^ (-s)) ^ n))
        (L s) ∧
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        (NumberField.Idele.idelicHaar ℚ) ∧
      globalZeta30 W χ s g =
        (Hν.c : ℂ) *
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
            ∂Hν.νS) *
          L s := by
  have _ := hψ0
  refine ⟨fun s => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∑' n : ℕ, EulerProductOutsideS.shellN c χ s v.1 n,
    fun s hs => ?_⟩
  have D : EulerProductOutsideS.PassageData c S W χ g Hν s :=
    { pointwise := fun L hLS hL a ha =>
        EulerProductOutsideS.zetaFn_eq_mul_prod_shellAt c ψ S W Warch Wloc hfac hK hlaw hψ1 hsph χ hχU g hg Hν s L hLS
          hL a ha
      integrableS := hS s hs
      shell := fun v hv =>
        EulerProductOutsideS.shell_data c χ v τ (hτ v hv) κ hκ0 (hκ v hv) s (hσ₀.trans hs.le) }
  obtain ⟨h1, h2, h3⟩ := EulerProductOutsideS.hasProd_and_integrable_and_integral_eq D
  exact ⟨h1, h2, h3⟩

end S_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart (solution)
