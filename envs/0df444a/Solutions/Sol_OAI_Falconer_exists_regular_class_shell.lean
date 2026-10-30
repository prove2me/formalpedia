-- Prove2me | solution 1 for OAI.Falconer.exists_regular_class_shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:20:59.316151+00:00
-- url     : https://prove2.me/submissions/33bb9686-aea3-419a-9aa1-65f78caf7465

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_two_profile_masked_shell_order
import Theorems.Thm_OAI_Falconer_exists_uniform_outer_angular_decay

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientMaskProductBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial mixed-derivative cost of an actual finite mask product

The zeroth-order bound is one. Consequently no constant is raised to the
number of descriptors: order `k` costs only `card^k`.
-/

namespace Falconer
open scoped ContDiff

variable {E A ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A] [DecidableEq ι]

theorem ambient_mask_product_derivatives (S : Finset ι) (f : ι → E → A)
    {D : ℝ} (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*D)^k := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a S ha ih =>
    have hfs : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbs : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k :=
      fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hih := ih hfs hbs
    intro k hk
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfp : ContDiff ℝ ∞ (fun z => ∏ i ∈ S, f i z) := contDiff_prod hfs
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfa hfp x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (k+1), (k.choose l : ℝ)*D^l*((S.card : ℝ)*D)^(k-l) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a (Finset.mem_insert_self _ _) l (hlk.trans hk))
            (Nat.cast_nonneg _))
          (hih (k-l) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      _ = (D+(S.card : ℝ)*D)^k := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by congr 1; ring

/-- A fixed positive-order derivative constant is absorbed into each
differentiated mask's scale, never into every undifferentiated mask. -/
theorem ambient_mask_product_budget (S : Finset ι) (f : ι → E → A)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (hzero : ∀ i ∈ S, ‖f i x‖ ≤ 1)
    (hb : ∀ i ∈ S, ∀ k, 1 ≤ k → k ≤ K → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C*D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*C*D)^k := by
  have hscaled : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ (C*D)^k := by
    intro i hi k hk
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero,pow_zero] using hzero i hi
    | succ k =>
      apply (hb i hi (k+1) (by omega) hk).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hC (by omega)) (pow_nonneg hD _)
  simpa only [mul_assoc] using ambient_mask_product_derivatives S f
    (mul_nonneg (zero_le_one.trans hC) hD) K x hf hscaled

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

 theorem descriptorAmbientProduct_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) :
    ContDiff ℝ ∞ (descriptorAmbientProduct Q ρ m N σ J i B S x) :=
  contDiff_prod (fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GlobalDescriptorBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global derivative budgets for actual descriptor products

The constants are chosen before the scale, cells, descriptor list and cap
families.  The only list-size loss is a power of its cardinality.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer

theorem descriptorAmbientProduct_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  classical
  choose A hA hAb using fun k => descriptorAmbientMask_global_derivatives d k
  let C := 1+∑ k ∈ Finset.range (K+1), A k
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (K+1)) => hA k)]
  have hAC (k : ℕ) (hk : k ≤ K) : A k ≤ C := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.range (K+1)) => hA k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z
  apply ambient_mask_product_budget B
    (fun b => descriptorAmbientMask Q ρ m N σ J i b (S b) x) hC hD K z
  · exact fun b _ => descriptorAmbientMask_contDiff Q ρ m N σ J i b (S b) x
  · intro b _
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b (S b) x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · intro b hb k _ hk
    apply (hAb k Q ρ m N σ J i b (S b) (hsep b hb) x z).trans
    exact mul_le_mul (hAC k hk)
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) (hscale b hb) k)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)
      (zero_le_one.trans hC)

theorem descriptorAmbientProduct_complex_global_budget (d K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
      (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
      (D : ℝ), 0 ≤ D →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ B, (descriptorMaskRadius N σ b)⁻¹ ≤ D) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w =>
          (descriptorAmbientProduct Q ρ m N σ J i B S x w : ℂ)) z‖ ≤
          ((B.card : ℝ)*C*D)^k := by
  obtain ⟨C,hC,hCb⟩ := descriptorAmbientProduct_global_budget d K
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i B S D hD hsep hscale x z k hk
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((descriptorAmbientProduct_contDiff Q ρ m N σ J i B S x).contDiffAt (x := z))
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘
    descriptorAmbientProduct Q ρ m N σ J i B S x) z‖ ≤ _
  rw [hn]
  exact hCb Q ρ m N σ J i B S D hD hsep hscale x z k hk

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorDerivativeScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derivative scale for the actual descriptor family

The fixed derivative constants and polynomial list size are absorbed before
choosing any cells, net points or descriptor family. The retained scale
remembers the largest nominal descriptor length.
-/

namespace Falconer
open Set MeasureTheory

theorem descriptorDerivativeScale_ge_one (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) :
    1 ≤ descriptorDerivativeScale N σ L := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) hσ
  · exact le_max_left _ _

theorem uniform_descriptor_global_scale (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (f : ℝ → ℝ) (J i L : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
      (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      B.card ≤ (N+1)^P → (∀ b ∈ B, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ B, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
        descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x z : Space d, ∀ k ≤ K,
        ‖iteratedFDeriv ℝ k (fun w => (descriptorAmbientProduct Q ρ f N σ J i B S x w : ℂ)) z‖ ≤
          (descriptorDerivativeScale N σ L)^k := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientProduct_complex_global_budget d K
  obtain ⟨N₁,hcount⟩ := descriptor_count_subpower P (half_pos hσ)
  obtain ⟨N₂,hconst⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) (8*C)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q ρ f J i L B S hcard hlength hsep x z k hk
  let W := max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))
  have hW : 0 ≤ W := (zero_le_one.trans (le_max_left _ _))
  have hc := hcount N ((le_max_left _ _).trans hN) B hcard
  have hC' := hconst N ((le_max_right _ _).trans hN)
  have hs : (B.card:ℝ)*C*(8*W) ≤ descriptorDerivativeScale N σ L := by
    calc
      _ = ((B.card:ℝ)*(8*C))*W := by ring
      _ ≤ (((2:ℝ)^N)^(σ/2)*((2:ℝ)^N)^(σ/2))*W :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc hC' (by positivity) (by positivity)) hW
      _ = descriptorDerivativeScale N σ L := by
        rw [← Real.rpow_add (by positivity),show σ/2+σ/2 = σ by ring]
        rfl
  have hb := hbound Q ρ f N σ J i B S (8*W) (by positivity) hsep
    (fun b hb => descriptorMaskRadius_inv_le N σ b (hlength b hb)) x z k hk
  exact hb.trans (pow_le_pow_left₀ (by positivity) hs k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorInverseRegime
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual descriptor derivative scale is in the inverse regime

The high-frequency condition and the retained descriptor length give a
uniform gap between the squared derivative scale and the oscillation.
The fixed shell factor four is absorbed before selecting any cells.
-/

namespace Falconer

theorem descriptorDerivativeScale_inverse_regime (N L : ℕ) {σ q : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hLN : L ≤ N)
    (hq : 20*σ*(N : ℝ) ≤ q) (hL : (L : ℝ) ≤ q/2+σ*(N : ℝ)) :
    1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      (descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q ≤ ((2 : ℝ)^N)^(-18*σ) :=
  ⟨descriptorDerivativeScale_ge_one N hσ.le L,
    descriptorDerivativeScale_le_square N L hσ.le hσ1 hLN,
    descriptorDerivativeScale_inverse_ratio N L hσ.le hq hL⟩

theorem eventual_descriptor_inverse_frequency {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (q Λ : ℝ), L ≤ N →
      20*σ*(N : ℝ) ≤ q → (L : ℝ) ≤ q/2+σ*(N : ℝ) →
      (2 : ℝ)^q/4 ≤ Λ →
      1 ≤ descriptorDerivativeScale N σ L ∧
      descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 ∧
      1 ≤ Λ ∧ (descriptorDerivativeScale N σ L)^2/Λ ≤ ((2 : ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ 4
  refine ⟨N₀,?_⟩
  intro N hN L q Λ hLN hq hL hΛ
  obtain ⟨hD,hDupper,hratio⟩ := descriptorDerivativeScale_inverse_regime N L hσ hσ1 hLN hq hL
  have hσN : 0 ≤ σ*(N : ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hRq : ((2 : ℝ)^N)^σ ≤ (2 : ℝ)^q := by
    rw [dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hfour : 4 ≤ (2 : ℝ)^q := (hN₀ N hN).trans hRq
  have hΛ1 : 1 ≤ Λ := (by linarith : (1 : ℝ) ≤ (2 : ℝ)^q/4).trans hΛ
  refine ⟨hD,hDupper,hΛ1,?_⟩
  calc
    _ ≤ (descriptorDerivativeScale N σ L)^2/((2 : ℝ)^q/4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΛ
    _ = 4*((descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q) := by ring
    _ ≤ 4*((2 : ℝ)^N)^(-18*σ) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ ((2 : ℝ)^N)^σ*((2 : ℝ)^N)^(-18*σ) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2 : ℝ)^N)^(-17*σ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

theorem dyadic_shell_frequency_lower {a v r : ℝ} (hr : (2 : ℝ)^v/4 ≤ r) :
    (2 : ℝ)^(v-a)/4 ≤ r*(2 : ℝ)^(-a) := by
  calc
    _ = ((2 : ℝ)^v/4)*(2 : ℝ)^(-a) := by
      rw [div_mul_eq_mul_div,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial term count in the individual-mask inverse expansion -/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [Fintype ι] in
theorem card_sum {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E) :
    Fintype.card (sum S).index = ∑ j, Fintype.card (S j).index :=
  Fintype.card_sigma

theorem card_derivative [DecidableEq ι] (S : MaskJetExpansion ι d E) (v : E) :
    Fintype.card (S.derivative v).index =
      Fintype.card S.index * (1+Fintype.card ι*d) := by
  change Fintype.card (S.index × (Unit ⊕ (ι × Fin d))) = _
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_unique (α := Unit),Fintype.card_prod,
    Fintype.card_fin]

theorem card_laplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) :
    Fintype.card (S.laplacian v).index =
      Fintype.card S.index * n * (1+Fintype.card ι*d)^2 := by
  rw [laplacian,card_sum]
  simp_rw [card_derivative]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem card_iteratedLaplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) (j : ℕ) :
    Fintype.card (S.iteratedLaplacian v j).index =
      Fintype.card S.index * n^j * (1+Fintype.card ι*d)^(2*j) := by
  induction j with
  | zero =>
    change Fintype.card S.index = _
    simp only [Nat.mul_zero,pow_zero,Nat.mul_one]
  | succ j ih =>
    change Fintype.card (((fun T : MaskJetExpansion ι d E => T.laplacian v)^[j+1]) S).index = _
    rw [Function.iterate_succ_apply',card_laplacian]
    change Fintype.card (S.iteratedLaplacian v j).index * _ * _ = _
    rw [ih,show 2*(j+1)=2*j+2 by omega,pow_add,pow_succ]
    ring

theorem card_stationaryJet [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.stationaryJet m j).index =
      Fintype.card S.index * (m+2)^j * (1+Fintype.card ι*d)^(2*j) := by
  change Fintype.card
    ((((S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulFixed
      (SmoothSeparation.stationaryJointDensity m)
      (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian
        (verticalDirections (m+2)) j)).index = _
  rw [card_iteratedLaplacian]
  rfl

theorem card_inverse [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.inverse m j).index =
      Fintype.card S.index * inverseMultiplicity (m+2) j *
        (1+Fintype.card ι*d)^(2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [MaskJetExpansion.inverse,inverseMultiplicity]
    | succ j =>
      rw [MaskJetExpansion.inverse,card_mulFixed,card_sum,inverseMultiplicity]
      simp_rw [card_stationaryJet]
      have hterm (h : Fin (j+1)) :
          Fintype.card (S.inverse m (j-h)).index * (m+2)^((h:ℕ)+1) *
            (1+Fintype.card ι*d)^(2*((h:ℕ)+1)) =
          Fintype.card S.index * (1+Fintype.card ι*d)^(2*(j+1)) *
            (inverseMultiplicity (m+2) (j-h) * (m+2)^((h:ℕ)+1)) := by
        rw [ih (j-h) (by have hh := h.isLt; omega)]
        have hp : 2*(j-h)+2*((h:ℕ)+1) = 2*(j+1) := by have hh := h.isLt; omega
        rw [← hp,pow_add]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SeededInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse acting on already normalized individual jets

Only the additional derivative orders enter the extracted radius weight.
The formula also permits a complex angular multiplier as a separate label.
-/

namespace Falconer
open scoped ContDiff

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

/-- Term count is unchanged by the initial derivative orders. -/
theorem card_inverse_seed (m j : ℕ) (k : ι → MaskJetIndex (m+3)) :
    Fintype.card ((seed k).inverse m j).index =
      inverseMultiplicity (m+2) j * (1+Fintype.card ι*(m+3))^(2*j) := by
  rw [card_inverse]
  change Fintype.card Unit * _ * _ = _
  rw [Fintype.card_unique,one_mul]

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateOperations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root symbols and Fourier operations in the exact descriptor class -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped ContDiff

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem spatialMultiplier_value (f : DescriptorJetSymbol n K L F D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (f.spatialMultiplier c hc hcb).value Q ρ m N σ J i S A x w =
      c x*f.value Q ρ m N σ J i S A x w := by
  simp only [value,multiplier,spatialMultiplier]
  ring

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseClassExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact inverse expansion in the recursive symbol class

The finite family is constructed from the actual differentiated masks.
Its constants are uniform in both descriptor lists, and the output keeps
the two original spatial multipliers and the remaining smoothness budget.
-/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

theorem card_descriptorInverseIndex
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ) :
    Fintype.card (DescriptorInverseIndex f g j) =
      MaskJetExpansion.inverseMultiplicity (m+2) j *
        (1+(2+F.card+G.card)*(m+3))^(2*j) := by
  rw [MaskJetExpansion.card_inverse_seed]
  simp only [DescriptorInverseLabel,Fintype.card_sum,Fintype.card_unique,
    Fintype.card_coe]
  congr 2
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarErrorBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the scalar shell's fixed cost and squared remainder

The shell width costs at most one power of R. Selecting the stationary
accuracy before scale therefore absorbs the square and the fixed constants.
-/

namespace Falconer

theorem eventual_scalar_shell_error_budget (T : ℝ) {C W : ℝ}
    (_hC : 0 ≤ C) (hW : 0 ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q ε : ℝ, q ≤ N → 0 ≤ ε →
      ε ≤ C*((2:ℝ)^N)^(-((T+2)/2)) →
      2*(2:ℝ)^q*ε^2*W ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by norm_num : (0:ℝ) < 1) (2*C^2*W)
  refine ⟨N₀,?_⟩
  intro N hN q ε hq hε hbound
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hqR : (2:ℝ)^q ≤ R := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq
  have hconst : 2*C^2*W ≤ R := by simpa only [Real.rpow_one] using hN₀ N hN
  have he : ε^2 ≤ C^2*R^(-(T+2)) := by
    have hpow := pow_le_pow_left₀ hε hbound 2
    convert hpow using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_pow,← Real.rpow_mul_natCast hR.le]
    congr 2
    ring
  calc
    _ ≤ 2*R*(C^2*R^(-(T+2)))*W := by gcongr
    _ = (2*C^2*W)*R*R^(-(T+2)) := by ring
    _ ≤ R*R*R^(-(T+2)) := by gcongr
    _ = R^(-T) := by
      rw [← sq,← Real.rpow_two,← Real.rpow_add hR]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedDescriptorFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One normalized descriptor inverse family for every large scale

The operator, its finite index set, and all constants are chosen before the
scale label. Every original descriptor remains in the support condition.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem equal_scale_product_derivatives {d K : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (B C : Space d → ℂ) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hb : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k B x‖ ≤ D^k)
    (hc : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k C x‖ ≤ D^k) :
    ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k (fun z => B z*C z) x‖ ≤ (2 : ℝ)^K*D^k := by
  classical
  let f : Fin 2 → Space d → ℂ := fun i => if i = 0 then B else C
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ContDiff ℝ ∞ (f i) := by
    intro i _
    fin_cases i
    · simpa [f] using hB
    · simpa [f] using hC
  intro k hk x
  have hfb : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ l ≤ K,
      ‖iteratedFDeriv ℝ l (f i) x‖ ≤ D^l := by
    intro i _ l hl
    fin_cases i
    · simpa [f] using hb l hl x
    · simpa [f] using hc l hl x
  have h := ambient_mask_product_derivatives Finset.univ f hD K x hf hfb k hk
  have hprod : (fun z => ∏ i : Fin 2, f i z) = fun z => B z*C z := by
    funext z
    simp [Fin.prod_univ_two,f]
  rw [hprod] at h
  have htwo : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  rw [htwo,mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (pow_nonneg hD _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DescriptorShellRegime
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual source shell satisfies the descriptor stationary regime -/

namespace Falconer
open Set MeasureTheory

theorem source_shell_frequency_bounds (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      (2:ℝ)^v/4 < r ∧ r < 4*(2:ℝ)^v := by
  have hn : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      Ψ (r/(2:ℝ)^v) ≠ 0 := by
    unfold PlanarFalconer.sourceAngularShellMeasure
    apply (ae_withDensity_iff (by fun_prop)).mpr
    filter_upwards with r hr
    intro hz
    apply hr
    simp only [hz,zero_div,ENNReal.ofReal_zero]
  filter_upwards [hn] with r hr
  have h := hsupp _ hr
  constructor
  · have hl := (lt_div_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.1
    linarith
  · exact (div_lt_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.2

theorem eventual_descriptor_source_shell_regime {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        1 ≤ r*(2:ℝ)^(-a) ∧
        (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
        r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a) ∧
        (descriptorDerivativeScale N σ L)^2/(r*(2:ℝ)^(-a)) ≤ ((2:ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := eventual_descriptor_inverse_frequency hσ hσ1
  refine ⟨N₀,?_⟩
  intro N hN L a v hLN hq hL
  filter_upwards [source_shell_frequency_bounds v Ψ hΨ hsupp] with r hr
  obtain ⟨hD,hDu,hΛ,hR⟩ := hN₀ N hN L (v-a) (r*(2:ℝ)^(-a)) hLN hq hL
    (dyadic_shell_frequency_lower hr.1.le)
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  have hsmall : ((2:ℝ)^N)^(-17*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  refine ⟨hD,hDu,hΛ,(div_le_one hΛpos).mp (hR.trans hsmall),?_,hR⟩
  calc
    _ ≤ (4*(2:ℝ)^v)*(2:ℝ)^(-a) :=
      mul_le_mul_of_nonneg_right hr.2.le (by positivity)
    _ = 4*(2:ℝ)^(v-a) := by
      rw [mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 2

theorem eventually_separated_inverse_frequency {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D r s t : ℝ, 1 ≤ D → 0 < s → δ ≤ t/s →
      0 < r*s → D^2/(r*s) ≤ ((2:ℝ)^N)^(-17*σ) →
      1 ≤ r*t ∧ D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ δ⁻¹
  refine ⟨N₀,?_⟩
  intro N hN D r s t hD hs ht hΛ hratio
  have hr : 0 < r := (mul_pos_iff_of_pos_right hs).mp hΛ
  have hst : δ*s ≤ t := (le_div_iff₀ hs).mp ht
  have hδΛ : 0 < (r*s)*δ := mul_pos hΛ hδ
  have hlower : (r*s)*δ ≤ r*t := by nlinarith [mul_le_mul_of_nonneg_left hst hr.le]
  have hrt : 0 < r*t := hδΛ.trans_le hlower
  have hbound : D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
    calc
      _ ≤ D^2/((r*s)*δ) := div_le_div_of_nonneg_left (sq_nonneg _) hδΛ hlower
      _ = δ⁻¹*(D^2/(r*s)) := by ring
      _ ≤ δ⁻¹*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hδ.le)
      _ ≤ ((2:ℝ)^N)^σ*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
      _ = ((2:ℝ)^N)^(-16*σ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
  have hsmall : ((2:ℝ)^N)^(-16*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  exact ⟨(one_le_pow₀ hD).trans ((div_le_one hrt).mp (hbound.trans hsmall)),hbound⟩


theorem eventual_descriptor_pair_shell_regime {d : ℕ} {σ δ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ (μ ν : Measure (Space d)),
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/(2:ℝ)^(-a)) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        (0 < r*(2:ℝ)^(-a) ∧
          (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
          r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a)) ∧
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧
          (descriptorDerivativeScale N σ L)^2/(r*dist z.1 z.2) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₁,hN₁⟩ := eventual_descriptor_source_shell_regime hσ hσ1 Ψ hΨ hsupp
  obtain ⟨N₂,hN₂⟩ := eventually_separated_inverse_frequency hσ hδ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN L a v hLN hq hL μ ν hsep
  filter_upwards [hN₁ N ((le_max_left _ _).trans hN) L a v hLN hq hL] with r hr
  obtain ⟨hD,hDu,hΛ,hDΛ,hΛu,hratio⟩ := hr
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  refine ⟨hD,hDu,⟨hΛpos,hDΛ,hΛu⟩,?_⟩
  filter_upwards [hsep] with z hz
  exact hN₂ N ((le_max_right _ _).trans hN) _ r ((2:ℝ)^(-a)) (dist z.1 z.2)
    hD (by positivity) hz hΛpos hratio

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously choosing the small outer-shell parameters -/

namespace Falconer

 theorem exists_outer_shell_parameters (m : ℕ) {χ : ℝ} (hχ : 0 < χ) :
    ∃ β κ σ lam η T : ℝ,
      0 < β ∧ 0 < κ ∧ κ ≤ 1 ∧ κ ≤ 1/1000 ∧ 0 < σ ∧ σ < κ/1000 ∧
      0 < lam ∧ lam ≤ σ ∧ 0 < η ∧ η ≤ 1 ∧
      4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1 ∧
      (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T ∧ β/2 ≤ T ∧
      β+((m+3:ℕ)+4)*lam < χ/4 ∧
      ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8 := by
  let d : ℝ := (m+3:ℕ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let β := min (χ/16) (1/16)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβχ : β ≤ χ/16 := min_le_left _ _
  have hβ1 : β ≤ 1/16 := min_le_right _ _
  let κ := min (1/2000) (β/(32000*(d+1)))
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκsmall : κ ≤ 1/2000 := min_le_left _ _
  have hκβ : κ*(32000*(d+1)) ≤ β :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let r : ℝ := 2*d+3
  let g : ℝ := (1000*(d+1)+32*d)+4*(d+1)+(d+4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  let b : ℝ := min (χ/(16*(d+4))) (min (κ/2000)
    (min (1/(8000*r)) (min (β*κ/(128000000*r)) (β/(128*g)))))
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨σ,hσ,hσb⟩ := exists_between hb
  have hσχ : σ*(16*(d+4)) ≤ χ :=
    (le_div_iff₀ (by positivity)).mp (hσb.le.trans (min_le_left _ _))
  have hσrest : σ ≤ min (κ/2000)
      (min (1/(8000*r)) (min (β*κ/(128000000*r)) (β/(128*g)))) :=
    hσb.le.trans (min_le_right _ _)
  have hσκ : σ ≤ κ/2000 := hσrest.trans (min_le_left _ _)
  have hrest := hσrest.trans (min_le_right _ _)
  have hσr : σ*(8000*r) ≤ 1 := (le_div_iff₀ (by positivity)).mp (hrest.trans (min_le_left _ _))
  have hrest' := hrest.trans (min_le_right _ _)
  have hσi : σ*(128000000*r) ≤ β*κ :=
    (le_div_iff₀ (by positivity)).mp (hrest'.trans (min_le_left _ _))
  have hσg : σ*(128*g) ≤ β :=
    (le_div_iff₀ (by positivity)).mp (hrest'.trans (min_le_right _ _))
  let η := β/64
  let T := (20/κ+1/σ)*(3*d+2)+β+20
  have hsmall : β+(d+4)*σ < χ/4 := by nlinarith
  have hreserve : dimensionalBranchReserve (m+3) σ σ+σ = r*σ := by
    dsimp [dimensionalBranchReserve,r,d]
    ring
  have hbranch : 4000*(dimensionalBranchReserve (m+3) σ σ+σ) ≤ 1 := by
    rw [hreserve]
    nlinarith
  have hfirst : 500*d*κ ≤ β/64 := by nlinarith [mul_nonneg hκ.le hd]
  have hinv : 10^6*(dimensionalBranchReserve (m+3) σ σ+σ)/κ ≤ β/128 := by
    rw [hreserve]
    apply (div_le_iff₀ hκ).mpr
    nlinarith
  have hgraph : (d+4)*σ+outerGraphLoss m σ σ ≤ β/128 := by
    have he : (d+4)*σ+outerGraphLoss m σ σ = g*σ := by
      dsimp [outerGraphLoss,g,d]
      ring
    rw [he]
    nlinarith
  refine ⟨β,κ,σ,σ,η,T,hβ,hκ,by linarith,by linarith,hσ,by linarith,hσ,le_rfl,
    by dsimp [η]; positivity,by dsimp [η]; linarith,hbranch,?_,?_,hsmall,?_⟩
  · change (20/κ+1/σ)*(3*d+2)+10 < (20/κ+1/σ)*(3*d+2)+β+20
    linarith
  · change β/2 ≤ (20/κ+1/σ)*(3*d+2)+β+20
    have hnonneg : 0 ≤ (20/κ+1/σ)*(3*d+2) := by positivity
    linarith
  · change (d+4)*σ+(500*d*κ+10^6*(dimensionalBranchReserve (m+3) σ σ+σ)/κ+η)+outerGraphLoss m σ σ ≤ β/8
    dsimp [η]
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_TwoProfileDerivatives
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One ambient derivative scale for the two original profile products -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem uniform_two_profile_derivatives (d K P : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube d) (ρ₁ ρ₂ : Measure (Space d)) (f₁ f₂ : ℝ → ℝ)
        (J i L : ℕ) (F G : Finset PolicyDescriptor)
        (S₁ S₂ : PolicyDescriptor → Finset (Sphere d)),
      F.card ≤ (N+1)^P → G.card ≤ (N+1)^P →
      (∀ b ∈ F, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ G, PlanarFalconer.descriptorLength b ≤ L) →
      (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ x y k, k ≤ K → ∀ w : Space d,
        ‖iteratedFDeriv ℝ k (fun t =>
          (descriptorAmbientProduct Q₁ ρ₁ f₁ N σ J i F S₁ x t : ℂ)*
          (descriptorAmbientProduct Q₂ ρ₂ f₂ N σ J i G S₂ y t : ℂ)) w‖ ≤
          (2:ℝ)^K*(descriptorDerivativeScale N σ L)^k := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_global_scale d K P hσ
  refine ⟨N₀,?_⟩
  intro N hN Q₁ Q₂ ρ₁ ρ₂ f₁ f₂ J i L F G S₁ S₂ hF hG hFL hGL hsepF hsepG x y k hk w
  exact equal_scale_product_derivatives
    (zero_le_one.trans (descriptorDerivativeScale_ge_one N hσ.le L)) _ _
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q₁ ρ₁ f₁ N σ J i F S₁ x))
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q₂ ρ₂ f₂ N σ J i G S₂ y))
    (fun l hl z => hN₀ N hN Q₁ ρ₁ f₁ J i L F S₁ hF hFL hsepF x z l hl)
    (fun l hl z => hN₀ N hN Q₂ ρ₂ f₂ J i L G S₂ hG hGL hsepG y z l hl)
    k hk w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TwoProfileInverseCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial cost of the actual root inverse family -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_two_profile_root_shell_cost (m k : ℕ) (A B : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F G : Finset PolicyDescriptor) (L : ℕ),
      descriptorInverseShellCost (descriptorRootSymbol (m+1) F L)
        (descriptorRootSymbol (m+1) G L) k A B 1 1 U δ W hδ hW ≤
        C*((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) := by
  let c : Fin (k+1) → ℝ := fun j => MaskJetExpansion.inverseMultiplicity (m+2) j.val
  let b : Fin (k+1) → ℝ := fun j =>
    ((|U*A j| *|U*B j| *|(1:ℝ)⁻¹| *|(1:ℝ)⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
      (spatialFourierCost (d := m+3) δ W hδ hW j.val)^2
  let C₁ : ℝ := ∑ j, c j
  let C₂ : ℝ := ∑ j, b j
  have hc (j) : 0 ≤ c j := Nat.cast_nonneg _
  have hb (j) : 0 ≤ b j := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg (fun j _ => hc j)
  have hC₂ : 0 ≤ C₂ := Finset.sum_nonneg (fun j _ => hb j)
  refine ⟨C₁^2*C₂,mul_nonneg (sq_nonneg _) hC₂,?_⟩
  intro F G L
  let f := descriptorRootSymbol (m+1) F L
  let g := descriptorRootSymbol (m+1) G L
  let I := DescriptorInverseFamilyIndex f g k
  let Q : ℝ := ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast Nat.le_add_right 1 _
  have hcard : (Fintype.card I : ℝ) ≤ C₁*Q^(2*k) := by
    have he : (Fintype.card I : ℝ) = ∑ j : Fin (k+1), c j*Q^(2*j.val) := by
      simp only [I,DescriptorInverseFamilyIndex,Fintype.card_sigma,card_descriptorInverseIndex,
        Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,c,Q]
    rw [he]
    dsimp only [C₁]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hc j)
    exact pow_le_pow_right₀ hQ (by have := j.isLt; omega)
  have hsum : (∑ z : I, b z.1) ≤ (Fintype.card I:ℝ)*C₂ := by
    calc
      _ ≤ ∑ _z : I, C₂ := Finset.sum_le_sum (fun z _ =>
        Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ z.1))
      _ = _ := by simp
  have hcost : descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW ≤
      (Fintype.card I:ℝ)^2*C₂ := by
    change (Fintype.card I:ℝ)*(∑ z : I, b z.1) ≤ _
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)).trans_eq (by ring)
  apply hcost.trans
  calc
    _ ≤ (C₁*Q^(2*k))^2*C₂ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hC₂
    _ = (C₁^2*C₂)*Q^(4*k) := by
      rw [mul_pow,← pow_mul]
      have he : 2*k*2 = 4*k := by omega
      rw [he]
      ring

theorem eventual_two_profile_root_shell_cost (m k : ℕ) (A B : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (F G : Finset PolicyDescriptor) (L : ℕ),
      F.card ≤ (N+1)^4 → G.card ≤ (N+1)^4 →
      descriptorInverseShellCost (descriptorRootSymbol (m+1) F L)
        (descriptorRootSymbol (m+1) G L) k A B 1 1 U δ W hδ hW ≤ ((2:ℝ)^N)^ε := by
  obtain ⟨C,hC,hbound⟩ := exists_two_profile_root_shell_cost m k A B U δ W hδ hW
  let H : ℝ := 1+4*(m+3:ℕ)
  obtain ⟨N₁,hN₁⟩ := PlanarFalconer.fixed_polynomial_subpower (16*k) (half_pos hε)
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed (half_pos hε) (C*H^(4*k))
  refine ⟨max N₁ N₂,?_⟩
  intro N hN F G L hF hG
  have hx : (1:ℝ) ≤ (N:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hX : (1:ℝ) ≤ ((N:ℝ)+1)^4 := one_le_pow₀ hx
  have hFc : (F.card:ℝ) ≤ ((N:ℝ)+1)^4 := by exact_mod_cast hF
  have hGc : (G.card:ℝ) ≤ ((N:ℝ)+1)^4 := by exact_mod_cast hG
  have hM : (0:ℝ) ≤ (m+3:ℕ) := Nat.cast_nonneg _
  have hQ : ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ) ≤ H*((N:ℝ)+1)^4 := by
    dsimp [H]
    push_cast at hM ⊢
    calc
      _ ≤ 1+(2+((N:ℝ)+1)^4+((N:ℝ)+1)^4)*((m:ℝ)+3) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hX)]
  have hp : ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) ≤
      H^(4*k)*((N:ℝ)+1)^(16*k) := by
    calc
      _ ≤ (H*((N:ℝ)+1)^4)^(4*k) := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
      _ = _ := by rw [mul_pow,← pow_mul]; congr 2; omega
  calc
    _ ≤ C*((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) := hbound F G L
    _ ≤ (C*H^(4*k))*((N:ℝ)+1)^(16*k) := by
      convert mul_le_mul_of_nonneg_left hp hC using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ (C*H^(4*k))*(4*(N:ℝ)+1)^(16*k) := by
      gcongr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ ((2:ℝ)^N)^(ε/2)*((2:ℝ)^N)^(ε/2) :=
      mul_le_mul (hN₂ N ((le_max_right _ _).trans hN))
        (hN₁ N ((le_max_left _ _).trans hN)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SpatialRestriction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable product restrictions stay in the original endpoint jet class -/

namespace Falconer
open Set MeasureTheory

 theorem endpointTransform_restrict_indicator {d : ℕ} (μ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (S : Set (Space d)) (hS : MeasurableSet S)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict S) M b r w =
      endpointTransform μ M (fun x u => S.indicator (fun _ => (1:ℂ)) x*b x u) r w := by
  unfold endpointTransform
  rw [← integral_indicator hS]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S <;> simp [hx]

namespace DescriptorJetSymbol

 theorem restrictSpatial_endpoint {n K L : ℕ} {F : Finset PlanarFalconer.PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D) (S : Set (Space (n+2))) (hS : MeasurableSet S)
    (Q : DyadicCube (n+2)) (ρ μ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (masks : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
    (A M r : ℝ) (w : Sphere (n+2)) :
    endpointTransform μ M ((f.restrictSpatial S hS).value Q ρ profile N σ J i masks A) r w =
      endpointTransform (μ.restrict S) M (f.value Q ρ profile N σ J i masks A) r w := by
  rw [endpointTransform_restrict_indicator μ M _ S hS]
  congr 1
  funext x u
  exact f.spatialMultiplier_value _ _ _ Q ρ profile N σ J i masks A x u

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRestrictedConversion
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer scalar conversion with arbitrary measurable product restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem exists_outer_restricted_scalar_conversion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1/100) (hε : 0 < ε)
    (T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
    (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ K : ℕ, ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.σ = σ → Q.σ = σ →
      P.J = Q.J → P.i = 0 → Q.i = 0 → P.Z = Z → Q.Z = Z →
      P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N → N₀ ≤ P.N →
      ∀ c : ℕ, 2*c ≤ P.N →
      (∀ b ∈ P.outerList c, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b ∈ Q.outerList c, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier), δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier),
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      ∀ energy : ℝ, 0 ≤ energy →
      (∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
        (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
        independentAngularEnergy P.a P.t Ψ
          (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
            (profileModelMass P.profile P.N P.a)
            (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
          (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
            (profileModelMass Q.profile Q.N Q.a)
            (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤ energy) →
      (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)),
        ‖charFun (P.outerRestrictedDistance Q c A₁ A₂) r‖^2) ≤ ((2:ℝ)^P.N)^ε*energy+((2:ℝ)^P.N)^(-T) := by
  let accuracy := (T+2)/2
  obtain ⟨k,A₀,hA₀,horder⟩ := exists_two_profile_masked_shell_order hgnomonic hquadratic m
    (κ := 16*σ) (T := accuracy) (by positivity)
  let order := 2*(k+1)+(m+2)+1
  let C : ℝ := (2:ℝ)^order
  let Cerr : ℝ := δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr,C]; positivity
  obtain ⟨Nder,hder⟩ := uniform_two_profile_derivatives (m+3) order 4 hσ
  obtain ⟨Nfreq,hfreq⟩ := eventual_descriptor_pair_shell_regime (d := m+3) hσ (by linarith) hδ Ψ hΨ hsupp
  obtain ⟨Nrad,hrad⟩ := Regularization.fixed_constant_absorbed hσ 8
  obtain ⟨Ntwo,htwo⟩ := Regularization.fixed_constant_absorbed (half_pos hε) 2
  obtain ⟨Nerr,herr⟩ := eventual_scalar_shell_error_budget T hCerr
    (show 0 ≤ 4*V by positivity)
  refine ⟨2*k,?_⟩
  intro L Z hZ
  obtain ⟨A,B,hA,hB,hshell⟩ := horder L
  obtain ⟨Ncost,hcost⟩ := eventual_two_profile_root_shell_cost m k A B Z δ W hδ hW (half_pos hε)
  refine ⟨max (max Nder Nfreq) (max (max Nrad Ntwo) (max Nerr Ncost)),?_⟩
  intro P Q hN hσP hσQ hJ hiP hiQ hZP hZQ haP haQ htP htQ hlarge c hc hsepP hsepQ hsep hnear A₁ A₂ hA₁ hA₂ energy he0 henergy
  let := P.regular.probability
  let := Q.regular.probability
  let μ₀ := P.ρ.restrict (P.Q.descendant P.X).carrier
  let ν₀ := Q.ρ.restrict (Q.Q.descendant Q.X).carrier
  let μ := μ₀.restrict A₁
  let ν := ν₀.restrict A₂
  have hdom : μ.prod ν ≤ μ₀.prod ν₀ := Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hsep' : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W :=
    (ae_mono hdom) hsep
  have hnear' : ∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 :=
    (ae_mono hdom) hnear
  let ell := max (P.outerLongest c) (Q.outerLongest c)
  have hell : 2*ell ≤ P.N := by
    have hp := P.outerLongest_half hc
    have hq := Q.outerLongest_half (by omega : 2*c ≤ Q.N)
    dsimp [ell]
    omega
  have hNd : Nder ≤ P.N := by omega
  have hNf : Nfreq ≤ P.N := by omega
  have hNr : Nrad ≤ P.N := by omega
  have hNt : Ntwo ≤ P.N := by omega
  have hNe : Nerr ≤ P.N := by omega
  have hNc : Ncost ≤ P.N := by omega
  have hsp : ∀ r, 4 < r → Ψ r = 0 := by
    intro r hr
    by_contra hn
    exact (not_lt_of_ge hr.le) (hsupp r hn).2
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.N:ℝ) Ψ hV hΨV hsp
  let E := descriptorDerivativeScale P.N σ ell
  have hE : 1 ≤ E := descriptorDerivativeScale_ge_one P.N hσ.le ell
  have hEu : E ≤ ((2:ℝ)^P.N)^2 := descriptorDerivativeScale_le_square P.N ell hσ.le (by linarith) (by omega)
  have hlengthP : ∀ b ∈ P.outerList c, PlanarFalconer.descriptorLength b ≤ ell :=
    fun b hb => (Finset.le_sup hb).trans (le_max_left _ _)
  have hlengthQ : ∀ b ∈ Q.outerList c, PlanarFalconer.descriptorLength b ≤ ell :=
    fun b hb => (Finset.le_sup hb).trans (le_max_right _ _)
  have hradP : ∀ b ∈ P.outerList c, (descriptorMaskRadius P.N σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N σ b (hlengthP b hb)).trans
    exact mul_le_mul_of_nonneg_right (hrad P.N hNr) (by positivity)
  have hradQ : ∀ b ∈ Q.outerList c, (descriptorMaskRadius P.N σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N σ b (hlengthQ b hb)).trans
    exact mul_le_mul_of_nonneg_right (hrad P.N hNr) (by positivity)
  have hgap : 20*σ*(P.N:ℝ) ≤ (P.N:ℝ)-0 := by
    have hh := mul_le_mul_of_nonneg_right hσsmall (Nat.cast_nonneg (α := ℝ) P.N)
    linarith
  have hellR : (ell:ℝ) ≤ ((P.N:ℝ)-0)/2+σ*P.N := by
    have hh : 2*(ell:ℝ) ≤ P.N := by exact_mod_cast hell
    nlinarith [mul_nonneg hσ.le (Nat.cast_nonneg (α := ℝ) P.N)]
  have hfreqP := hfreq P.N hNf ell 0 P.N (by omega) hgap hellR μ ν (by simpa using hsep'.mono (fun _ hz => hz.1))
  have hd := hder P.N hNd P.Q Q.Q P.ρ Q.ρ (fun u => P.profile (u/P.N))
    (fun u => Q.profile (u/Q.N)) P.J 0 ell (P.outerList c) (Q.outerList c) P.masks Q.masks
    (P.outerList_card c) (by simpa only [hN] using Q.outerList_card c)
    hlengthP hlengthQ (by simpa only [hσP] using hsepP) (by simpa only [hσQ,← hN] using hsepQ)
  have hM : profileModelMass P.profile P.N P.a = 1 := by simp [profileModelMass,haP,P.regular.zero]
  have hP : profileModelMass Q.profile Q.N Q.a = 1 := by simp [profileModelMass,haQ,Q.regular.zero]
  have hmass : (μ.prod ν).real univ ≤ 1 := by
    have hp : μ univ ≤ 1 := (Measure.restrict_le_self univ).trans
      ((Measure.restrict_le_self univ).trans (by simp))
    have hq : ν univ ≤ 1 := (Measure.restrict_le_self univ).trans
      ((Measure.restrict_le_self univ).trans (by simp))
    rw [measureReal_def]
    apply (ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) ?_).trans_eq (by norm_num)
    rw [← univ_prod_univ,Measure.prod_prod]
    simpa only [one_mul] using mul_le_mul hp hq (by positivity) (by positivity)
  have hb := hshell ((2:ℝ)^P.N) E δ W C (one_le_pow₀ (by norm_num)) hE hEu hδ hW
    (one_le_pow₀ (by norm_num)) P.Q Q.Q P.ρ Q.ρ (fun u => P.profile (u/P.N))
    (fun u => Q.profile (u/Q.N)) P.N σ P.J 0 (P.outerList c) (Q.outerList c) P.masks Q.masks
    (by simpa only [hσP] using hsepP) (by simpa only [hσQ,← hN] using hsepQ) hradP hradQ
    μ ν 1 1 1 zero_lt_one zero_lt_one zero_lt_one (by simpa using hsep') hnear'
    (fun x y l hl w => hd x y l hl w) Z hZ 0 P.N Ψ hΨ hpos hzero hone
    (by simpa using hfreqP.mono (fun _ hr => hr.2.2.1))
    (by simpa only [E,neg_mul] using hfreqP.mono (fun _ hr => hr.2.2.2)) energy
    (by
      intro f g
      have hh := henergy (f.restrictSpatial A₁ hA₁) (g.restrictSpatial A₂ hA₂)
      simp only [DescriptorJetSymbol.restrictSpatial_endpoint] at hh
      rw [hM,hP] at hh
      simpa only [haP,haQ,Nat.cast_zero,htP,hσP,hσQ,hJ,hiP,hiQ,hZP,hZQ,← hN] using hh)
  let err : ℝ := Cerr*((2:ℝ)^P.N)^(-accuracy)*(μ.prod ν).real univ
  have her0 : 0 ≤ err := by dsimp [err]; positivity
  have her : err ≤ Cerr*((2:ℝ)^P.N)^(-((T+2)/2)) := by
    simpa only [accuracy,mul_one] using mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ Cerr*((2:ℝ)^P.N)^(-accuracy))
  have he : 2*(2:ℝ)^(P.N:ℝ)*err^2*(PlanarFalconer.sourceAngularShellMeasure (P.N:ℝ) Ψ).real univ ≤ ((2:ℝ)^P.N)^(-T) := by
    apply (mul_le_mul_of_nonneg_left
      (PlanarFalconer.sourceAngularShellMeasure_real_mass_le (P.N:ℝ) Ψ hV hΨV hsp) (by positivity)).trans
    exact herr P.N hNe P.N err le_rfl her0 her
  have hcostP := hcost P.N hNc (P.outerList c) (Q.outerList c) (L+2*k)
    (P.outerList_card c) (by simpa only [hN] using Q.outerList_card c)
  have hcoeff : 2*descriptorInverseShellCost
      (descriptorRootSymbol (m+1) (P.outerList c) (L+2*k))
      (descriptorRootSymbol (m+1) (Q.outerList c) (L+2*k)) k A B 1 1 Z δ W hδ hW ≤ ((2:ℝ)^P.N)^ε := by
    calc
      _ ≤ ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(ε/2) :=
        mul_le_mul (htwo P.N hNt) hcostP (by unfold descriptorInverseShellCost; positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hb' : (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)), ‖charFun (P.outerRestrictedDistance Q c A₁ A₂) r‖^2) ≤
      2*(descriptorInverseShellCost
        (descriptorRootSymbol (m+1) (P.outerList c) (L+2*k))
        (descriptorRootSymbol (m+1) (Q.outerList c) (L+2*k)) k A B 1 1 Z δ W hδ hW*energy)+
      2*(2:ℝ)^(P.N:ℝ)*err^2*(PlanarFalconer.sourceAngularShellMeasure (P.N:ℝ) Ψ).real univ := by
    unfold PolicyJetData.outerRestrictedDistance
    rw [hM,hP]
    simpa only [hσP,hσQ,hJ,hiP,hiQ,← hN,neg_zero,Real.rpow_zero,
      one_mul,sub_zero,inv_one,abs_one,mul_one,accuracy,err,Cerr,C,mul_assoc,μ,ν,μ₀,ν₀] using hb
  apply hb'.trans
  exact add_le_add (by nlinarith only [mul_le_mul_of_nonneg_right hcoeff he0]) he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRoot
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual regularized classes as initial policy states -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor sourcePolicyBlock sourceSmoothingLevels)

 theorem descriptorNets_cover (d N : ℕ) (σ : ℝ) (b : PolicyDescriptor) (w : Sphere d) :
    ∃ c ∈ descriptorNets d N σ b, dist w c ≤ descriptorMaskRadius N σ b/2 :=
  (Classical.choose_spec (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))).2.1 w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RegularRestrictedShell
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One entry depth works for every measurable product restriction -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_regular_outer_restricted_shell
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    {χ β : ℝ} (hχ : 0 < χ) (hβ : 0 < β)
    (hκsmall : κ ≤ 1/1000) (hTβ : β/2 ≤ T)
    (hentrySmall : β+((m+3:ℕ)+4)*lam < χ/4)
    (hdecay : ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ (Z : ℝ) (N₀ : ℕ), 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = lam → Q.lam = lam →
      P.s = (m+3:ℕ)/2+χ → Q.s = (m+3:ℕ)/2+χ →
      P.σ = σ → Q.σ = σ → P.J = sourceSmoothingLevels σ κ → Q.J = sourceSmoothingLevels σ κ →
      P.q = sourcePolicyBlock P.N κ → Q.q = sourcePolicyBlock Q.N κ →
      P.Z = Z → Q.Z = Z → P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N →
      N₀ ≤ P.N → P.i = 0 → Q.i = 0 →
      P.policy = profileExcess (d := m+3) P.profile P.N →
      Q.policy = profileExcess (d := m+3) Q.profile Q.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Q.masks b,
        dist w c ≤ descriptorMaskRadius Q.N Q.σ b/2) →
      (∀ b, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier), δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier),
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
        β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)),
        ‖charFun (P.outerRestrictedDistance Q c A₁ A₂) r‖^2) ≤ ((2:ℝ)^P.N)^(-β/16) := by
  have hσsmall : σ ≤ 1/100 := by linarith
  obtain ⟨Ks,hscalar⟩ := exists_outer_restricted_scalar_conversion hgnomonic hquadratic m hσ hσsmall
    (by positivity : 0 < β/8) (β/8) δ W hδ hW Ψ hΨ hpos hzero hone hV hΨV hsupp
  obtain ⟨K,L,Z,Na,hK,hZ,hNa,hangular⟩ := exists_uniform_outer_angular_decay
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    hχ hβ hκsmall hTβ hentrySmall hdecay φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp Ks
  obtain ⟨Ns,hscalar⟩ := hscalar L Z (zero_lt_one.trans_le hZ)
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < β/16) 2
  refine ⟨Z,max Na (max Ns Nc),hZ,by omega,?_⟩
  intro P Q hN hLamP hLamQ hsP hsQ hσP hσQ hJP hJQ hqP hqQ hZP hZQ
    haP haQ htP htQ hlarge hiP hiQ hprofileP hprofileQ hcoverP hcoverQ hsepP hsepQ hsep hnear
  have hNaP : Na ≤ P.N := by omega
  have hNsP : Ns ≤ P.N := by omega
  have hNcP : Nc ≤ P.N := by omega
  obtain ⟨c,hc,hw,hclo,henergy⟩ := hangular P Q hN hLamP hLamQ hsP hsQ hσP hσQ hJP hJQ hqP hqQ
    hZP hZQ haP haQ htP htQ hNaP hiP hiQ hprofileP hprofileQ hcoverP hcoverQ hsepP hsepQ
  refine ⟨c,hc,hw,hclo,?_⟩
  intro A₁ A₂ hA₁ hA₂
  have hb := hscalar P Q hN hσP hσQ (hJP.trans hJQ.symm) hiP hiQ hZP hZQ
    haP haQ htP htQ hNsP c (by omega) (fun b _ => hsepP b) (fun b _ => hsepQ b)
    hsep hnear A₁ A₂ hA₁ hA₂ (((2:ℝ)^P.N)^(-β/4)) (by positivity) (by
      intro f g
      exact henergy (f.relax hK le_rfl (by norm_num) le_rfl)
        (g.relax hK le_rfl (by norm_num) le_rfl))
  calc
    _ ≤ ((2:ℝ)^P.N)^(β/8)*((2:ℝ)^P.N)^(-β/4)+((2:ℝ)^P.N)^(-(β/8)) := hb
    _ = 2*((2:ℝ)^P.N)^(-β/8) := by
      rw [← Real.rpow_add (by positivity),show β/8+-β/4 = -β/8 by ring]
      ring_nf
    _ ≤ ((2:ℝ)^P.N)^(β/16)*((2:ℝ)^P.N)^(-β/8) :=
      mul_le_mul_of_nonneg_right (hNc P.N hNcP) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RegularClassShell
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform shell estimate for the original regularized class laws

The parameters are chosen before the scale and the classes. A single entry
index for each class pair works for every measurable product restriction.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff

 theorem exists_regular_class_shell_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N ((m+3:ℕ)/2+χ) lam profile₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N ((m+3:ℕ)/2+χ) lam profile₂ →
      ρ₁ Q₁.carrierᶜ = 0 → ρ₂ Q₂.carrierᶜ = 0 →
      (∀ᵐ z ∂ρ₁.prod ρ₂, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂ρ₁.prod ρ₂,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : ℕ, 4*c ≤ N ∧ c+100*PlanarFalconer.sourcePolicyBlock N κ < N ∧
        β*N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance (ρ₁.restrict A₁) (ρ₂.restrict A₂) 1 1 1
          (descriptorAmbientProduct Q₁ ρ₁ (fun u => profile₁ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₁ N κ c)
            (descriptorNets (m+3) N σ))
          (descriptorAmbientProduct Q₂ ρ₂ (fun u => profile₂ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₂ N κ c)
            (descriptorNets (m+3) N σ))) r‖^2) ≤ ((2:ℝ)^N)^(-β/16) := by
  obtain ⟨β,κ,σ,lam,η,T,hβ,hκ,hκ1,hκsmall,hσ,hgap,hlam,hlamσ,hη,hη1,hloss,hT,hTβ,hentry,hdecay⟩ :=
    exists_outer_shell_parameters m hχ
  obtain ⟨Z,N₀,hZ,hN₀,hmain⟩ := exists_regular_outer_restricted_shell hgnomonic hquadratic m
    hlam.le hσ hκ hκ1 hgap hη hη1 hloss hT hχ hβ hκsmall hTβ hentry hdecay
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp δ W hδ hW
  refine ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ profile₁ profile₂ hreg₁ hreg₂ hcarry₁ hcarry₂ hsep hnear
  have hNp : 0 < N := hN₀.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  let P := regularRoot Q₁ hQ₁ ρ₁ profile₁ (σ := σ) hreg₁ hNp hκ hZp
  let Q := regularRoot Q₂ hQ₂ ρ₂ profile₂ (σ := σ) hreg₂ hNp hκ hZp
  have hρ₁ : ρ₁.restrict Q₁.carrier = ρ₁ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcarry₁)
  have hρ₂ : ρ₂.restrict Q₂.carrier = ρ₂ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcarry₂)
  have hp : P.ρ.restrict (P.Q.descendant P.X).carrier = ρ₁ := by
    simpa only [P,regularRoot,DyadicCube.descendant_nil] using hρ₁
  have hq : Q.ρ.restrict (Q.Q.descendant Q.X).carrier = ρ₂ := by
    simpa only [Q,regularRoot,DyadicCube.descendant_nil] using hρ₂
  obtain ⟨c,hc,hw,hclo,hbound⟩ := hmain P Q rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl hN rfl rfl rfl rfl
    (descriptorNets_cover (m+3) N σ) (descriptorNets_cover (m+3) N σ)
    (descriptorNets_separated (m+3) N σ) (descriptorNets_separated (m+3) N σ)
    (by rwa [hp,hq]) (by rwa [hp,hq])
  refine ⟨c,hc,hw,hclo,?_⟩
  intro A₁ A₂ hA₁ hA₂
  have hb := hbound A₁ A₂ hA₁ hA₂
  simpa only [PolicyJetData.outerRestrictedDistance,hp,hq,P,Q,regularRoot,
    PolicyJetData.outerList,PolicyJetData.list,regularOuterList,profileModelMass,
    DyadicCube.descendant_nil,hρ₁,hρ₂,
    Nat.cast_zero,zero_div,hreg₁.zero,hreg₂.zero,neg_zero,Real.rpow_zero] using hb

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_regular_class_shell_oai := @OAI.Falconer.exists_regular_class_shell_oai
