-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.band_projected_high
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:24:20.72269+00:00
-- url     : https://prove2.me/submissions/6c3e5fd1-5700-48fe-a2a9-1ce789413a34

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_exists_finite_diagonal_high_l1
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_exists_normalized_symbol_basic_l1

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntGeometricSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric bound used on the two sides of a dyadic crossover. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem int_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    Summable (fun k : ℤ => r^k.natAbs) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  apply Summable.of_nat_of_neg
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h

theorem int_geometric_tsum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    (∑' k : ℤ, r^k.natAbs)≤2/(1-r) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  have hnat : Summable (fun n : ℕ => r^(n:ℤ).natAbs) := by simpa only [Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => r^(-n:ℤ).natAbs) := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h
  have heq : (∑' k : ℤ, r^k.natAbs)=(∑' n : ℕ, r^n)+(∑' n : ℕ, r^n)-1 := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero] using
      (hnat.tsum_of_nat_of_neg (f:=fun k : ℤ => r^k.natAbs) hneg)
  rw [heq,tsum_geometric_of_abs_lt_one (r:=r)
    (by simpa only [abs_of_nonneg hr] using hr1),div_eq_mul_inv]
  linarith

theorem int_geometric_shift_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, r^(k-a).natAbs)≤2/(1-r) := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), r^k.natAbs)=∑ k∈S, r^(k-a).natAbs :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact ((int_geometric_summable hr hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr k.natAbs)).trans
    (int_geometric_tsum_le hr hr1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeClassBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplitude levels of comparable support measure have a bounded
sum-to-energy ratio, independently of their number. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_class_bound (S : Finset ℤ) (mass : ℤ → ℝ) (m : ℝ)
    (hlow : ∀ i∈S, m ≤ mass i) (hhigh : ∀ i∈S, mass i≤2*m) :
    (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
  classical
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : j∈S := Finset.max'_mem S hS
    have hgeom := int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) S j
    have hp (i : ℤ) (hi : i∈S) : (2:ℝ)^i=(2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs := by
      have hij : i≤j := Finset.le_max' S i hi
      have hn : ((i-j).natAbs:ℤ)=j-i := by omega
      have he : (1/2:ℝ)^(i-j).natAbs=(2:ℝ)^(-((i-j).natAbs:ℤ)) := by
        simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
      rw [he,hn,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      congr 1
      omega
    have hmass (i : ℤ) (hi : i∈S) : Real.sqrt (mass i)≤Real.sqrt 2*Real.sqrt (mass j) := by
      calc
        _ ≤ Real.sqrt (2*mass j) := Real.sqrt_le_sqrt ((hhigh i hi).trans (mul_le_mul_of_nonneg_left (hlow j hj) (by norm_num)))
        _ = _ := Real.sqrt_mul (by norm_num) _
    have hs : (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
        4*Real.sqrt 2*((2:ℝ)^j*Real.sqrt (mass j)) := by
      calc
        _ ≤ ∑ i∈S, ((2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs)*(Real.sqrt 2*Real.sqrt (mass j)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hp i hi]
          exact mul_le_mul_of_nonneg_left (hmass i hi) (by positivity)
        _ = ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*(∑ i∈S, (1/2:ℝ)^(i-j).natAbs) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*4 :=
          mul_le_mul_of_nonneg_left (by norm_num at hgeom ⊢; exact hgeom) (by positivity)
        _ = _ := by ring
    have hterm : (2:ℝ)^j*Real.sqrt (mass j)≤
        Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (fun i _ => sq_nonneg ((2:ℝ)^i*Real.sqrt (mass i))) hj
    exact hs.trans (mul_le_mul_of_nonneg_left hterm (by positivity))
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.sum_empty,Real.sqrt_zero,mul_zero,le_refl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicMeasureClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support-measure class is chosen from the actual positive
measure by the integer floor of its base-two logarithm. -/
noncomputable section
namespace LipschitzHilbert

theorem dyadicMeasureClass_bounds {m : ℝ} (hm : 0 < m) :
    (2:ℝ)^(dyadicMeasureClass m) ≤ m ∧ m<(2:ℝ)^(dyadicMeasureClass m+1) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (Real.log_le_log_iff (zpow_pos (by norm_num) _) hm).mp
    rw [Real.log_zpow]
    exact (le_div_iff₀ hc).mp (Int.floor_le _)
  · apply (Real.log_lt_log_iff hm (zpow_pos (by norm_num) _)).mp
    rw [Real.log_zpow,Int.cast_add,Int.cast_one]
    exact (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual disjoint amplitude levels and their square-energy budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_finite (μ : Measure X) {f : X → E} (hf : MemLp f 2 μ) (i : ℤ) :
    μ (amplitudeLevel f i)≠∞ := by
  let eps : ℝ≥0 := ⟨(2:ℝ)^(i-1),(zpow_pos (by norm_num) _).le⟩
  have heps : eps≠0 := by
    intro h
    have := congrArg (fun t : ℝ≥0 => (t:ℝ)) h
    exact (zpow_pos (by norm_num : (0:ℝ)<2) (i-1)).ne' this
  have h := hf.meas_ge_lt_top (by norm_num) (by norm_num) heps
  apply ne_top_of_le_ne_top h.ne (measure_mono ?_)
  intro x hx
  exact_mod_cast hx.1.le

theorem amplitude_energy_budget (μ : Measure X) {f : X → E}
    (hf : MemLp f 2 μ) (hm : Measurable (fun x => ‖f x‖)) (I : Finset ℤ) :
    (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
      4*(∫ x, ‖f x‖^2 ∂μ) := by
  have hsq := hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hlevel (i : ℤ) : (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i)≤
      4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
    have hp : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
      rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      norm_num
      ring
    have hbound : (∫ _ in amplitudeLevel f i, ((2:ℝ)^i)^2/4 ∂μ)≤
        ∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ := by
      apply setIntegral_mono_on
        (integrableOn_const (amplitudeLevel_finite μ hf i)) hsq.integrableOn (amplitudeLevel_measurable hm i)
      intro x hx
      have hn : 0<(2:ℝ)^(i-1) := zpow_pos (by norm_num) _
      have hs := sq_le_sq₀ hn.le (norm_nonneg (f x)) |>.2 hx.1.le
      rw [hp]
      nlinarith only [hs]
    rw [setIntegral_const,smul_eq_mul] at hbound
    have he : (2:ℝ)^(2*i)=((2:ℝ)^i)^2 := by rw [mul_comm (2:ℤ) i,zpow_mul]; norm_num
    rw [he]
    nlinarith only [hbound]
  calc
    _ = ∑ i∈I, (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,Real.sq_sqrt measureReal_nonneg]
      congr 1
      rw [mul_comm (2:ℤ) i,zpow_mul]
      norm_num
    _ ≤ ∑ i∈I, 4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := Finset.sum_le_sum (fun i _ => hlevel i)
    _ = 4*(∫ x in ⋃ i∈I, amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
      rw [←Finset.mul_sum,integral_biUnion_finset I (fun i _ => amplitudeLevel_measurable hm i)
        (fun i _ j _ hij => amplitudeLevel_disjoint f hij) (fun _ _ => hsq.integrableOn)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hsq
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))) (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteAmplitudeGeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric summation for the two discarded amplitude tails. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_zpow_sum_bound (S : Finset ℤ) (b R : ℝ) (hb : 1<b) (hR : 0≤R)
    (hbound : ∀ i∈S, b^i≤R) :
    (∑ i∈S, b^i)≤(2/(1-b⁻¹))*R := by
  classical
  have hb0 : 0<b := zero_lt_one.trans hb
  have hr : 0≤b⁻¹ := inv_nonneg.mpr hb0.le
  have hr1 : b⁻¹<1 := inv_lt_one_of_one_lt₀ hb
  have hC : 0≤2/(1-b⁻¹) := by positivity
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : j∈S := Finset.max'_mem S hS
    have heq (i : ℤ) (hi : i∈S) : b^i=b^j*(b⁻¹)^(i-j).natAbs := by
      have hij : i≤j := Finset.le_max' S i hi
      have hn : ((i-j).natAbs:ℤ)=j-i := by omega
      rw [←zpow_natCast,inv_zpow,←zpow_neg,hn,←zpow_add₀ hb0.ne']
      congr 1
      omega
    calc
      _ = b^j*(∑ i∈S, (b⁻¹)^(i-j).natAbs) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl heq
      _ ≤ b^j*(2/(1-b⁻¹)) := mul_le_mul_of_nonneg_left
        (int_geometric_shift_sum_le hr hr1 S j) (zpow_pos hb0 _).le
      _ ≤ (2/(1-b⁻¹))*R := by nlinarith [hbound j hj]
  · have hEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [Finset.sum_empty]
    exact mul_nonneg hC hR

theorem sqrt_two_zpow (i : ℤ) : (Real.sqrt 2)^i=Real.sqrt ((2:ℝ)^i) := by
  have hs : ((Real.sqrt 2)^i)^2=(2:ℝ)^i := by
    rw [←zpow_natCast,←zpow_mul,mul_comm,zpow_mul,zpow_natCast,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [←hs,Real.sqrt_sq_eq_abs,abs_of_pos (zpow_pos (Real.sqrt_pos.2 (by norm_num)) _)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_AmplitudeMassTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical small- and large-measure tails for the amplitude
levels after bin projection. The constants are independent of dimension
and of the finite set of retained levels. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_small_mass_tail (I : Finset ℤ) (mass : ℤ → ℝ) (M0 Q eps : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (_heps : 0≤eps)
    (hamp : ∀ i∈I, (2:ℝ)^i≤2*Q)
    (hmass : ∀ i∈I, mass i≤eps*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i/M0))≤8*Q*Real.sqrt eps := by
  have hsum := finite_zpow_sum_bound I 2 (2*Q) (by norm_num) (by positivity) hamp
  have hsum' : (∑ i∈I, (2:ℝ)^i)≤8*Q := by norm_num at hsum; linarith
  calc
    _ ≤ ∑ i∈I, (2:ℝ)^i*Real.sqrt eps := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((div_le_iff₀ hM0).mpr (hmass i hi)))
      positivity
    _ = (∑ i∈I, (2:ℝ)^i)*Real.sqrt eps := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum' (Real.sqrt_nonneg _)

theorem amplitude_large_mass_tail (I : Finset ℤ) (mass : ℤ → ℝ) (M0 Q eps : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0<eps)
    (hmass : ∀ i∈I, 0 ≤ mass i)
    (hlarge : ∀ i∈I, M0≤eps*mass i)
    (hL1 : ∀ i∈I, (2:ℝ)^i*mass i≤2*Q*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i/M0))≤
      2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := by
  have hbase : 1<Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hp := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hamp (i : ℤ) (hi : i∈I) : (2:ℝ)^i≤2*Q*eps := by
    have hpow : 0≤(2:ℝ)^i := (zpow_pos (by norm_num) _).le
    have h1 := mul_le_mul_of_nonneg_left (hlarge i hi) hpow
    have h2 := mul_le_mul_of_nonneg_left (hL1 i hi) heps.le
    have he : (2:ℝ)^i*M0≤(2*Q*eps)*M0 := by nlinarith
    nlinarith
  have hsum := finite_zpow_sum_bound I (Real.sqrt 2) (Real.sqrt (2*Q*eps)) hbase
    (Real.sqrt_nonneg _) (fun i hi => by rw [sqrt_two_zpow]; exact Real.sqrt_le_sqrt (hamp i hi))
  have hpoint (i : ℤ) (hi : i∈I) :
      (2:ℝ)^i*Real.sqrt (mass i/M0)≤Real.sqrt (2*Q)*(Real.sqrt 2)^i := by
    rw [sqrt_two_zpow]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg (hmass i hi) hM0.le),
      Real.sq_sqrt (by positivity : 0≤2*Q),Real.sq_sqrt (by positivity : 0≤(2:ℝ)^i)]
    have hh : (2:ℝ)^i*(mass i/M0)≤2*Q := by
      rw [←mul_div_assoc]
      exact (div_le_iff₀ hM0).mpr (hL1 i hi)
    nlinarith [mul_le_mul_of_nonneg_left hh (zpow_pos (by norm_num : (0:ℝ)<2) i).le]
  calc
    _ ≤ ∑ i∈I, Real.sqrt (2*Q)*(Real.sqrt 2)^i := Finset.sum_le_sum hpoint
    _ = Real.sqrt (2*Q)*(∑ i∈I, (Real.sqrt 2)^i) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt (2*Q)*((2/(1-(Real.sqrt 2)⁻¹))*Real.sqrt (2*Q*eps)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤2*Q)]
      have hs := Real.sq_sqrt (by positivity : 0≤2*Q)
      calc
        _ = (2/(1-(Real.sqrt 2)⁻¹))*Real.sqrt eps*(Real.sqrt (2*Q))^2 := by ring
        _ = _ := by rw [hs]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeLevelL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical amplitude tail hypotheses follow from the actual
pointwise and L1 bounds of the bin-projected vector. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_amplitude_bound (mu : Measure X) (f : X → E)
    (Q : ℝ) (hQ : ∀ x, ‖f x‖≤Q) (i : ℤ)
    (hpos : 0 < mu.real (amplitudeLevel f i)) : (2:ℝ)^i≤2*Q := by
  have hn : (amplitudeLevel f i).Nonempty := by
    by_contra h
    have he : amplitudeLevel f i=∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hpos
  obtain ⟨x,hx⟩ := hn
  have h := hx.1.trans_le (hQ x)
  have he : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
    rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
    norm_num
    ring
  rw [he]
  linarith

theorem amplitudeLevel_l1_bound (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hL1 : Integrable (fun x => ‖f x‖) mu) (i : ℤ) :
    (2:ℝ)^i*mu.real (amplitudeLevel f i)≤2*∫ x, ‖f x‖ ∂mu := by
  have hset := amplitudeLevel_measurable hm i
  have hi : IntegrableOn (fun _ : X => (2:ℝ)^(i-1)) (amplitudeLevel f i) mu :=
    integrableOn_const (amplitudeLevel_finite mu hf i)
  have hlow : (∫ _ in amplitudeLevel f i, (2:ℝ)^(i-1) ∂mu)≤
      ∫ x in amplitudeLevel f i, ‖f x‖ ∂mu := by
    apply setIntegral_mono_on hi hL1.integrableOn hset
    intro x hx
    exact hx.1.le
  have hfull := setIntegral_le_integral hL1 (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (s:=amplitudeLevel f i)
  rw [setIntegral_const,smul_eq_mul] at hlow
  have he : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
    rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
    norm_num
    ring
  rw [he]
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeNormalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual amplitude-level energy by the reference set
measure, as used in the bin reduction. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitude_normalized_energy_budget (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (M0 C0 : ℝ) (hM0 : 0<M0) (henergy : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0) (I : Finset ℤ) :
    (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))^2)≤4*C0 := by
  have heq : (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))^2)=
      (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)))^2)/M0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg measureReal_nonneg hM0.le),Real.sq_sqrt measureReal_nonneg]
    ring
  rw [heq]
  apply (div_le_iff₀ hM0).mpr
  have h := amplitude_energy_budget mu hf hm I
  nlinarith

theorem amplitudeLevel_small_tail (mu : Measure X) (f : X → E)
    (I : Finset ℤ) (M0 Q eps : ℝ) (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0≤eps)
    (hbound : ∀ x, ‖f x‖≤Q) (hpos : ∀ i∈I, 0 < mu.real (amplitudeLevel f i))
    (hsmall : ∀ i∈I, mu.real (amplitudeLevel f i)≤eps*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤8*Q*Real.sqrt eps :=
  amplitude_small_mass_tail I (fun i => mu.real (amplitudeLevel f i)) M0 Q eps hM0 hQ heps
    (fun i hi => amplitudeLevel_amplitude_bound mu f Q hbound i (hpos i hi)) hsmall

theorem amplitudeLevel_large_tail (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hL1 : Integrable (fun x => ‖f x‖) mu)
    (I : Finset ℤ) (M0 Q eps : ℝ) (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0<eps)
    (hbound : (∫ x, ‖f x‖ ∂mu)≤Q*M0)
    (hlarge : ∀ i∈I, M0≤eps*mu.real (amplitudeLevel f i)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := by
  apply amplitude_large_mass_tail I (fun i => mu.real (amplitudeLevel f i)) M0 Q eps
    hM0 hQ heps (fun _ _ => measureReal_nonneg) hlarge
  intro i _
  have h := amplitudeLevel_l1_bound mu f hf hm hL1 i
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeDiscardedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both discarded logarithmic mass tails of the actual amplitude
levels have the manuscript's Q exp(-L/8) bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_discarded_sum (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hf1 : Integrable (fun x => ‖f x‖) mu) (I : Finset ℤ) (M0 Q L : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (hinfty : ∀ x, ‖f x‖≤Q)
    (hL1 : (∫ x, ‖f x‖ ∂mu)≤Q*M0)
    (hpos : ∀ i∈I, 0 < mu.real (amplitudeLevel f i))
    (hdiscard : ∀ i∈I, L/4 < |Real.log (mu.real (amplitudeLevel f i)/M0)|) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      (8+2*(2/(1-(Real.sqrt 2)⁻¹)))*Q*Real.exp (-L/8) := by
  classical
  let eps := Real.exp (-L/4)
  let P := fun i : ℤ => mu.real (amplitudeLevel f i)≤eps*M0
  have heps : 0<eps := Real.exp_pos _
  have hs := amplitudeLevel_small_tail mu f (I.filter P) M0 Q eps hM0 hQ heps.le hinfty
    (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hl := amplitudeLevel_large_tail mu f hf hm hf1 (I.filter (fun i => ¬P i))
    M0 Q eps hM0 hQ heps hL1 (fun i hi => ?_)
  · have he : Real.sqrt eps=Real.exp (-L/8) := by
      rw [show eps=Real.exp (-L/4) from rfl,←Real.exp_half]
      congr 1
      ring
    calc
      _=(∑ i∈I.filter P, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))+
          ∑ i∈I.filter (fun i => ¬P i), (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0) :=
        (Finset.sum_filter_add_sum_filter_not I P _).symm
      _≤8*Q*Real.sqrt eps+2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := add_le_add hs hl
      _=_ := by rw [he]; ring
  · obtain ⟨hiI,hiP⟩ := Finset.mem_filter.mp hi
    have hratio : 0 < mu.real (amplitudeLevel f i)/M0 := div_pos (hpos i hiI) hM0
    have hlow : -L/4<Real.log (mu.real (amplitudeLevel f i)/M0) := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log hratio]
      exact (lt_div_iff₀ hM0).mpr (lt_of_not_ge hiP)
    have hhigh : L/4<Real.log (mu.real (amplitudeLevel f i)/M0) := by
      by_contra hh
      have habs := abs_le.mpr ⟨by linarith,le_of_not_gt hh⟩
      exact (not_le_of_gt (hdiscard i hiI)) habs
    have hr : Real.exp (L/4)*M0 ≤ mu.real (amplitudeLevel f i) := by
      apply (le_div_iff₀ hM0).mp
      exact (Real.exp_lt_exp.mpr hhigh).le.trans_eq (Real.exp_log hratio)
    have hcancel : eps*Real.exp (L/4)=1 := by
      dsimp only [eps]
      rw [←Real.exp_add]
      rw [show (-L/4)+(L/4)=0 by ring,Real.exp_zero]
    calc
      M0=eps*(Real.exp (L/4)*M0) := by rw [←mul_assoc,hcancel,one_mul]
      _≤eps*mu.real (amplitudeLevel f i) := mul_le_mul_of_nonneg_left hr heps.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeClassSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained amplitude levels cost only the square root of the
number of their dyadic measure classes. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_class_sum (I : Finset ℤ) (mass : ℤ → ℝ) (cls : ℤ → ℤ)
    (hlo : ∀ i∈I, (2:ℝ)^(cls i) ≤ mass i)
    (hhi : ∀ i∈I, mass i≤(2:ℝ)^(cls i+1)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt ((I.image cls).card:ℝ)*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
  classical
  let a := fun i : ℤ => (2:ℝ)^i*Real.sqrt (mass i)
  let E := fun k : ℤ => ∑ i∈I.filter (fun i => cls i=k), (a i)^2
  have hE (k : ℤ) : 0≤E k := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hclass (k : ℤ) : (∑ i∈I.filter (fun i => cls i=k), a i)≤4*Real.sqrt 2*Real.sqrt (E k) := by
    apply amplitude_class_bound (I.filter (fun i => cls i=k)) mass ((2:ℝ)^k)
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hlo i hi
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      calc
        _ ≤ (2:ℝ)^(k+1) := by simpa only [he] using hhi i hi
        _ = 2*(2:ℝ)^k := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hfiber : (∑ k∈I.image cls, E k)=∑ i∈I, (a i)^2 :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem cls hi) (fun i => (a i)^2)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (I.image cls) (fun _ => (1:ℝ)) (fun k => Real.sqrt (E k))
  have hcs' : (∑ k∈I.image cls, Real.sqrt (E k))≤
      Real.sqrt ((I.image cls).card:ℝ)*Real.sqrt (∑ i∈I, (a i)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,Nat.cast_one,mul_one,
      Real.sq_sqrt (hE _),hfiber] using hcs
  calc
    _ = ∑ k∈I.image cls, ∑ i∈I.filter (fun i => cls i=k), a i :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem cls hi) a).symm
    _ ≤ ∑ k∈I.image cls, 4*Real.sqrt 2*Real.sqrt (E k) := Finset.sum_le_sum (fun k _ => hclass k)
    _ = 4*Real.sqrt 2*(∑ k∈I.image cls, Real.sqrt (E k)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs' (by positivity : 0≤4*Real.sqrt 2)

theorem dyadic_amplitude_class_sum (I : Finset ℤ) (mass : ℤ → ℝ)
    (hm : ∀ i∈I, 0 < mass i) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2) :=
  amplitude_class_sum I mass (fun i => dyadicMeasureClass (mass i))
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).1)
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).2.le)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeClassCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic window of support measures contains only linearly many
of the dyadic classes used in the retained amplitude sum. -/
noncomputable section
namespace LipschitzHilbert

theorem dyadicMeasureClass_abs_le (m L : ℝ) (hlog : |Real.log m|≤L) :
    |(dyadicMeasureClass m:ℝ)|≤L/Real.log 2+1 := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hx : |Real.log m/Real.log 2|≤L/Real.log 2 := by
    rw [abs_div,abs_of_pos hc]
    exact div_le_div_of_nonneg_right hlog hc.le
  have hfloor := Int.floor_le (Real.log m/Real.log 2)
  have hceil := Int.lt_floor_add_one (Real.log m/Real.log 2)
  change |(⌊Real.log m/Real.log 2⌋:ℝ)|≤_
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2]⟩

theorem dyadicMeasureClass_image_card (I : Finset ℤ) (mass : ℤ → ℝ) (L : ℝ)
    (hL : 0≤L) (hlog : ∀ i∈I, |Real.log (mass i)|≤L) :
    ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)≤2*(L/Real.log 2)+5 := by
  classical
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K : ℕ := ⌈L/Real.log 2+1⌉₊
  have hKlo : L/Real.log 2+1≤K := Nat.le_ceil _
  have hKhi : (K:ℝ)≤L/Real.log 2+2 := by
    have h := (Nat.ceil_lt_add_one (show 0≤L/Real.log 2+1 by positivity)).le
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using h
  have hsub : I.image (fun i => dyadicMeasureClass (mass i)) ⊆ Finset.Icc (-(K:ℤ)) K := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have habs : |(dyadicMeasureClass (mass i):ℝ)|≤K :=
      (dyadicMeasureClass_abs_le _ L (hlog i hi)).trans hKlo
    have hInt : |dyadicMeasureClass (mass i)|≤(K:ℤ) := by exact_mod_cast habs
    exact Finset.mem_Icc.mpr (abs_le.mp hInt)
  have hcard : (Finset.Icc (-(K:ℤ)) K).card=2*K+1 := by
    have h := Int.card_Icc_of_le (a:=-(K:ℤ)) (b:=(K:ℤ)) (by omega)
    omega
  have hn : (I.image (fun i => dyadicMeasureClass (mass i))).card≤2*K+1 := by
    rw [←hcard]
    exact Finset.card_le_card hsub
  have hreal : ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)≤2*(K:ℝ)+1 := by
    exact_mod_cast hn
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeRetainedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained level sum has the square-root logarithmic loss needed
by the improved diagonal estimate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem retained_amplitude_sum (I : Finset ℤ) (mass : ℤ → ℝ) (L E : ℝ)
    (hL : 0≤L) (hm : ∀ i∈I, 0 < mass i)
    (hlog : ∀ i∈I, |Real.log (mass i)|≤L)
    (henergy : (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2)≤E) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt E := by
  have h := dyadic_amplitude_class_sum I mass hm
  apply h.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (dyadicMeasureClass_image_card I mass L hL hlog))
    positivity
  · exact Real.sqrt_le_sqrt henergy
  · exact Real.sqrt_nonneg _
  · positivity

theorem amplitudeLevel_retained_sum {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu)
    (hm : Measurable (fun x => ‖f x‖)) (I : Finset ℤ) (M0 C0 L : ℝ)
    (hM0 : 0<M0) (hL : 0≤L) (henergy : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0)
    (hpos : ∀ i∈I, 0 < mu.real (amplitudeLevel f i))
    (hlog : ∀ i∈I, |Real.log (mu.real (amplitudeLevel f i)/M0)|≤L) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt (4*C0) :=
  retained_amplitude_sum I (fun i => mu.real (amplitudeLevel f i)/M0) L (4*C0)
    hL (fun i hi => div_pos (hpos i hi) hM0) hlog
    (amplitude_normalized_energy_budget mu f hf hm M0 C0 hM0 henergy I)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeMatrixBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite amplitude reconstruction preserves a restricted pairing bound
with precisely the product of its two amplitude-weight sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_amplitude_matrix_bound (I J : Finset ℤ) (m n : ℤ → ℝ)
    (pairing : ℤ → ℤ → ℂ) (C : ℝ)
    (hpair : ∀ i∈I, ∀ j∈J, ‖pairing i j‖≤C*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖≤
      C*(∑ i∈I, (2:ℝ)^i*Real.sqrt (m i))*(∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)) := by
  calc
    _≤∑ i∈I, ∑ j∈J, ‖((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _≤∑ i∈I, ∑ j∈J, C*((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(2:ℝ)^i*(2:ℝ)^j)]
      calc
        _≤((2:ℝ)^i*(2:ℝ)^j)*(C*Real.sqrt (m i)*Real.sqrt (n j)) :=
          mul_le_mul_of_nonneg_left (hpair i hi j hj) (by positivity)
        _=_ := by ring
    _=(∑ i∈I, C*((2:ℝ)^i*Real.sqrt (m i)))*
        (∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _=_ := congrArg (fun x : ℝ => x*(∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)))
      (Finset.mul_sum I (fun i => (2:ℝ)^i*Real.sqrt (m i)) C).symm

theorem amplitude_weight_sum_unnormalize (I : Finset ℤ) (m : ℤ → ℝ)
    (M : ℝ) (hM : 0<M) (hm : ∀ i∈I, 0 ≤ m i) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (m i))=
      (∑ i∈I, (2:ℝ)^i*Real.sqrt (m i/M))*Real.sqrt M := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sqrt_div (hm i hi), mul_assoc,div_mul_cancel₀ _ (Real.sqrt_pos.2 hM).ne']

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RetainedAmplitudeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained pair sum loses only one logarithmic factor, as in the
source amplitude reduction. This concerns the actual measurable levels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem retained_amplitude_matrix_bound {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (f g : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hgm : Measurable g) (hf2 : MemLp f 2 mu) (hg2 : MemLp g 2 mu)
    (I J : Finset ℤ) (F E Cf Cg C L : ℝ)
    (hF : 0<F) (hE : 0<E) (hC : 0≤C) (hL : 0≤L)
    (henergyF : (∫ x, ‖f x‖^2 ∂mu)≤Cf*F) (henergyG : (∫ x, ‖g x‖^2 ∂mu)≤Cg*E)
    (hposF : ∀ i∈I, 0 < mu.real (amplitudeLevel f i))
    (hposG : ∀ j∈J, 0 < mu.real (amplitudeLevel g j))
    (hlogF : ∀ i∈I, |Real.log (mu.real (amplitudeLevel f i)/F)|≤L)
    (hlogG : ∀ j∈J, |Real.log (mu.real (amplitudeLevel g j)/E)|≤L)
    (pairing : ℤ → ℤ → ℂ)
    (hpair : ∀ i∈I, ∀ j∈J, ‖pairing i j‖≤
      C*Real.sqrt (mu.real (amplitudeLevel f i))*Real.sqrt (mu.real (amplitudeLevel g j))) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖≤
      C*retainedAmplitudeCost Cf L*retainedAmplitudeCost Cg L*Real.sqrt F*Real.sqrt E := by
  have hsumF := amplitudeLevel_retained_sum mu f hf2 hfm.norm I F Cf L hF hL henergyF hposF hlogF
  have hsumG := amplitudeLevel_retained_sum mu g hg2 hgm.norm J E Cg L hE hL henergyG hposG hlogG
  have h := finite_amplitude_matrix_bound I J
    (fun i => mu.real (amplitudeLevel f i)) (fun j => mu.real (amplitudeLevel g j)) pairing C hpair
  rw [amplitude_weight_sum_unnormalize I _ F hF (fun _ _ => measureReal_nonneg),
    amplitude_weight_sum_unnormalize J _ E hE (fun _ _ => measureReal_nonneg)] at h
  apply h.trans
  calc
    _≤C*(retainedAmplitudeCost Cf L*Real.sqrt F)*(retainedAmplitudeCost Cg L*Real.sqrt E) := by
      have hsG : 0≤∑ j∈J, (2:ℝ)^j*Real.sqrt (mu.real (amplitudeLevel g j)/E) := by positivity
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumF (Real.sqrt_nonneg _)) hC
      · exact mul_le_mul_of_nonneg_right hsumG (Real.sqrt_nonneg _)
      · positivity
      · exact mul_nonneg hC (by unfold retainedAmplitudeCost; positivity)
    _=_ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeAllWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All finite collections of actual amplitude levels split into the
retained logarithmic cost and the two exponentially small mass tails. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_all_weights (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hf1 : Integrable (fun x => ‖f x‖) mu) (I : Finset ℤ) (M0 Q C0 L : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (hL : 0≤L) (hinfty : ∀ x, ‖f x‖≤Q)
    (hL1 : (∫ x, ‖f x‖ ∂mu)≤Q*M0) (hL2 : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0)
    (hpos : ∀ i∈I, 0 < mu.real (amplitudeLevel f i)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L := by
  classical
  let P := fun i : ℤ => |Real.log (mu.real (amplitudeLevel f i)/M0)|≤L/4
  have hret := amplitudeLevel_retained_sum mu f hf hm (I.filter P) M0 C0 (L/4)
    hM0 (by positivity) hL2 (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hdrop := amplitudeLevel_discarded_sum mu f hf hm hf1 (I.filter (fun i => ¬P i)) M0 Q L
    hM0 hQ hinfty hL1 (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => lt_of_not_ge (Finset.mem_filter.mp hi).2)
  rw [←Finset.sum_filter_add_sum_filter_not I P]
  exact add_le_add hret hdrop

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted-to-strong estimate for the actual finite amplitude
approximations of Hilbert-valued functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudePiece_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (i : ℤ) :
    Measurable (amplitudePiece f i) :=
  measurable_const.smul (hf.indicator (amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudePiece_bounded (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X) :
    ‖amplitudePiece f i x‖≤1 := by
  by_cases hx : x∈amplitudeLevel f i
  · change ‖(2:ℝ)^(-i) • (amplitudeLevel f i).indicator f x‖≤1
    rw [Set.indicator_of_mem hx,norm_smul,Real.norm_of_nonneg (zpow_pos (by norm_num) _).le]
    calc
      _ ≤ (2:ℝ)^(-i)*(2:ℝ)^i := mul_le_mul_of_nonneg_left hx.2 (zpow_pos (by norm_num) _).le
      _ = _ := by rw [←zpow_add₀ (by norm_num : (2:ℝ)≠0)]; simp
  · simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero,norm_zero,zero_le_one]

omit [MeasurableSpace X] in
theorem amplitudePiece_supported (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X)
    (hx : x∉amplitudeLevel f i) : amplitudePiece f i x=0 := by
  simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite amplitude approximations converge in squared L2 energy.
The cutoff is the actual disjoint union of its amplitude levels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudeApprox_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (I : Finset ℤ) :
    Measurable (amplitudeApprox f I) := by
  rw [amplitudeApprox_eq_indicator]
  exact hf.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudeApprox_eventually_eq (f : X → EuclideanSpace ℂ κ) (x : X) :
    ∀ᶠ n : ℕ in atTop, amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x=f x := by
  by_cases hx : f x=0
  · filter_upwards [] with n
    rw [amplitudeApprox_eq_indicator]
    by_cases hm : x∈⋃ i∈Finset.Icc (-(n:ℤ)) n, amplitudeLevel f i
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm,hx]
  · obtain ⟨i,hi⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx) (by norm_num : (1:ℝ)<2)
    have hlevel : x∈amplitudeLevel f (i+1) := by
      change (2:ℝ)^(i+1-1)<‖f x‖ ∧ ‖f x‖≤(2:ℝ)^(i+1)
      simpa only [Set.mem_Ioc,add_sub_cancel_right] using hi
    filter_upwards [eventually_ge_atTop (i+1).natAbs] with n hn
    rw [amplitudeApprox_eq_indicator,Set.indicator_of_mem]
    exact Set.mem_iUnion.mpr ⟨i+1,Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr (by omega),hlevel⟩⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeApproximationL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite amplitude approximations also converge in L1. Null levels
can be deleted without changing their almost-everywhere values. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudeApprox_integrable (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f mu) (I : Finset ℤ) :
    Integrable (amplitudeApprox f I) mu := by
  rw [amplitudeApprox_eq_indicator]
  exact hf1.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hfm.norm i))

theorem amplitudePiece_zero_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) (i : ℤ) (hi : mu.real (amplitudeLevel f i)=0) :
    amplitudePiece f i=ᵐ[mu] 0 := by
  have hz := (measureReal_eq_zero_iff (amplitudeLevel_finite mu hf2 i)).mp hi
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
  exact amplitudePiece_supported f i x hx

theorem amplitudeApprox_positive_filter_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) (I : Finset ℤ) :
    amplitudeApprox f (I.filter (fun i => 0 < mu.real (amplitudeLevel f i)))=ᵐ[mu]
      amplitudeApprox f I := by
  classical
  unfold amplitudeApprox
  rw [Finset.sum_filter]
  apply eventuallyEq_sum
  intro i _
  by_cases hi : 0 < mu.real (amplitudeLevel f i)
  · exact Filter.Eventually.of_forall (fun _ => by simp only [hi,ite_true, if_true])
  · have hz : mu.real (amplitudeLevel f i)=0 := le_antisymm (le_of_not_gt hi) measureReal_nonneg
    filter_upwards [amplitudePiece_zero_ae mu f hf2 i hz] with x hx
    simp only [hi,ite_false, if_false,Pi.zero_apply,Pi.smul_apply,hx,smul_zero]

 theorem amplitudeApprox_positive_tendsto_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) :
    ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0 < mu.real (amplitudeLevel f i))) x)
      atTop (𝓝 (f x)) := by
  have ha : ∀ᵐ x ∂mu, ∀ n : ℕ, amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0 < mu.real (amplitudeLevel f i))) x=
      amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x :=
    ae_all_iff.mpr (fun n => amplitudeApprox_positive_filter_ae mu f hf2 _)
  filter_upwards [ha] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [amplitudeApprox_eventually_eq f x] with n hn
  rw [hx n,hn]

omit [MeasurableSpace X] in
theorem amplitudeApprox_coordinate_norm_le (f : X → EuclideanSpace ℂ κ)
    (I : Finset ℤ) (x : X) (k : κ) : ‖amplitudeApprox f I x k‖≤‖f x k‖ := by
  rw [amplitudeApprox_eq_indicator]
  by_cases hx : x∈⋃ i∈I, amplitudeLevel f i
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simp only [WithLp.ofLp_zero,Pi.zero_apply,norm_zero,norm_nonneg]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeDisparity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retaining logarithmically comparable amplitude masses preserves the
source model's full disparity interval. -/
noncomputable section
namespace LipschitzHilbert

theorem sqrt_mass_ratio (F E : ℝ) (hF : 0<F) (hE : 0<E) :
    0<Real.sqrt (E/F) ∧ E=(Real.sqrt (E/F))^2*F := by
  refine ⟨Real.sqrt_pos.2 (div_pos hE hF),?_⟩
  rw [Real.sq_sqrt (div_pos hE hF).le]
  field_simp

theorem log_amplitude_disparity (F E f g ratio : ℝ)
    (hF : 0<F) (hE : 0<E) (hf : 0<f) (hg : 0<g) (hr : 0 < ratio)
    (heq : E=ratio^2*F) :
    Real.log (Real.sqrt (g/f))=
      Real.log ratio+(Real.log (g/E)-Real.log (f/F))/2 := by
  rw [Real.log_sqrt (div_pos hg hf).le,Real.log_div hg.ne' hf.ne',
    Real.log_div hg.ne' hE.ne',Real.log_div hf.ne' hF.ne',heq,
    Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow]
  ring

theorem retained_amplitude_disparity (F E f g ratio L : ℝ)
    (hF : 0<F) (hE : 0<E) (hf : 0<f) (hg : 0<g) (hr : 0 < ratio)
    (heq : E=ratio^2*F) (hL : Real.log ratio=L)
    (hlogf : |Real.log (f/F)|≤L/4) (hlogg : |Real.log (g/E)|≤L/4) :
    L/2≤Real.log (Real.sqrt (g/f)) ∧ Real.log (Real.sqrt (g/f))≤2*L := by
  have hnonneg : 0≤L := by linarith [abs_nonneg (Real.log (f/F))]
  rw [log_amplitude_disparity F E f g ratio hF hE hf hg hr heq,hL]
  obtain ⟨hflo,hfhi⟩ := abs_le.mp hlogf
  obtain ⟨hglo,hghi⟩ := abs_le.mp hlogg
  constructor <;> linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeTailParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The allowed exp(O(L^0.9)) amplitude bound is absorbed by the
exp(-L/8) discarded-mass saving. -/
noncomputable section
open Filter
namespace LipschitzHilbert

theorem eventually_amplitude_tail_decay (A B C : ℝ) (hA : 0<A) (_hB : 0≤B) (hC : 0<C) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      C*Q*Real.exp (-L/8)≤Real.exp (-L/16) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop (32*B),
    eventually_ge_atTop (32*|Real.log (C*A)|)] with L hL hgap hconstant Q hQ
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : L=L^(9/10:ℝ)*L^(1/10:ℝ) := by
    rw [←Real.rpow_add hLp]
    norm_num
  have hslow : B*L^(9/10:ℝ)≤L/32 := by
    have h := mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hLp.le (9/10:ℝ))
    rw [←hpow] at h
    nlinarith
  have hlog : Real.log (C*A)≤L/32 := by
    have h := le_abs_self (Real.log (C*A))
    linarith
  calc
    C*Q*Real.exp (-L/8)≤C*(A*Real.exp (B*L^(9/10:ℝ)))*Real.exp (-L/8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hC.le) (Real.exp_pos _).le
    _=Real.exp (Real.log (C*A)+B*L^(9/10:ℝ)-L/8) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_add,Real.exp_log (mul_pos hC hA),neg_div]
      ring
    _≤Real.exp (-L/16) := Real.exp_le_exp.mpr (by linarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeTailCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace LipschitzHilbert

theorem amplitudeTailCoefficient_pos : 0<(8:ℝ)+2*(2/(1-(Real.sqrt 2)⁻¹)) := by
  have hd : 0<1-(Real.sqrt 2)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two)
  positivity

theorem amplitudeTailCost_nonneg (Q L : ℝ) (hQ : 0≤Q) : 0≤amplitudeTailCost Q L := by
  unfold amplitudeTailCost
  exact mul_nonneg (mul_nonneg amplitudeTailCoefficient_pos.le hQ) (Real.exp_pos _).le

theorem retainedAmplitudeCost_nonneg (C L : ℝ) : 0 ≤ retainedAmplitudeCost C L := by
  unfold retainedAmplitudeCost
  positivity

theorem eventually_amplitudeTailCost_bound (A B : ℝ) (hA : 0<A) (hB : 0≤B) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      amplitudeTailCost Q L≤Real.exp (-L/16) :=
  eventually_amplitude_tail_decay A B _ hA hB amplitudeTailCoefficient_pos

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeErrorDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full discarded-amplitude error is smaller than L^-19 for the
source's allowed amplitude growth, uniformly over the level cutoffs. -/
noncomputable section
open Filter
namespace LipschitzHilbert

theorem retainedAmplitudeCost_le_linear (C0 L : ℝ) (hL : 1≤L) :
    retainedAmplitudeCost C0 (L/4)≤
      (4*Real.sqrt 2*Real.sqrt (4*C0)*(2/Real.log 2+5))*L := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0≤L := by linarith
  have hT : 1≤2*((L/4)/Real.log 2)+5 := by
    have h : 0≤2*((L/4)/Real.log 2) := by positivity
    linarith
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hT)
  have ht : 2*((L/4)/Real.log 2)+5≤(2/Real.log 2+5)*L := by
    have hr : (L/4)/Real.log 2≤L/Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hlog.le
    calc
      _≤2*(L/Real.log 2)+5 := by linarith
      _≤(2/Real.log 2+5)*L := by
        have he : 2*(L/Real.log 2)=(2/Real.log 2)*L := by ring
        rw [he]
        nlinarith
  unfold retainedAmplitudeCost
  calc
    _=(4*Real.sqrt 2*Real.sqrt (4*C0))*Real.sqrt (2*((L/4)/Real.log 2)+5) := by ring
    _≤(4*Real.sqrt 2*Real.sqrt (4*C0))*((2/Real.log 2+5)*L) :=
      mul_le_mul_of_nonneg_left (hs.trans ht) (by positivity)
    _=_ := by ring

theorem eventually_amplitude_error_decay (A B C0 : ℝ) (hA : 0<A) (hB : 0≤B) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, 0≤Q → Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
        (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L≤L^(-19:ℝ) := by
  let D := 4*Real.sqrt 2*Real.sqrt (4*C0)*(2/Real.log 2+5)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0≤D := by dsimp only [D]; positivity
  let delta := 1/(2*(D+1))
  have hd : 0<delta := by dsimp only [delta]; positivity
  have hsmall := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0:ℝ)<1/16) (-20)).bound hd
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_amplitudeTailCost_bound A B hA hB,hsmall]
    with L hL htail hsmall Q hQ hQbound
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hcost : retainedAmplitudeCost C0 (L/4)≤D*L := retainedAmplitudeCost_le_linear C0 L hL
  have he : Real.exp (-L/16)≤delta*L^(-20:ℝ) := by
    have heq : -(1/16:ℝ)*L=-L/16 := by ring
    simpa only [heq,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg hLp.le (-20:ℝ))] using hsmall
  have heone : Real.exp (-L/16)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht := htail Q hQbound
  have ht0 := amplitudeTailCost_nonneg Q L hQ
  have hr0 := retainedAmplitudeCost_nonneg C0 (L/4)
  have hp : L^(-20:ℝ)*L=L^(-19:ℝ) := by
    calc
      _=L^(-20:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _=L^((-20:ℝ)+1) := (Real.rpow_add hLp _ _).symm
      _=_ := by norm_num
  calc
    _≤2*Real.exp (-L/16)*(D*L+1) := by
      have hs : retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L≤D*L+1 :=
        add_le_add hcost (ht.trans heone)
      have hp1 := mul_le_mul ht hs (add_nonneg hr0 ht0) (Real.exp_pos _).le
      have hp2 := mul_le_mul hs ht ht0 (by positivity : 0≤D*L+1)
      nlinarith
    _≤2*(delta*L^(-20:ℝ))*((D+1)*L) := by
      have hlin : D*L+1≤(D+1)*L := by nlinarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hlin
        (by positivity) (by positivity)
    _=L^(-19:ℝ) := by
      have hdid : 2*delta*(D+1)=1 := by dsimp only [delta]; field_simp
      calc
        _=(2*delta*(D+1))*(L^(-20:ℝ)*L) := by ring
        _=_ := by rw [hdid,one_mul,hp]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteMatrixDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite matrix restricted to two retained index sets differs from
the full matrix by at most the product bounds with one discarded factor. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private theorem finite_product_sum {ι ν : Type*} (I : Finset ι) (J : Finset ν)
    (a : ι → ℝ) (b : ν → ℝ) :
    (∑ i∈I, ∑ j∈J, a i*b j)=(∑ i∈I, a i)*(∑ j∈J, b j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem finite_matrix_discard_bound {ι ν : Type*} (I : Finset ι) (J : Finset ν)
    (p : ι → Prop) (q : ν → Prop) [DecidablePred p] [DecidablePred q]
    (a : ι → ℝ) (b : ν → ℝ) (B : ι → ν → ℂ) (C : ℝ)
    (hC : 0≤C) (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤C*a i*b j) :
    ‖(∑ i∈I, ∑ j∈J, B i j)-(∑ i∈I.filter p, ∑ j∈J.filter q, B i j)‖≤
      C*((∑ i∈I.filter (fun i => ¬p i), a i)*(∑ j∈J, b j)+
        (∑ i∈I, a i)*(∑ j∈J.filter (fun j => ¬q j), b j)) := by
  have heq : (∑ i∈I, ∑ j∈J, B i j)-(∑ i∈I.filter p, ∑ j∈J.filter q, B i j)=
      ∑ i∈I, ∑ j∈J, if p i ∧ q j then 0 else B i j := by
    simp only [Finset.sum_filter]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i
    · simp only [hp,ite_true, if_true]
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hq : q j <;> simp [hq]
    · simp [hp]
  rw [heq]
  calc
    _≤∑ i∈I, ∑ j∈J, ‖if p i ∧ q j then 0 else B i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _≤∑ i∈I, ∑ j∈J, C*((if p i then 0 else a i)*b j+a i*(if q j then 0 else b j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hB i hi j hj
      have hn : 0≤C*a i*b j := mul_nonneg (mul_nonneg hC (ha i hi)) (hb j hj)
      by_cases hp : p i <;> by_cases hq : q j <;> simp [hp,hq] <;> nlinarith
    _=C*(∑ i∈I, ∑ j∈J, (if p i then 0 else a i)*b j)+
        C*(∑ i∈I, ∑ j∈J, a i*(if q j then 0 else b j)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    _=_ := by
      rw [finite_product_sum,finite_product_sum]
      simp only [Finset.sum_filter,ite_not]
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeMatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LipschitzHilbert

theorem weighted_pair_bound_normalized (z : ℂ) (a b K m n F E : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hm : 0 ≤ m) (hn : 0≤n) (hF : 0<F) (hE : 0<E)
    (hz : ‖z‖≤K*Real.sqrt m*Real.sqrt n) :
    ‖(a*b) • z‖≤(K*Real.sqrt F*Real.sqrt E)*
      (a*Real.sqrt (m/F))*(b*Real.sqrt (n/E)) := by
  rw [norm_smul,Real.norm_of_nonneg (mul_nonneg ha hb)]
  apply (mul_le_mul_of_nonneg_left hz (mul_nonneg ha hb)).trans_eq
  rw [Real.sqrt_div hm,Real.sqrt_div hn]
  field_simp [(Real.sqrt_pos.2 hF).ne',(Real.sqrt_pos.2 hE).ne']

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeRetainedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained amplitude loss is linear in the logarithmic disparity,
so the model's L^-20 saving leaves L^-19 after reconstruction. -/
noncomputable section
namespace LipschitzHilbert

theorem retainedAmplitudeCost_sq (C0 L : ℝ) (hC0 : 0≤C0) (hL : 0≤L) :
    (retainedAmplitudeCost C0 L)^2=128*C0*(2*(L/Real.log 2)+5) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold retainedAmplitudeCost
  simp only [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
    Real.sq_sqrt (by positivity : 0≤2*(L/Real.log 2)+5),
    Real.sq_sqrt (by positivity : 0≤4*C0)]
  ring

theorem retainedAmplitudeCost_decay (K C0 L : ℝ) (hK : 0≤K) (hC0 : 0≤C0) (hL : 1≤L) :
    K*L^(-20:ℝ)*(retainedAmplitudeCost C0 L)^2≤
      (128*K*C0*(2/Real.log 2+5))*L^(-19:ℝ) := by
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hT : 2*(L/Real.log 2)+5≤(2/Real.log 2+5)*L := by
    calc
      _=(2/Real.log 2)*L+5 := by ring
      _≤(2/Real.log 2)*L+5*L := by linarith
      _=_ := by ring
  have hp : L^(-20:ℝ)*L=L^(-19:ℝ) := by
    calc
      _=L^(-20:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _=L^((-20:ℝ)+1) := (Real.rpow_add hLp _ _).symm
      _=_ := by norm_num
  rw [retainedAmplitudeCost_sq C0 L hC0 hLp.le]
  calc
    _=128*K*C0*(L^(-20:ℝ)*(2*(L/Real.log 2)+5)) := by ring
    _≤128*K*C0*(L^(-20:ℝ)*((2/Real.log 2+5)*L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hLp.le _)) (by positivity)
    _=_ := by
      calc
        _=(128*K*C0*(2/Real.log 2+5))*(L^(-20:ℝ)*L) := by ring
        _=_ := by rw [hp]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

/-- The annular multiplier and the narrow horizontal frequency support
force the normalized selector away from zero, uniformly in the scales. -/
theorem normalized_selector_lower (X V U c C : ℝ)
    (_hc : 0 < c) (hC : 0<C) (hV0 : 0≤V) (hV : V≤C)
    (hX : |X| ≤ c/4) (hAnnulus : c≤|X+V*U|) :
    3*c/(4*C)≤|U| := by
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri := abs_add_le X (V*U)
  have hbound : V*|U|≤C*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

/-- The positive vertical annulus also bounds the normalized selector
above; no scale or bin count enters the bound. -/
theorem normalized_selector_upper (X V U c C M : ℝ)
    (hc : 0 < c) (hV : c≤V) (hX : |X|≤C/4) (hAnnulus : |X+V*U|≤M) :
    |U|≤(M+C/4)/c := by
  have hV0 : 0≤V := hc.le.trans hV
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri : |V*U|≤|X+V*U|+|X| := by
    calc
      _ = |(X+V*U)+(-X)| := by congr 1; ring
      _ ≤ |X+V*U|+|-X| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hbound : c*|U|≤V*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (le_div_iff₀ hc).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolFourier
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation of the normalized (X,Y,U) symbol by Fourier inversion.
The two frequency coordinates and the selector coordinate are separated
inside an absolutely convergent integral. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolPoint_inner (nu : SymbolSpace) (X Y U : ℝ) :
    inner ℝ nu (symbolPoint X Y U)=nu 0*X+nu 1*Y+nu 2*U := by
  simp [PiLp.inner_apply, symbolPoint, Fin.sum_univ_succ]
  ring

theorem separated_symbol_fourier (S : SchwartzMap SymbolSpace ℂ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      𝓕 S nu * frequencyCharacter nu X Y * selectorCharacter nu U := by
  have hinv : (𝓕⁻ (𝓕 S : SchwartzMap SymbolSpace ℂ) : SchwartzMap SymbolSpace ℂ)=S :=
    FourierTransform.fourierInv_fourier_eq _
  have h := congrArg (fun f : SchwartzMap SymbolSpace ℂ => f (symbolPoint X Y U)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  calc
    _ = ∫ nu : SymbolSpace, Real.fourierChar (inner ℝ nu (symbolPoint X Y U)) • 𝓕 S nu := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with nu
      rw [symbolPoint_inner, Real.fourierChar.map_add_eq_mul, Real.fourierChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul, frequencyCharacter, selectorCharacter]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolWeights
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable fixed polynomial weights for the separated symbol.
The same weight is allocated to the two waves and to the selector,
leaving an integrable outside coefficient. Only a fixed seminorm is used. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolWeight_pos (q : ℕ) (nu : SymbolSpace) : 0 < symbolWeight q nu :=
  inv_pos.mpr (pow_pos (by positivity) q)

theorem weighted_symbol_identity (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*
        ((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*weightedSelector S q nu U := by
  rw [separated_symbol_fourier S X Y U]
  apply integral_congr_ae
  filter_upwards [] with nu
  have hw : (symbolWeight q nu : ℂ)≠0 := by exact_mod_cast (symbolWeight_pos q nu).ne'
  unfold weightedSelector
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolSlice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting one fixed Schwartz symbol to the two scale parameters.
The restriction does not enlarge any Schwartz seminorm. -/
noncomputable section
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem symbolInclusion_norm : ‖symbolInclusion‖≤1 :=
  ContinuousLinearMap.norm_inl_le_one ℝ SymbolSpace (ℝ × ℝ)

theorem symbolSlice_derivative_bound (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (n : ℕ) (q : SymbolSpace) :
    ‖iteratedFDeriv ℝ n (symbolSlice F p) q‖≤‖iteratedFDeriv ℝ n F (q,p)‖ := by
  have hid : (symbolSlice F p : SymbolSpace → ℂ)=
      (fun z : MasterSymbolSpace => F (z+(0,p))) ∘ symbolInclusion := by
    ext x
    simp [symbolInclusion]
  have hs : ContDiff ℝ ∞ (fun z : MasterSymbolSpace => F (z+(0,p))) := by fun_prop
  have hd := symbolInclusion.iteratedFDeriv_comp_right
    (f := fun z : MasterSymbolSpace => F (z+(0,p))) hs q (i := n) (mod_cast le_top)
  rw [hid, hd]
  rw [iteratedFDeriv_comp_add_right]
  have h := (iteratedFDeriv ℝ n F (symbolInclusion q+(0,p))).norm_compContinuousLinearMap_le
    (fun _ : Fin n => symbolInclusion)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hp : ‖symbolInclusion‖^n≤1 := pow_le_one₀ (norm_nonneg _) symbolInclusion_norm
  exact h.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by
    simp [symbolInclusion]))

theorem symbolSlice_seminorm (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (symbolSlice F p)≤SchwartzMap.seminorm ℝ k n F := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (apply_nonneg _ _)
  intro q
  calc
    _ ≤ ‖q‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ :=
      mul_le_mul_of_nonneg_left (symbolSlice_derivative_bound F p n q) (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖(q,p)‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ := by
      gcongr
      exact le_max_left _ _
    _ ≤ _ := SchwartzMap.le_seminorm ℝ k n F (q,p)

/-- The Fourier coefficient bound is uniform over both parameters.
Only finitely many seminorms of the single master symbol enter. -/
theorem symbolSlice_coefficient_uniform (F : SchwartzMap MasterSymbolSpace ℂ) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ × ℝ, symbolCoefficientBound (symbolSlice F p) q≤C := by
  let Q : Seminorm ℝ (SchwartzMap SymbolSpace ℂ) :=
    ((Finset.Iic (4*q,0)).sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)).comp
      (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).toLinearMap
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ SymbolSpace ℂ).continuous_seminorm i)).comp
        (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).continuous
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ SymbolSpace ℂ) Q hQ
  let M := (s.sup (schwartzSeminormFamily ℝ MasterSymbolSpace ℂ)) F
  refine ⟨2^(4*q)*((A:ℝ)*M)+1, by dsimp [M]; positivity, ?_⟩
  intro p
  have hs : (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p)≤M := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact (symbolSlice_seminorm F p i.1 i.2).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ MasterSymbolSpace ℂ) (x := F) hi)
  have hb := (Seminorm.le_def.mp hbound) (symbolSlice F p)
  change Q (symbolSlice F p)≤(A:ℝ)*
    (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p) at hb
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)
  change (Finset.Iic (4*q,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 (symbolSlice F p))≤(A:ℝ)*M at hfinal
  unfold symbolCoefficientBound
  exact add_le_add (mul_le_mul_of_nonneg_left hfinal (show (0:ℝ)≤2^(4*q) by positivity)) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single compactly supported master symbol for the normalized
annular multipliers. Its slices have uniform Fourier coefficient bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem masterCutoff_one (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) (hz : ‖z‖≤R) :
    masterCutoff R hR z=1 := by
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  change (b z : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa using hz)]
  norm_num

theorem masterSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (z : MasterSymbolSpace) :
    masterSymbol psi R hR z=psi (masterArgument z)*masterCutoff R hR z := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (psi.hasTemperateGrowth.comp masterArgument_temperate) _ _

theorem normalizedSchwartzSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=
      psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t)) := by
  rw [normalizedSchwartzSymbol, symbolSlice_apply, masterSymbol_apply]
  rfl

theorem normalizedSchwartzSymbol_one (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) (hxyz : ‖symbolPoint X Y U‖≤R) (hp : ‖(v,t)‖≤R) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  have hz : ‖(symbolPoint X Y U,(v,t))‖≤R := by
    rw [Prod.norm_def]
    exact max_le hxyz hp
  rw [normalizedSchwartzSymbol_apply,
    masterCutoff_one R hR (symbolPoint X Y U,(v,t)) hz, mul_one]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolRepresentation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier separation on the bounded frequency windows used for
the annular packet decomposition. Constants precede both scale parameters. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolPoint_norm_le (X Y U : ℝ) :
    ‖symbolPoint X Y U‖≤|X|+|Y|+|U| := by
  have hs : ‖symbolPoint X Y U‖^2=X^2+Y^2+U^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, symbolPoint, Fin.sum_univ_succ]
    ring
  nlinarith only [hs, norm_nonneg (symbolPoint X Y U), abs_nonneg X,
    abs_nonneg Y, abs_nonneg U, sq_abs X, sq_abs Y, sq_abs U,
    mul_nonneg (abs_nonneg X) (abs_nonneg Y),
    mul_nonneg (abs_nonneg X) (abs_nonneg U),
    mul_nonneg (abs_nonneg Y) (abs_nonneg U)]

/-- A cutoff which is one wherever the windowed annular symbol can be nonzero. -/
theorem normalizedSchwartzSymbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c M R : ℝ) (hR : 0<R) (hc : 0 < c)
    (hpsi : ∀ s : ℝ, M < |s| → psi s=0)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  by_cases hzero : psi (X+(v+t*Y)*U)=0
  · rw [normalizedSchwartzSymbol_apply, hzero, zero_mul]
  · have hann : |X+(v+t*Y)*U|≤M := by
      by_contra h
      exact hzero (hpsi _ (lt_of_not_ge h))
    have hU : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) hann
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    apply normalizedSchwartzSymbol_one
    · exact (symbolPoint_norm_le X Y U).trans ((add_le_add (add_le_add hX hY) hU).trans hsize)
    · exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth annular selector. Multiplying the separated selector
by this cutoff gives the required support away from the reference slope. -/
noncomputable section
open scoped ContDiff FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem annularCutoff_apply (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    annularCutoff a b ha hb U=selectorOuter b hb U*(1-selectorInner a ha U) := rfl

theorem annularCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (hlo : a≤|U|) (hhi : |U|≤b) : annularCutoff a b ha hb U=1 := by
  have hi : selectorInner a ha U=0 :=
    (selectorInner a ha).zero_of_le_dist (by simpa [selectorInner, Real.dist_eq] using hlo)
  have ho : selectorOuter b hb U=1 :=
    (selectorOuter b hb).one_of_mem_closedBall (by simpa [selectorOuter, Real.dist_eq] using hhi)
  rw [annularCutoff_apply, hi, ho]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPlancherel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-coordinate Plancherel and the common-frequency witness
needed for the actual planar packet Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

/-- Plancherel for the manuscript's product-coordinate Fourier transform. -/
theorem planar_integral_inner_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (planarFourier f z) (planarFourier g z) ∂volume.prod volume)=
      ∫ z, inner ℂ (f z) (g z) ∂volume.prod volume := by
  calc
    _ = ∫ x : HilbertPlane, inner ℂ (𝓕 (liftPlanar f) x) (𝓕 (liftPlanar g) x) := by
      rw [integral_hilbertPlane]
      simp only [fourier_liftPlanar]
    _ = ∫ x : HilbertPlane, inner ℂ (liftPlanar f x) (liftPlanar g x) :=
      SchwartzMap.integral_inner_fourier_fourier (liftPlanar f) (liftPlanar g)
    _ = _ := by
      rw [integral_hilbertPlane]
      rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

theorem planarFourier_integrable (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (planarFourier f) (volume.prod volume) := by
  have h : Integrable (planarFourierSchwartz f : ℝ×ℝ → ℂ) (volume.prod volume) :=
    (planarFourierSchwartz f).integrable
  simpa only [funext (planarFourierSchwartz_apply f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedSymbolIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact separated symbol with compact annular selectors. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem localized_symbol_identity (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (X Y U : ℝ) :
    (chi U : ℂ)*S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector chi S q nu U := by
  rw [weighted_symbol_identity S q X Y U, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with nu
  unfold localizedSelector
  ring

theorem localized_annular_multiplier (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R : ℝ) (hR : 0<R) (hc : 0 < c) (hC : 0<C) (ha : 0<a)
    (hM : 0<M) (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) (hVC : v+t*Y≤C) (q : ℕ) :
    psi (X+(v+t*Y)*U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector
          (annularCutoff (3*a/(4*C)) ((M+A)/c) (by positivity) (by positivity))
          (normalizedSchwartzSymbol psi R hR v t) q nu U := by
  rw [← localized_symbol_identity]
  have htail : ∀ s : ℝ, M < |s| → psi s=0 := by
    intro s hs
    by_contra hn
    exact (not_lt_of_ge (hpsi s hn).2) hs
  rw [normalizedSchwartzSymbol_eq psi A B c M R hR hc htail hsize v t X Y U hp hX hY hV]
  by_cases hz : psi (X+(v+t*Y)*U)=0
  · rw [hz, mul_zero]
  · have hlo := normalized_selector_lower X (v+t*Y) U a C ha hC
      (hc.le.trans hV) hVC (hX.trans hsmall) (hpsi _ hz).1
    have hhi : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) (hpsi _ hz).2
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    rw [annularCutoff_one _ _ _ _ U hlo hhi, Complex.ofReal_one, one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarFrequencyPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverseSchwartz_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz F x=planarInverse F x := by
  rw [← planarFourier_inversion (planarInverseSchwartz F) x]
  congr 1
  funext omega
  exact planarInverseSchwartz_fourier F omega

theorem affineFrequencyCharacter_temperate (a b c : ℝ) :
    Function.HasTemperateGrowth (fun omega : ℝ×ℝ =>
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact Function.HasTemperateGrowth.comp (g := fun t : ℝ => Complex.exp (t * Complex.I)) OAI.hasTemperateGrowth_exp_mul_I (by fun_prop)

theorem modulatedFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a b c : ℝ) (omega : ℝ×ℝ) :
    modulatedFrequencyWindow F a b c omega=
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)*F omega :=
  SchwartzMap.smulLeftCLM_apply_apply (affineFrequencyCharacter_temperate a b c) F omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedTranslatedProfiles
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights absorb translations of normalized packet
profiles. The estimates are uniform before all packet locations. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem translatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a : ℝ×ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (F.compSubConstCLM ℂ a)≤
      (1+‖a‖)^k*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  change ‖x‖^k*‖iteratedFDeriv ℝ n (fun z => F (z-a)) x‖≤_
  rw [iteratedFDeriv_comp_sub]
  have ht : ‖x‖≤‖x-a‖+‖a‖ := by
    convert norm_add_le (x-a) a using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  have hp : ‖x‖≤(1+‖a‖)*(1+‖x-a‖) := by
    nlinarith only [ht, norm_nonneg a, norm_nonneg (x-a),
      mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  calc
    _ ≤ ((1+‖a‖)*(1+‖x-a‖))^k*‖iteratedFDeriv ℝ n F (x-a)‖ := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp k) (norm_nonneg _)
    _ = (1+‖a‖)^k*((1+‖x-a‖)^k*‖iteratedFDeriv ℝ n F (x-a)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k,n)) le_rfl le_rfl F (x-a))
      (by positivity)

theorem weightedTranslatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) (ha : ‖a‖≤‖nu‖)
    (k n : ℕ) (hk : k≤q) :
    SchwartzMap.seminorm ℝ k n (weightedTranslatedProfile F q nu a)≤
      2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F := by
  have hweight : symbolWeight q nu*(1+‖a‖)^k≤1 := by
    have hpow : (1+‖a‖)^k≤(1+‖nu‖)^q :=
      (pow_le_pow_left₀ (by positivity) (by linarith only [ha]) k).trans
        (pow_le_pow_right₀ (by linarith only [norm_nonneg nu]) hk)
    unfold symbolWeight
    calc
      _ ≤ ((1+‖nu‖)^q)⁻¹*((1+‖nu‖)^q) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  rw [weightedTranslatedProfile, map_smul_eq_mul]
  simp only [Real.norm_eq_abs, abs_of_pos (symbolWeight_pos q nu)]
  calc
    _ ≤ symbolWeight q nu*((1+‖a‖)^k*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)) :=
      mul_le_mul_of_nonneg_left (translatedProfile_seminorm F a k n) (symbolWeight_pos q nu).le
    _ = (symbolWeight q nu*(1+‖a‖)^k)*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by ring
    _ ≤ 1*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := one_mul _

/-- Any fixed continuous seminorm has a uniformly weighted translation
bound. Its finite required order determines the weight exponent. -/
theorem weightedTranslatedProfile_bounded (F : SchwartzMap (ℝ×ℝ) ℂ)
    (P : Seminorm ℝ (SchwartzMap (ℝ×ℝ) ℂ)) (hP : Continuous P) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      P (weightedTranslatedProfile F q nu a)≤C := by
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ) P hP
  let M : ℝ := ∑ i ∈ s, 2^i.1*(Finset.Iic i).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F
  have hM : 0≤M := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨s.sup Prod.fst, (A:ℝ)*M+1, by positivity, ?_⟩
  intro q hq nu a ha
  have hs : (s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a)≤M := by
    apply Seminorm.finset_sup_apply_le hM
    intro i hi
    exact (weightedTranslatedProfile_seminorm F q nu a ha i.1 i.2 ((Finset.le_sup hi).trans hq)).trans
      (Finset.single_le_sum (f := fun j : ℕ×ℕ =>
        2^j.1*(Finset.Iic j).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)
          (fun j _ => by positivity) hi)
  have hb := (Seminorm.le_def.mp hbound) (weightedTranslatedProfile F q nu a)
  change P (weightedTranslatedProfile F q nu a)≤
    (A:ℝ)*(s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a) at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)).trans (by linarith)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_UniformTranslatedProfileBounds
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual profile constant used by the packet estimates is controlled
uniformly for the polynomially weighted translated profiles. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem profileJetCLM_apply (i : Fin 3) (F : PlanarSchwartz) :
    profileJetCLM i F=planarVerticalJet F i := by
  fin_cases i <;> rfl

theorem envelopeSeminorm_continuous (n : ℕ) : Continuous (envelopeSeminorm n) :=
  ((schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ).continuous_seminorm (0,0)).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun z : ℝ×ℝ => (planarPolynomialWeight n z:ℂ))).continuous)

theorem profileControlSeminorm_continuous (n : ℕ) : Continuous (profileControlSeminorm n) := by
  unfold profileControlSeminorm
  apply Seminorm.continuous_finsetSum
  intro i _
  exact (((envelopeSeminorm_continuous n).comp (profileJetCLM i).continuous).add
    ((envelopeSeminorm_continuous n).comp
      (profileHorizontalCLM.comp (profileJetCLM i)).continuous)).add
        ((envelopeSeminorm_continuous n).comp
          (profileVerticalCLM.comp (profileJetCLM i)).continuous)

theorem profileControlSeminorm_apply (n : ℕ) (F : PlanarSchwartz) :
    planarProfileConstant F n=profileControlSeminorm n F+9 := by
  have hpoint (i : Fin 3) :
      planarEnvelopeConstant (planarVerticalJet F i) n+
        planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet F i)) n+
        planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet F i)) n=
      (envelopeSeminorm n (profileJetCLM i F)+
        envelopeSeminorm n (profileHorizontalCLM (profileJetCLM i F))+
        envelopeSeminorm n (profileVerticalCLM (profileJetCLM i F)))+3 := by
    simp only [profileJetCLM_apply]
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=_
    change (envelopeSeminorm n (planarVerticalJet F i)+1)+
      (envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+1)+
      (envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i))+1)=
        (envelopeSeminorm n (planarVerticalJet F i)+
          envelopeSeminorm n (planarHorizontalDerivative (planarVerticalJet F i))+
          envelopeSeminorm n (planarVerticalDerivative (planarVerticalJet F i)))+3
    ring
  unfold planarProfileConstant
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  simp [profileControlSeminorm]

theorem uniform_translated_profile_bound (F : PlanarSchwartz) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      planarProfileConstant (weightedTranslatedProfile F q nu a) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := weightedTranslatedProfile_bounded F
    (profileControlSeminorm n) (profileControlSeminorm_continuous n)
  refine ⟨q₀,C+9,by linarith only [hC],?_⟩
  intro q hq nu a ha
  rw [profileControlSeminorm_apply]
  exact add_le_add (hbound q hq nu a ha) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketProfiles
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single Fourier parameter determines both normalized wave profiles.
Their common bound is chosen before all spatial scales and frequency bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem uniform_normalized_profile_pair (F G : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile F q nu) n ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) n ≤ C := by
  obtain ⟨qF,CF,hCF,hF⟩ := uniform_translated_profile_bound F n
  obtain ⟨qG,CG,hCG,hG⟩ := uniform_translated_profile_bound (reflectedConjugateProfile G) n
  refine ⟨max qF qG,max CF CG,lt_max_of_lt_left hCF,?_⟩
  intro q hq nu
  constructor
  · apply (hF q ((le_max_left _ _).trans hq) nu (-nu 0,0) ?_).trans (le_max_left _ _)
    simpa only [Prod.norm_def, norm_neg, norm_zero, max_eq_left (norm_nonneg _)] using
      PiLp.norm_apply_le nu 0
  · apply (hG q ((le_max_right _ _).trans hq) nu (0,nu 1) ?_).trans (le_max_right _ _)
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
      PiLp.norm_apply_le nu 1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarGramSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite Gram-matrix estimate to actual planar Schwartz
functions and their product-Lebesgue square integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem planar_toL2_norm_sq (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖f.toLp 2 (volume.prod volume)‖^2=∫ z, ‖f z‖^2 ∂volume.prod volume := by
  have h := SchwartzMap.inner_toL2_toL2_eq f f (volume.prod volume)
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  change ((‖f.toLp 2 (volume.prod volume)‖^2 : ℝ) : ℂ) =
    ∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂volume.prod volume at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoundedSupportedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate integrability follows from the vector indicator bound,
without a factor depending on the number of coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem bounded_supported_coordinate_integrable {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hbound : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hEfin : planeMeasure E≠∞)
    (hsupport : ∀ z, z∉E → g z=0) (k : κ) : Integrable (fun z => g z k) planeMeasure := by
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) planeMeasure :=
    (integrable_indicator_iff hE).2 (integrableOn_const (μ:=planeMeasure) hEfin)
  have hm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z∈E
  · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (g z) k).trans (hbound z)
  · simp only [Set.indicator_of_notMem hz,hsupport z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntegerSlopeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed angular lattice has local multiplicity independently of
its finite truncation. These bounds supply the model's label hypothesis. -/
noncomputable section
namespace LipschitzHilbert.SourceSlopeLabels

 theorem integer_slope_multiplicity_one (labels : Finset ℤ) (offset spacing : ℝ)
    (hspacing : 0 < spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) spacing 1 := by
  classical
  intro a
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hupper : spacing*((i:ℝ)-(j:ℝ)) < spacing := by linarith
  have hlower : spacing*((j:ℝ)-(i:ℝ)) < spacing := by linarith
  have hu : (i:ℝ)-(j:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hupper])
  have hl : (j:ℝ)-(i:ℝ)<1 := (mul_lt_mul_iff_right₀ hspacing).mp (by nlinarith only [hlower])
  have habs : |(i:ℝ)-(j:ℝ)|<1 := abs_lt.mpr ⟨by linarith,hu⟩
  have hInt : |i-j|<(1:ℤ) := by exact_mod_cast habs
  have habsInt := abs_lt.mp hInt
  omega

 theorem integer_slope_multiplicity (labels : Finset ℤ) (offset spacing precision : ℝ)
    (hspacing : 0 < spacing) (_hprecision : 0≤precision) (K : ℕ)
    (hK : precision≤2*K*spacing) :
    LocalMultiplicity labels (fun n : ℤ => offset+spacing*(n:ℝ)) precision (2*K+1) := by
  classical
  intro a
  have hlocal := integer_slope_multiplicity_one labels offset spacing hspacing
  apply (Finset.card_le_card (show labels.filter (fun n : ℤ =>
      a≤offset+spacing*(n:ℝ) ∧ offset+spacing*(n:ℝ)<a+precision) ⊆
      window labels (fun n : ℤ => offset+spacing*(n:ℝ)) (a+precision/2) spacing K from ?_)).trans
    ((window_card_le labels (fun n : ℤ => offset+spacing*(n:ℝ)) hspacing hlocal
      (le_refl (K:ℝ))).trans_eq (by omega))
  intro n hn
  obtain ⟨hn,hlo,hhi⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hn,abs_le.mpr ⟨?_,?_⟩⟩ <;> nlinarith

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FourierConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier multiplication by a Schwartz kernel is convolution for every
L1 input. This includes the measurable amplitude slices used after binning. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_l1_bound (f : ℝ×ℝ → ℂ) (omega : ℝ×ℝ) :
    ‖planarFourier f omega‖≤∫ z, ‖f z‖ ∂planeMeasure := by
  unfold planarFourier
  simpa only [Circle.norm_smul] using
    norm_integral_le_integral_norm (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f z)

theorem planarFourier_l1_continuous (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Continuous (planarFourier f) := by
  unfold planarFourier
  apply continuous_of_dominated (bound:=fun z => ‖f z‖)
  · intro omega
    exact ((show Continuous (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by fun_prop).aestronglyMeasurable.smul
      hf.aestronglyMeasurable)
  · intro omega
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  · exact hf.norm
  · exact Filter.Eventually.of_forall (fun z => by fun_prop)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable frequency envelopes justify multipliers and finite
recombination for L1 inputs, including discontinuous amplitude slices. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem variableFrequencyMultiplier_measurable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Measurable (variableFrequencyMultiplierL1 m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) :=
    (planarFourier_l1_continuous f hf).measurable.comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_integrand_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (z : ℝ×ℝ) :
    Integrable (fun omega => Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (m (z,omega)*planarFourier f omega)) planeMeasure := by
  have hp : Measurable (fun omega : ℝ×ℝ =>
      (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)) := by fun_prop
  have hm' : Measurable (fun omega => m (z,omega)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  apply (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure)).mono'
    (hp.mul (hm'.mul (planarFourier_l1_continuous f hf).measurable)).aestronglyMeasurable
  filter_upwards [] with omega
  change ‖(Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
    (m (z,omega)*planarFourier f omega)‖≤_
  rw [norm_mul,Circle.norm_coe,one_mul,norm_mul]
  exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
    (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))

theorem variableFrequencyMultiplier_bound_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplierL1 m f z‖≤
      (∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure) := by
  have h := norm_integral_le_of_norm_le (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure))
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
        q omega*(∫ x, ‖f x‖ ∂planeMeasure) from by
      rw [Circle.norm_smul,norm_mul]
      exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
        (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))))
  simpa only [variableFrequencyMultiplierL1,planeMeasure,integral_mul_const] using h

theorem variableFrequencyMultiplier_pairing_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplierL1 m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable_l1 m hm f hf).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul ((∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure))).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplierL1 m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound_l1 m q hq hbound f z) (norm_nonneg _)

theorem finite_variableFrequencyMultiplier_pairing_l1 {ι : Type*} [Fintype ι]
    (m : ι → (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : ∀ i, Measurable (m i))
    (q : ι → ℝ×ℝ → ℝ) (hq : ∀ i, Integrable (q i) planeMeasure)
    (hbound : ∀ i z omega, ‖m i (z,omega)‖≤q i omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1 (m i) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (fun p => ∑ i, m i p) f z*star (g z) ∂planeMeasure := by
  classical
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_pairing_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf g hg)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←Finset.sum_mul]
  congr 1
  unfold variableFrequencyMultiplierL1
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_integrand_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf z)]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Finset.sum_mul,Finset.smul_sum]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L1MultiplierDominatedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated convergence for the exact L1 frequency multiplier pairing.
The frequency envelope is fixed for a given finite band. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_tendsto_dominated
    (f : ℝ×ℝ → ℂ) (fseq : ℕ → (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure)
    (hseq : ∀ n, Integrable (fseq n) planeMeasure)
    (hbound : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hlim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (omega : ℝ×ℝ) :
    Tendsto (fun n => planarFourier (fseq n) omega) atTop (𝓝 (planarFourier f omega)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (show Continuous (fun x : ℝ×ℝ => Real.fourierChar (-(x.1*omega.1+x.2*omega.2))) by
      fun_prop).aestronglyMeasurable.smul (hseq n).aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rwa [Circle.norm_smul]
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul hx

theorem variableFrequencyMultiplier_tendsto_dominated
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hmb : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (fseq : ℕ → (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure)
    (hseq : ∀ n, Integrable (fseq n) planeMeasure)
    (hbound : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hlim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (z : ℝ×ℝ) :
    Tendsto (fun n => variableFrequencyMultiplierL1 m (fseq n) z) atTop
      (𝓝 (variableFrequencyMultiplierL1 m f z)) := by
  have hmass (n : ℕ) : (∫ x, ‖fseq n x‖ ∂planeMeasure)≤∫ x, ‖f x‖ ∂planeMeasure :=
    integral_mono_ae (hseq n).norm hf.norm (hbound n)
  have hmz : Measurable (fun omega => m (z,omega)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hp : Continuous (fun omega : ℝ×ℝ => Real.fourierChar (z.1*omega.1+z.2*omega.2)) := by fun_prop
  apply tendsto_integral_of_dominated_convergence (fun omega => q omega*(∫ x, ‖f x‖ ∂planeMeasure))
  · intro n
    exact hp.aestronglyMeasurable.smul
      (hmz.aestronglyMeasurable.mul (planarFourier_l1_continuous _ (hseq n)).aestronglyMeasurable)
  · exact hq.mul_const _
  · intro n
    filter_upwards [] with omega
    rw [Circle.norm_smul,norm_mul]
    exact mul_le_mul (hmb z omega) ((planarFourier_l1_bound (fseq n) omega).trans (hmass n))
      (norm_nonneg _) ((norm_nonneg _).trans (hmb z omega))
  · filter_upwards [] with omega
    exact tendsto_const_nhds.smul
      (tendsto_const_nhds.mul (planarFourier_tendsto_dominated f fseq hf hseq hbound hlim omega))

theorem variableFrequencyMultiplier_pairing_tendsto_dominated
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hmb : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f g : ℝ×ℝ → ℂ) (fseq gseq : ℕ → (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hg : Integrable g planeMeasure)
    (hfs : ∀ n, Integrable (fseq n) planeMeasure) (hgs : ∀ n, Integrable (gseq n) planeMeasure)
    (hfb : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hgb : ∀ n, ∀ᵐ x ∂planeMeasure, ‖gseq n x‖≤‖g x‖)
    (hflim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (hglim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => gseq n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ z, variableFrequencyMultiplierL1 m (fseq n) z*star (gseq n z) ∂planeMeasure)
      atTop (𝓝 (∫ z, variableFrequencyMultiplierL1 m f z*star (g z) ∂planeMeasure)) := by
  have hqpos : 0≤∫ omega, q omega ∂planeMeasure :=
    integral_nonneg (fun omega => (norm_nonneg (m (0,omega))).trans (hmb 0 omega))
  have hmass (n : ℕ) : (∫ x, ‖fseq n x‖ ∂planeMeasure)≤∫ x, ‖f x‖ ∂planeMeasure :=
    integral_mono_ae (hfs n).norm hf.norm (hfb n)
  have hvbound (n : ℕ) (z : ℝ×ℝ) : ‖variableFrequencyMultiplierL1 m (fseq n) z‖≤
      (∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure) :=
    (variableFrequencyMultiplier_bound_l1 m q hq hmb (fseq n) z).trans
      (mul_le_mul_of_nonneg_left (hmass n) hqpos)
  apply tendsto_integral_of_dominated_convergence
    (fun z => ((∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure))*‖g z‖)
  · intro n
    exact (variableFrequencyMultiplier_measurable_l1 m hm (fseq n) (hfs n)).aestronglyMeasurable.mul
      (hgs n).aestronglyMeasurable.star
  · exact hg.norm.const_mul _
  · intro n
    filter_upwards [hgb n] with z hz
    rw [norm_mul,norm_star]
    exact mul_le_mul (hvbound n z) hz (norm_nonneg _) (mul_nonneg hqpos (integral_nonneg (fun _ => norm_nonneg _)))
  · filter_upwards [hglim] with z hz
    exact (variableFrequencyMultiplier_tendsto_dominated m hm q hq hmb f fseq hf hfs hfb hflim z).mul hz.star

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NormalizedProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the finite derivative order and Fourier-decay exponent before
any packet lattice. Their fixed profile cost fits the model's logarithmic
budget once the disparity parameter is large enough. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem requiredPacketOrder_basic (D : ℕ) :
    207 ≤ requiredPacketOrder D ∧ 6+2*(8*D+1) ≤ requiredPacketOrder D :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem exists_normalized_profile_budget (F G : SchwartzMap (ℝ×ℝ) ℂ) (D : ℕ) :
    ∃ q : ℕ, 4≤q ∧ ∃ C L₀ : ℝ, 0<C ∧ 16≤L₀ ∧
      (∀ nu : SymbolSpace,
        planarProfileConstant (synthesisProfile F q nu) (2*requiredPacketOrder D) ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) (2*requiredPacketOrder D) ≤ C) ∧
      ∀ L : ℝ, L₀≤L →
        ((2:ℝ)^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D) ≤ L^(1:ℝ) := by
  obtain ⟨q₀,C,hC,hprofiles⟩ := uniform_normalized_profile_pair F G (2*requiredPacketOrder D)
  let budget : ℝ := (2^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D)
  refine ⟨max 4 q₀,le_max_left _ _,C,max 16 budget,hC,le_max_left _ _,?_,?_⟩
  · exact hprofiles (max 4 q₀) (le_max_right _ _)
  · intro L hL
    rw [Real.rpow_one]
    exact (le_max_right 16 budget).trans hL

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledWindowFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier coordinates of the normalized physical kernels.
The Jacobian is derived by two one-dimensional changes of variables. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem integral_packetCoordinates (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta : ℝ) (hl : l≠0) (hW : W≠0) :
    (∫ z, F (packetCoordinates l W theta hl hW z) ∂planeMeasure)=
      |l*W| • (∫ z, F z ∂planeMeasure) := by
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W theta hl hW) F
  have hi : Integrable (fun z => F (packetCoordinates l W theta hl hW z)) planeMeasure := G.integrable
  have hs (x : ℝ) : (∫ y : ℝ, F (x/l,(y-theta*x)/W))=
      |W| • (∫ y : ℝ, F (x/l,y)) := by
    rw [integral_sub_right_eq_self (fun y : ℝ => F (x/l,y/W)) (theta*x)]
    exact Measure.integral_comp_div (fun y : ℝ => F (x/l,y)) W
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, F (x/l,(y-theta*x)/W) := integral_prod _ hi
    _ = ∫ x : ℝ, |W| • (∫ y : ℝ, F (x/l,y)) :=
      integral_congr_ae (Filter.Eventually.of_forall hs)
    _ = |W| • (∫ x : ℝ, ∫ y : ℝ, F (x/l,y)) := integral_smul _ _
    _ = |W| • (|l| • (∫ x : ℝ, ∫ y : ℝ, F (x,y))) := by
      rw [Measure.integral_comp_div (fun x : ℝ => ∫ y : ℝ, F (x,y)) l]
    _ = _ := by
      rw [smul_smul, ← integral_prod _ F.integrable, abs_mul, mul_comm]

theorem normalizedSpatialKernel_fourier (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    planarFourier (normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  let X := symbolX l xi eta theta
  let Y := symbolY W eta center
  let G := modulatedFrequencyWindow F (-X) (-Y) 0
  have hpoint (z : ℝ×ℝ) :
      Real.fourierChar (-(z.1*xi+z.2*eta)) •
        normalizedSpatialKernel F l W theta (2*Real.pi*center) hl.ne' hW.ne' z=
      (l*W:ℂ)⁻¹*G (packetCoordinates l W theta hl.ne' hW.ne' z) := by
    simp only [normalizedSpatialKernel, smul_apply, smul_eq_mul, physicalPlanarPacket_apply,
      sub_zero, G, modulatedFrequencyWindow_apply]
    change (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
      ((l*W:ℂ)⁻¹*(Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)*
        F (z.1/l,(z.2-theta*z.1)/W)))=
      (l*W:ℂ)⁻¹*((Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ)*
        F (z.1/l,(z.2-theta*z.1)/W))
    have hp : (Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
        Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I)=
        (Real.fourierChar ((-X)*(z.1/l)+(-Y)*((z.2-theta*z.1)/W)+0):ℂ) := by
      rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
      congr 1
      dsimp [X,Y,symbolX,symbolY]
      push_cast
      field_simp [show (l:ℂ)≠0 by exact_mod_cast hl.ne', show (W:ℂ)≠0 by exact_mod_cast hW.ne']
      ring
    calc
      _ = (l*W:ℂ)⁻¹*((Real.fourierChar (-(z.1*xi+z.2*eta)):ℂ)*
          Complex.exp (((2*Real.pi*center)*(z.2-theta*z.1):ℝ)*Complex.I))*
            F (z.1/l,(z.2-theta*z.1)/W) := by ring
      _ = _ := by rw [hp]; ring
  have hint : (∫ z, G z ∂planeMeasure)=planarFourier F (X,Y) := by
    unfold planarFourier
    apply integral_congr_ae
    filter_upwards [] with z
    rw [modulatedFrequencyWindow_apply]
    change (Real.fourierChar ((-X)*z.1+(-Y)*z.2+0):ℂ)*F z=
      (Real.fourierChar (-(z.1*X+z.2*Y)):ℂ)*F z
    have he : (-X)*z.1+(-Y)*z.2+0= -(z.1*X+z.2*Y) := by ring
    rw [he]
  unfold planarFourier
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    integral_packetCoordinates G l W theta hl.ne' hW.ne', abs_of_pos (mul_pos hl hW)]
  rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_mul,
    inv_mul_cancel₀ (show (l:ℂ)*(W:ℂ)≠0 by exact_mod_cast (mul_pos hl hW).ne'), one_mul]
  exact hint

theorem scaledFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow F l W theta (2*Real.pi*center) hl.ne' hW.ne' (xi,eta)=
      planarFourier F (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow, planarFourierSchwartz_apply]
  exact normalizedSpatialKernel_fourier F l W theta center hl hW xi eta

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScaledWindowSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed frequency plateaus give the original narrow spectra for
both actual packet kernels, uniformly in their Fourier-series parameter. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem scaledWindow_inverse_profile_apply (chi : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center)
      hl.ne' hW.ne' (xi,eta)=chi (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow_apply _ l W theta center hl hW, planarInverseSchwartz_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SmoothSlopeSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth extension of the slope denominator gives the full normalized
symbol, including its slope partition and vertical frequency window. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem positiveDenominator_eq (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : c ≤ s) :
    positiveDenominator c s=s := by
  unfold positiveDenominator
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : (0:ℝ) < c/2)).2
    (by linarith only [hs])), one_mul]
  ring

theorem partitionedMasterSymbol_apply (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) :
    partitionedMasterSymbol psi rho beta c hc R hR z=
      masterCutoff R hR z*(psi (masterArgument z)*rho (masterSlopeArgument c z)*beta (z.1 1)) := rfl

theorem partitionedSymbol_uniform (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ v t : ℝ,
      symbolCoefficientBound (partitionedSymbol psi rho beta c hc R hR v t) q≤C := by
  obtain ⟨C,hC,h⟩ := symbolSlice_coefficient_uniform (partitionedMasterSymbol psi rho beta c hc R hR) q
  exact ⟨C,hC,fun v t => h (v,t)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedSymbolIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the full symbol, including the frequency-slope
partition and the vertical bin window, with annular selector support. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem partitionedSymbol_factor (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (v t X Y U : ℝ) :
    partitionedSymbol psi rho beta c hc R hR v t (symbolPoint X Y U)=
      normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)*
        rho (-X/positiveDenominator c (v+t*Y))*beta Y := by
  rw [partitionedSymbol, symbolSlice_apply, partitionedMasterSymbol_apply,
    normalizedSchwartzSymbol_apply]
  change masterCutoff R hR (symbolPoint X Y U,(v,t))*
      (psi (X+(v+t*Y)*U)*rho (-X/positiveDenominator c (v+t*Y))*beta Y)=
    psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t))*
      rho (-X/positiveDenominator c (v+t*Y))*beta Y
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RescaledAnnularSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed angular enlargement is an exact change of normalized
coordinates. The annular cutoff and the compact master symbol are still
one on every contributing frequency. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem rescaled_symbol_coordinates (H l w W theta center u xi eta : ℝ)
    (hH : H≠0) (hl : l≠0) (hw : w≠0) (hW : W≠0) :
    symbolX l xi eta theta+
      (H*w*center+(H*w/W)*symbolY W eta center)*symbolU l (H*w) u theta=
      l*(xi+u*eta) := by
  unfold symbolX symbolY symbolU
  field_simp
  ring

theorem rescaled_localized_symbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (l w W theta center u xi eta : ℝ) (hl : 0<l) (hw : 0<w) (hW : 0<W)
    (hparam : ‖(H*w*center,H*w/W)‖≤R)
    (hX : |symbolX l xi eta theta|≤A) (hY : |symbolY W eta center|≤B)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
      (symbolU l (H*w) u theta):ℂ)*
      normalizedSchwartzSymbol psi R hR (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta)) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hVhi : H*w*center+(H*w/W)*symbolY W eta center≤H*C := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hhi hH.le
  have heq := localized_annular_multiplier psi A B (H*c) (H*C) a M R hR
    (mul_pos hH hc) (mul_pos hH hC) ha hM hA hsmall hpsi hsize
    (H*w*center) (H*w/W) (symbolX l xi eta theta) (symbolY W eta center)
    (symbolU l (H*w) u theta) hparam hX hY hVlo hVhi 0
  rw [←localized_symbol_identity] at heq
  rw [rescaled_symbol_coordinates H l w W theta center u xi eta hH.ne' hl.ne' hw.ne' hW.ne'] at heq
  exact heq.symm


/-- A vertical frequency window inherits the original annulus from its
center and width, with the exact endpoint allowance. -/
theorem vertical_annulus_from_window (w W center eta B c C : ℝ)
    (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C)
    (hY : |symbolY W eta center|≤B) : c≤w*eta ∧ w*eta≤C := by
  have hy := abs_le.mp hY
  have hp : 0≤w/W := (div_pos hw hW).le
  have hcancel : (w/W)*symbolY W eta center=w*(eta-center) := by
    unfold symbolY
    field_simp
  have hleft := mul_le_mul_of_nonneg_left hy.1 hp
  have hright := mul_le_mul_of_nonneg_left hy.2 hp
  rw [hcancel] at hleft hright
  constructor <;> nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RescaledPartitionedSymbol
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope partition is rescaled together with the angular variable,
so its argument remains the original frequency slope divided by w/l. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem rescaled_partitioned_symbol_eq (psi rho beta : SchwartzMap ℝ ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (l w W theta center u xi eta : ℝ) (hl : 0<l) (hw : 0<w) (hW : 0<W)
    (hparam : ‖(H*w*center,H*w/W)‖≤R)
    (hX : |symbolX l xi eta theta|≤A) (hY : |symbolY W eta center|≤B)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
      (symbolU l (H*w) u theta):ℂ)*
      partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR
        (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta))*rho (-symbolX l xi eta theta/(w*eta))*beta (symbolY W eta center) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hwe : 0<w*eta := hc.trans_le hlo
  rw [partitionedSymbol_factor,positiveDenominator_eq (H*c) (mul_pos hH hc) _ hVlo,
    dilatedSlopeWindow_apply,hvertical]
  have hrho : H*(-symbolX l xi eta theta/(H*(w*eta)))=
      -symbolX l xi eta theta/(w*eta) := by field_simp
  rw [hrho]
  rw [←mul_assoc,←mul_assoc,
    rescaled_localized_symbol_eq psi A B c C a M R H hR hH hc hC ha hM hA hsmall
      hpsi hsize l w W theta center u xi eta hl hw hW hparam hX hY hlo hhi]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete compact smooth partition on an arithmetic slope lattice.
The finite sum is exactly one on its prescribed interval. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem slopePartition_apply (x : ℝ) : slopePartition x=(slopePartitionReal x : ℂ) := rfl

theorem slopePartition_support (x : ℝ) (hx : slopePartition x≠0) : |x|≤1 := by
  by_contra h
  have habs : 1 < |x| := lt_of_not_ge h
  have hxx : x≤-1 ∨ 1≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at habs
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at habs
      exact Or.inr habs.le
  have heq := slopePartitionReal_eq_zero x hxx
  exact hx (by rw [slopePartition_apply,heq,Complex.ofReal_zero])

theorem slopePartitionReal_sum (x : ℝ) (N : ℕ) :
    ∑ n∈Finset.range N, slopePartitionReal (x-(n:ℝ))=
      Real.smoothTransition (x+1)-Real.smoothTransition (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,slopePartitionReal]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

theorem slopePartition_sum_one (K : ℕ) (x : ℝ) (hx : |x|≤K) :
    ∑ n∈Finset.range (2*K+1), slopePartition (x+K-(n:ℝ))=1 := by
  simp only [slopePartition_apply,←Complex.ofReal_sum]
  rw [slopePartitionReal_sum]
  have hbounds := abs_le.mp hx
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnnularPacketGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical choices for the annular multiplier. The enlargement
and compact master radius depend only on its support and on the two
frequency-window widths. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ} (p : AnnularPacketGeometry A B c C a M)

theorem outer_pos : 0<p.outer := by unfold outer; positivity [p.H_pos,p.hc,p.hM,p.hA]

theorem parameter_bound (w W center : ℝ) (hw : 0<w) (hW : 0<W)
    (hwW : p.H*w≤W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    ‖(p.H*w*center,p.H*w/W)‖≤p.R := by
  have hratio : 0≤w/W := (div_pos hw hW).le
  have hpad : 0≤B*(w/W) := mul_nonneg p.hB hratio
  have hcenter : 0≤w*center := by linarith [p.hc]
  have hcenterHi : w*center≤C := by linarith
  have hleft : |p.H*w*center|≤p.H*C := by
    rw [abs_of_nonneg (by nlinarith [p.H_pos])]
    nlinarith [p.H_pos]
  have hright : |p.H*w/W|≤p.H := by
    rw [abs_of_pos (div_pos (mul_pos p.H_pos hw) hW)]
    have hh : p.H*w/W≤1 := (div_le_one hW).mpr hwW
    exact hh.trans p.hH
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (max_le_max hleft hright).trans p.radius

end AnnularPacketGeometry

/-- The required geometry follows from a narrow horizontal window; all
large constants are chosen before the scale, carrier, or row families. -/
theorem exists_annular_packet_geometry (A B c C a M : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hnarrow : A≤a/4) (hsep : A/c<(3*a/(4*C)/2)/4) :
    Nonempty (AnnularPacketGeometry A B c C a M) := by
  let a0 := 3*a/(4*C)
  let b0 := (M+A)/c
  have ha0 : 0<a0 := by dsimp [a0]; positivity
  have hb0 : 0<b0 := by dsimp [b0]; positivity
  obtain ⟨H,hH⟩ := exists_gt (max 1 (max (2*a0) (6*max (2*b0) (A/c+a0/2))))
  have hH1 : 1≤H := ((le_max_left _ _).trans hH.le)
  have hHp : 0<H := zero_lt_one.trans_le hH1
  have hHa : 2*a0<H := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  have hHcover : 6*max (2*b0) (A/c+a0/2)<H :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  let R := 1+max (A+B+(M+A)/(H*c)) (max (H*C) H)
  have hR : 0<R := by
    dsimp only [R]
    have h := (le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)).trans' (le_max_right (H*C) H)
    linarith
  have hpi : (2*Real.pi*A)/(2*Real.pi*(H*c))=(A/c)/H := by
    field_simp [Real.pi_ne_zero,hHp.ne',hc.ne']
  have haH : 3*a/(4*(H*C))=a0/H := by dsimp [a0]; ring
  have hbH : (M+A)/(H*c)=b0/H := by dsimp [b0]; ring
  refine ⟨⟨H,R,hA,hB,hc,hC,ha,hM,hH1,hR,hnarrow,?_,?_,?_,?_,?_⟩⟩
  · dsimp only [R]
    linarith [le_max_left (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · dsimp only [R]
    linarith [le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · rw [haH]
    have hh : a0/H≤1/2 := (div_le_iff₀ hHp).mpr (by linarith)
    linarith
  · rw [hpi,haH,show (a0/H/2)/4=(a0/2/4)/H by ring]
    exact div_lt_div_of_pos_right hsep hHp
  · rw [hpi,haH,hbH,show 2*(b0/H)=(2*b0)/H by ring,
      show (A/c)/H+(a0/H)/2=(A/c+a0/2)/H by ring,max_div_div_right hHp.le]
    have hh := (div_lt_one hHp).mpr hHcover
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RectangularFrequencyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed rectangular plateau supplies both convolution factors in the
finite band representation. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem rectangularFrequencyCutoff_apply (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ) :
    rectangularFrequencyCutoff A B hA hB z=(unitPlaneBump (z.1/(A/2),z.2/(B/2)):ℂ) := by
  change (unitPlaneBump (z.1/(A/2),(z.2-0*z.1)/(B/2)):ℂ)=_
  simp only [zero_mul,sub_zero]

theorem rectangularFrequencyCutoff_one (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hx : |z.1|≤A/2) (hy : |z.2|≤B/2) : rectangularFrequencyCutoff A B hA hB z=1 := by
  rw [rectangularFrequencyCutoff_apply]
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖≤1 := by
    change max |z.1/(A/2)| |z.2/(B/2)|≤1
    simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact max_le ((div_le_one (by positivity)).mpr hx) ((div_le_one (by positivity)).mpr hy)
  have ho : unitPlaneBump (z.1/(A/2),z.2/(B/2))=1 :=
    unitPlaneBump.one_of_mem_closedBall (by
      change dist (z.1/(A/2),z.2/(B/2)) 0≤1
      rw [dist_zero_right]
      exact hn)
  rw [ho]
  norm_num

theorem rectangularFrequencyCutoff_support (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hz : rectangularFrequencyCutoff A B hA hB z≠0) : |z.1|≤A ∧ |z.2|≤B := by
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖<2 := by
    by_contra h
    have hzero : unitPlaneBump (z.1/(A/2),z.2/(B/2))=0 :=
      unitPlaneBump.zero_of_le_dist (by
        change 2≤dist (z.1/(A/2),z.2/(B/2)) 0
        rw [dist_zero_right]
        exact le_of_not_gt h)
    apply hz
    rw [rectangularFrequencyCutoff_apply,hzero]
    norm_num
  change max |z.1/(A/2)| |z.2/(B/2)|<2 at hn
  simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2),max_lt_iff] at hn
  constructor
  · have hh := (div_lt_iff₀ (by positivity : 0<A/2)).mp hn.1
    linarith
  · have hh := (div_lt_iff₀ (by positivity : 0<B/2)).mp hn.2
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SlopePartitionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite smooth partition uses the same arithmetic labels as
the packet model; their local multiplicity is uniform in the truncation. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceSlopeLabels

theorem injective_integer_multiplicity {ι : Type*} [Fintype ι]
    (index : ι → ℤ) (hinj : Function.Injective index)
    (offset spacing precision : ℝ) (hs : 0 < spacing) (hp : 0≤precision)
    (K : ℕ) (hK : precision≤2*K*spacing) :
    LocalMultiplicity Finset.univ (fun i => offset+spacing*(index i:ℝ)) precision (2*K+1) := by
  classical
  have h := integer_slope_multiplicity (Finset.univ.image index) offset spacing precision hs hp K hK
  intro a
  apply (Finset.card_le_card_of_injOn index ?_ (fun _ _ _ _ heq => hinj heq)).trans (h a)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hi).2⟩

end LipschitzHilbert.SourceSlopeLabels
namespace LipschitzHilbert.PacketRepresentation

theorem scaledSlopePartition_apply (delta : ℝ) (hd : 0<delta) (x : ℝ) :
    scaledSlopePartition delta hd x=slopePartition (x/delta) := by
  rw [scaledSlopePartition,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem scaledSlopePartition_support (delta : ℝ) (hd : 0<delta) (x : ℝ)
    (hx : scaledSlopePartition delta hd x≠0) : |x|≤delta := by
  rw [scaledSlopePartition_apply] at hx
  have h := slopePartition_support _ hx
  rw [abs_div,abs_of_pos hd] at h
  exact (div_le_one hd).mp h

theorem finiteSlopePartition_sum (K : ℕ) (delta d s : ℝ) (hdelta : 0<delta) (hd : 0<d)
    (hcover : |s/(delta*d)|≤K) :
    ∑ n∈finiteSlopeLabels K,
      scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=1 := by
  have heq (n : ℕ) : scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=
      slopePartition (s/(delta*d)+K-(n:ℝ)) := by
    rw [scaledSlopePartition_apply]
    congr 1
    unfold finiteSlopeCenter
    field_simp
    ring
  simp_rw [heq]
  exact slopePartition_sum_one K (s/(delta*d)) hcover

theorem exists_finiteSlopeCenter_multiplicity (delta H : ℝ) (hdelta : 0<delta) (hH : 0≤H) :
    ∃ M : ℕ, ∀ (K : ℕ) (d : ℝ), 0<d →
      SourceSlopeLabels.LocalMultiplicity (Finset.univ : Finset (finiteSlopeLabels K))
        (fun n => finiteSlopeCenter K delta d n.val) (H*d) M := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (H/(2*delta))
  refine ⟨2*J+1,?_⟩
  intro K d hd
  have hJ' := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hdelta)).mp hJ
  have hh : H*d≤2*J*(delta*d) := by nlinarith
  have hi : Function.Injective (fun n : finiteSlopeLabels K => (n.val:ℤ)) := by
    intro x y h
    change (x.val:ℤ)=(y.val:ℤ) at h
    exact Subtype.ext (Int.ofNat.inj h)
  have h := SourceSlopeLabels.injective_integer_multiplicity
    (fun n : finiteSlopeLabels K => (n.val:ℤ)) hi (-delta*d*K) (delta*d) (H*d)
    (mul_pos hdelta hd) (mul_nonneg hH hd.le) J hh
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [finiteSlopeCenter,Int.cast_natCast]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedFrequencySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete slope-partitioned frequency symbol is uniformly bounded
and measurable, including at the zero of its vertical denominator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem partitionedFrequencySymbol_measurable (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (partitionedFrequencySymbol psi rho beta l W w theta center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold partitionedFrequencySymbol symbolX symbolY
  apply Measurable.mul
  · apply Measurable.mul
    · apply psi.continuous.measurable.comp
      fun_prop
    · apply rho.continuous.measurable.comp
      fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

theorem partitionedFrequencySymbol_bound (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (z omega : ℝ×ℝ) :
    ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤
      SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta := by
  unfold partitionedFrequencySymbol
  rw [norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _) (SchwartzMap.norm_le_seminorm ℝ rho _)
      (norm_nonneg _) (apply_nonneg _ _))
    (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (by positivity)

theorem sum_partitionedFrequencySymbol {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center : ℝ) (theta : ι → ℝ)
    (u : ℝ×ℝ → ℝ)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1) :
    (fun p => ∑ i, partitionedFrequencySymbol psi rho beta l W w (theta i) center u p)=
      annularBandSymbol psi beta l W center u := by
  classical
  funext p
  rcases p with ⟨z,omega⟩
  unfold partitionedFrequencySymbol annularBandSymbol
  by_cases hp : psi (l*(omega.1+u z*omega.2))=0
  · simp only [hp,zero_mul,Finset.sum_const_zero]
  by_cases hb : beta (symbolY W omega.2 center)=0
  · simp only [hb,mul_zero,Finset.sum_const_zero]
  rw [←Finset.sum_mul,←Finset.mul_sum,hpartition z omega hp hb,mul_one]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularFrequencyEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded direction and compact annular and vertical windows give a
single integrable frequency envelope, uniformly in the spatial point. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_support_bounds
    (psi beta : SchwartzMap ℝ ℂ) (l W center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) (z omega : ℝ×ℝ)
    (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    |omega.1|≤M/l+U*(|center|+B/W) ∧ |omega.2|≤|center|+B/W := by
  have hy := hbeta _ hb
  change |W*(omega.2-center)|≤B at hy
  rw [abs_mul,abs_of_pos hW] at hy
  have hy' : |omega.2-center|≤B/W := (le_div_iff₀ hW).mpr (by nlinarith)
  have hy'' : |omega.2|≤|center|+B/W := by
    calc
      |omega.2|=|(omega.2-center)+center| := by congr 1; ring
      _≤|omega.2-center|+|center| := abs_add_le _ _
      _≤|center|+B/W := by linarith
  have hx := hpsi _ hp
  rw [abs_mul,abs_of_pos hl] at hx
  have hx' : |omega.1+u z*omega.2|≤M/l := (le_div_iff₀ hl).mpr (by nlinarith)
  refine ⟨?_,hy''⟩
  calc
    |omega.1|=|(omega.1+u z*omega.2)-(u z*omega.2)| := by congr 1; ring
    _≤|omega.1+u z*omega.2|+|u z*omega.2| := abs_sub _ _
    _≤M/l+U*(|center|+B/W) := by
      rw [abs_mul]
      exact add_le_add hx' (mul_le_mul (hu z) hy'' (abs_nonneg _) hU)

theorem exists_frequency_rectangle_envelope
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (C R S : ℝ)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (hsupport : ∀ z omega, m (z,omega)≠0 → |omega.1|≤R ∧ |omega.2|≤S) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖m (z,omega)‖≤q omega := by
  let s : Set (ℝ×ℝ) := Icc (-R) R ×ˢ Icc (-S) S
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfin : planeMeasure s≠∞ := (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  refine ⟨s.indicator (fun _ => C), (integrableOn_const hfin).integrable_indicator hs,?_⟩
  intro z omega
  by_cases hm : m (z,omega)=0
  · have hC : 0≤C := (norm_nonneg (m (z,omega))).trans (hbound z omega)
    rw [hm,norm_zero]
    exact indicator_nonneg (fun _ _ => hC) _
  · have hmem : omega∈s := by
      obtain ⟨hR,hS⟩ := hsupport z omega hm
      exact ⟨abs_le.mp hR,abs_le.mp hS⟩
    rw [indicator_of_mem hmem]
    exact hbound z omega

theorem exists_partitionedFrequencySymbol_envelope
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w theta center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤q omega := by
  apply exists_frequency_rectangle_envelope _
    (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta)
    (M/l+U*(|center|+B/W)) (|center|+B/W)
    (partitionedFrequencySymbol_bound psi rho beta l W w theta center u)
  intro z omega hm
  have hp : psi (l*(omega.1+u z*omega.2))≠0 := by
    intro hp; exact hm (by simp [partitionedFrequencySymbol,hp])
  have hb : beta (symbolY W omega.2 center)≠0 := by
    intro hb; exact hm (by simp [partitionedFrequencySymbol,hb])
  exact annularBandSymbol_support_bounds psi beta l W center M B U hl hW hU hpsi hbeta u hu z omega hp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_measurable (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (annularBandSymbol psi beta l W center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold annularBandSymbol symbolY
  apply Measurable.mul
  · apply psi.continuous.measurable.comp
    fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

theorem exists_annularBandSymbol_envelope
    (psi beta : SchwartzMap ℝ ℂ) (l W center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖annularBandSymbol psi beta l W center u (z,omega)‖≤q omega := by
  apply exists_frequency_rectangle_envelope _
    (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 beta)
    (M/l+U*(|center|+B/W)) (|center|+B/W)
  · intro z omega
    unfold annularBandSymbol
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (apply_nonneg _ _)
  · intro z omega hm
    have hp : psi (l*(omega.1+u z*omega.2))≠0 := by
      intro hp; exact hm (by simp [annularBandSymbol,hp])
    have hb : beta (symbolY W omega.2 center)≠0 := by
      intro hb; exact hm (by simp [annularBandSymbol,hb])
    exact annularBandSymbol_support_bounds psi beta l W center M B U hl hW hU hpsi hbeta u hu z omega hp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSlopePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an annular multiplier, bounded output directions imply a finite
range of frequency slopes. The constructed arithmetic partition covers
that entire range, with no remaining partition-of-unity premise. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annular_normalized_slope_bound (l w delta c M U u xi eta : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hu : |u|≤U) (hfreq : |l*(xi+u*eta)|≤M) (hvertical : c≤w*eta) :
    |(-xi/eta)/(delta*(w/l))|≤U/(delta*(w/l))+M/(delta*c) := by
  have hdw : 0<delta*(w/l) := mul_pos hd (div_pos hw hl)
  have hV : 0<w*eta := hc.trans_le hvertical
  have heta : eta≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have heq : (-xi/eta)/(delta*(w/l))=
      u/(delta*(w/l))-(l*(xi+u*eta))/(delta*(w*eta)) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |u/(delta*(w/l))|+|(l*(xi+u*eta))/(delta*(w*eta))| := abs_sub _ _
    _ = |u|/(delta*(w/l))+|l*(xi+u*eta)|/(delta*(w*eta)) := by
      rw [abs_div,abs_div,abs_of_pos hdw,abs_of_pos (mul_pos hd hV)]
    _ ≤ U/(delta*(w/l))+M/(delta*c) := add_le_add
      (div_le_div_of_nonneg_right hu hdw.le)
      ((div_le_div_of_nonneg_right hfreq (mul_pos hd hV).le).trans
        (div_le_div_of_nonneg_left hM (mul_pos hd hc)
          (mul_le_mul_of_nonneg_left hvertical hd.le)))

theorem finiteSlopePartition_annular (psi beta : SchwartzMap ℝ ℂ)
    (K : ℕ) (l W w delta c M U center : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ eta, beta (symbolY W eta center)≠0 → c≤w*eta)
    (hK : U/(delta*(w/l))+M/(delta*c)≤K)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U)
    (z omega : ℝ×ℝ) (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    ∑ n : finiteSlopeLabels K, scaledSlopePartition delta hd
      (-symbolX l omega.1 omega.2 (finiteSlopeCenter K delta (w/l) n.val)/(w*omega.2))=1 := by
  have hV := hc.trans_le (hbeta omega.2 hb)
  have heta : omega.2≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have hcover : |(-omega.1/omega.2)/(delta*(w/l))|≤K :=
    (annular_normalized_slope_bound l w delta c M U (u z) omega.1 omega.2
      hl hw hd hc hM (hu z) (hpsi _ hp) (hbeta _ hb)).trans hK
  have hsum := finiteSlopePartition_sum K delta (w/l) (-omega.1/omega.2) hd (div_pos hw hl) hcover
  rw [←Finset.sum_attach] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  unfold symbolX
  field_simp
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalGeometryChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete choice of the narrow frequency plateau and slope spacing
for every fixed positive annular support. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exists_diagonal_geometry (B c C a M : ℝ) (hB : 0<B)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M) :
    ∃ A delta : ℝ, ∃ _p : AnnularPacketGeometry A B c C a M,
      0<A ∧ 0<delta ∧ delta*C≤A/2 := by
  let A := min (a/8) (3*a*c/(128*C))
  have hA : 0<A := lt_min (by positivity) (by positivity)
  have hnarrow : A≤a/4 := (min_le_left _ _).trans (by linarith)
  have hAc : A/c≤3*a/(128*C) := by
    apply (div_le_iff₀ hc).mpr
    convert min_le_right (a/8) (3*a*c/(128*C)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsep : A/c<(3*a/(4*C)/2)/4 := by
    have hp : 0<3*a/(128*C) := by positivity
    have heq : (3*a/(4*C)/2)/4=4*(3*a/(128*C)) := by ring
    rw [heq]
    linarith
  obtain ⟨p⟩ := exists_annular_packet_geometry A B c C a M hA.le hB.le hc hC ha hM hnarrow hsep
  let delta := A/(4*C)
  have hd : 0<delta := by dsimp [delta]; positivity
  have hdelta : delta*C≤A/2 := by
    have heq : delta*C=A/4 := by dsimp [delta]; field_simp
    rw [heq]
    linarith
  exact ⟨A,delta,p,hA,hd,hdelta⟩

theorem center_frequency_bounds (B c C w W center : ℝ)
    (hB : 0≤B) (hc : 0 < c) (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    (2*Real.pi*c)/w≤|2*Real.pi*center| ∧ |2*Real.pi*center|≤(2*Real.pi*C)/w := by
  have hp : 0≤B*(w/W) := by positivity
  have hcenter : 0 < center := by nlinarith
  rw [abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hcenter)]
  constructor
  · apply (div_le_iff₀ hw).mpr
    nlinarith [Real.pi_pos]
  · apply (le_div_iff₀ hw).mpr
    nlinarith [Real.pi_pos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite representation including the manuscript slope partition
and the vertical bin window. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem normalizedSymbolSum_eq_partitioned_annular_l1
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hparam : ∀ k, ‖(H*w*center k,H*w/width)‖≤R)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    normalizedSymbolSumL1 chiA chiB
      (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity))
      topLength width (H*w) htop hwidth labels theta center
      (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)) u f g =
      partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth labels theta center u f g := by
  classical
  unfold normalizedSymbolSumL1 partitionedAnnularSumL1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hz : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=0
  · simp only [hz,zero_mul,mul_zero,smul_zero]
  have hwindow : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=
      chiA (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
        symbolY width omega.2 (center k)) := by
    exact scaledWindow_inverse_profile_apply chiA _ width _ _
      (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2
  obtain ⟨hX,hY⟩ := hchiA _ (by simpa only [hwindow] using hz)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY
  have heq := rescaled_partitioned_symbol_eq psi rho beta A B c C a M R H hR hH hc hC ha hM hA hsmall
    hpsi hsize (latticeLength topLength labels i) w width (theta i.1 i.2) (center k) (u z)
    omega.1 omega.2 (latticeLength_pos topLength htop labels i) hw hwidth (hparam k) hX hY hVlo hVhi
  simp only [Circle.smul_def,smul_eq_mul]
  calc
    _ = (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
        (((annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
          (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2)):ℂ)*
          partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)
            (symbolPoint (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2))
              (symbolY width omega.2 (center k))
              (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2))))*
          (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
            latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
            planarFourier (f k) omega)) := by ring
    _ = _ := by rw [heq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite partitioned annular multiplier has a uniform basic bound.
The fixed symbol and profile costs are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_partitioned_annular_basic_l1 (hVariation : LepingleInput)
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M : ℝ) (p : AnnularPacketGeometry A B c C a M) (multiplicity : ℕ)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → p.H*w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/(p.H*w)) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) → (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth
        labels theta center u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨q,hq,Cprofile,_Lp,hCp,_hLp,hprofiles,_hbudget⟩ :=
    exists_normalized_profile_budget (planarInverseSchwartz chiA) (planarInverseSchwartz chiB) 0
  obtain ⟨Csymbol,hCs,hS⟩ := partitionedSymbol_uniform psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
    (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR q
  obtain ⟨K,hK,hbasic⟩ := exists_normalized_symbol_basic_l1 hVariation chiA chiB q hq
    A B (2*Real.pi*(p.H*c)) (2*Real.pi*(p.H*C)) p.inner p.outer Cprofile Csymbol
    multiplicity (requiredPacketOrder 0) p.hA p.hB (by positivity [p.H_pos,p.hc])
    (by positivity [p.H_pos,p.hC]) p.inner_pos p.outer_pos p.quarter
    hCp hCs (requiredPacketOrder_basic 0).1 p.separation p.coverage p.numerics
    hchiA hchiB hprofiles
  refine ⟨K,hK,?_⟩
  intro N κ Label _ topLength width w F htop hwidth hw hW hF labels theta center
    hfrequency hlo hhi hlocal u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs
  have hscaledLo (k : κ) : 2*Real.pi*(p.H*c)+(2*Real.pi*B)*((p.H*w)/width)≤
      (p.H*w)*(2*Real.pi*center k) := by
    first | (convert mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos])).trans (le_of_eq (by ring)))
  have hscaledHi (k : κ) : (p.H*w)*(2*Real.pi*center k)+(2*Real.pi*B)*((p.H*w)/width)≤
      2*Real.pi*(p.H*C) := by
    first | (convert mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos])).trans (le_of_eq (by ring)))
  rw [←normalizedSymbolSum_eq_partitioned_annular_l1 psi rho beta chiA chiB A B c C a M p.R p.H p.hR p.H_pos
    p.hc p.hC p.ha p.hM p.hA p.narrow hpsi p.size hchiA topLength width w htop hwidth hw
    labels theta center (fun k => p.parameter_bound w width (center k) hw hwidth hW (hlo k) (hhi k))
    hlo hhi u f g]
  exact hbasic N κ Label topLength width (p.H*w) F htop hwidth (mul_pos p.H_pos hw) hW hF
    labels theta center hfrequency hscaledLo hscaledHi hlocal
    (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
      (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR (p.H*w*center k) (p.H*w/width))
    (fun _ k => hS _ _) u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedBandFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the two auxiliary frequency plateaus from the actual
partitioned multiplier. They equal one on its contributing frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem partitionedAnnularSum_eq_finitePartitionedBand_l1
    (psi beta : SchwartzMap ℝ ℂ) (A B c C delta : ℝ)
    (hA : 0<A) (hB : 0<B) (hc : 0 < c) (hdelta : 0<delta) (hnarrow : delta*C≤A/2)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    partitionedAnnularSumL1 psi (scaledSlopePartition delta hdelta) beta
      (rectangularFrequencyCutoff A B hA hB) (rectangularFrequencyCutoff A B hA hB)
      topLength width w htop hwidth labels theta center u f g=
      finitePartitionedBandL1 psi (scaledSlopePartition delta hdelta) beta topLength width w
        labels theta center u f g := by
  classical
  unfold partitionedAnnularSumL1 finitePartitionedBandL1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hb : beta (symbolY width omega.2 (center k))=0
  · simp only [hb,mul_zero,zero_mul,smul_zero]
  by_cases hr : scaledSlopePartition delta hdelta
      (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))=0
  · simp only [hr,mul_zero,zero_mul,smul_zero]
  have hY := hbeta _ hb
  have hY' : |symbolY width omega.2 (center k)|≤B := hY.trans (by linarith)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY'
  have hVp : 0<w*omega.2 := hc.trans_le hVlo
  have hX := scaledSlopePartition_support delta hdelta _ hr
  rw [abs_div,abs_neg,abs_of_pos hVp] at hX
  have hX' : |symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)|≤A/2 :=
    ((div_le_iff₀ hVp).mp hX).trans ((mul_le_mul_of_nonneg_left hVhi hdelta.le).trans hnarrow)
  have hwindow : latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=1 := by
    rw [show latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=
      rectangularFrequencyCutoff A B hA hB
        (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
          symbolY width omega.2 (center k)) from
      scaledWindow_inverse_profile_apply _ _ width _ _
        (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2]
    exact rectangularFrequencyCutoff_one A B hA hB _ hX' hY
  simp only [hwindow,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWindowRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarge the vertical reference width together with the auxiliary
angular precision. This leaves the physical multiplier and W/w unchanged. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticallyRescaledWindow_apply (beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H) (y : ℝ) :
    verticallyRescaledWindow beta H hH y=beta (y/H) := by
  rw [verticallyRescaledWindow,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem verticallyRescaledWindow_symbolY (beta : SchwartzMap ℝ ℂ)
    (H W eta center : ℝ) (hH : 0<H) :
    verticallyRescaledWindow beta H hH (symbolY (H*W) eta center)=beta (symbolY W eta center) := by
  rw [verticallyRescaledWindow_apply]
  congr 1
  unfold symbolY
  field_simp

theorem verticallyRescaledWindow_support (beta : SchwartzMap ℝ ℂ)
    (B H : ℝ) (hH : 0<H) (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (y : ℝ) (hy : verticallyRescaledWindow beta H hH y≠0) : |y|≤(H*B)/2 := by
  rw [verticallyRescaledWindow_apply] at hy
  have h := hbeta (y/H) hy
  rw [abs_div,abs_of_pos hH] at h
  have hh := (div_le_iff₀ hH).mp h
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWindowRescalingL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finitePartitionedBand_vertical_rescaling_l1 {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
    (psi rho beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    finitePartitionedBandL1 psi rho (verticallyRescaledWindow beta H hH) topLength (H*width) w
      labels theta center u f g=finitePartitionedBandL1 psi rho beta topLength width w
        labels theta center u f g := by
  unfold finitePartitionedBandL1
  simp_rw [verticallyRescaledWindow_symbolY]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedFrequencyL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite slope recombination for L1 inputs, with all frequency
interchanges justified by the compact annular envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem recombine_partitioned_frequency_pairing_l1 {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center M B U : ℝ) (theta : ι → ℝ)
    (hl : 0<l) (hW : 0<W)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (hub : ∀ z, |u z|≤U)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1
      (partitionedFrequencySymbol psi rho beta l W w (theta i) center u) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (annularBandSymbol psi beta l W center u) f z*star (g z) ∂planeMeasure := by
  classical
  have henv (i : ι) := exists_partitionedFrequencySymbol_envelope psi rho beta
    l W w (theta i) center M B U hl hW ((abs_nonneg (u 0)).trans (hub 0)) hpsi hbeta u hub
  choose q hq hbound using henv
  rw [finite_variableFrequencyMultiplier_pairing_l1
    (fun i => partitionedFrequencySymbol psi rho beta l W w (theta i) center u)
    (fun i => partitionedFrequencySymbol_measurable psi rho beta l W w (theta i) center u hu)
    q hq hbound f hf g hg,
    sum_partitionedFrequencySymbol psi rho beta l W w center theta u hpartition]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic slope partition recombines exactly into the finite
vector-valued diagonal band operator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finitePartitionedBand_eq_diagonal_l1 {N : ℕ} {κ : Type} [Fintype κ]
    (psi beta : SchwartzMap ℝ ℂ) (K : Fin N → ℕ)
    (topLength width w delta c M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w) (hd : 0<delta) (hc : 0 < c) (hM : 0≤M)
    (hbetaSupport : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ k eta, beta (symbolY width eta (center k))≠0 → c≤w*eta)
    (hK : ∀ j, U/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)≤K j)
    (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f : κ → (ℝ×ℝ) → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : ∀ k, Integrable (f k) planeMeasure)
    (hg : ∀ k, Integrable (fun z => g z k) planeMeasure) :
    finitePartitionedBandL1 psi (scaledSlopePartition delta hd) beta topLength width w
      (fun j => finiteSlopeLabels (K j))
      (fun j n => finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val)
      center u f g=finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g := by
  classical
  unfold finitePartitionedBandL1 finiteDiagonalBandL1
  dsimp only [LatticeRow]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hlen : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  exact recombine_partitioned_frequency_pairing_l1 psi (scaledSlopePartition delta hd) beta
    (topLength/(2:ℝ)^j.val) width w (center k) M B U
    (fun n : finiteSlopeLabels (K j) =>
      finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val) hlen hwidth hpsi hbetaSupport u hum hu
    (finiteSlopePartition_annular psi beta (K j) (topLength/(2:ℝ)^j.val) width w delta c M U
      (center k) hlen hw hd hc hM hpsi (hbeta k) (hK j) u hu) (f k) (hf k) (fun z => g z k) (hg k)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform basic estimate for the actual finite diagonal band form.
Slope labels, plateaus, compact symbols, and profile budgets are all
constructed inside the proof. The scalar width W=w is included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_basic_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta : ℝ)
    (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
    (hd : 0<delta) (hnarrow : delta*C≤A/2)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w F : ℝ), 0<topLength → 0<width → 0<w → w≤width → 0≤F →
    ∀ (center : κ → ℝ), (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  let p' := p.enlargeVertical
  let beta' := verticallyRescaledWindow beta p.H p.H_pos
  let chi := rectangularFrequencyCutoff A (p.H*B) hA (mul_pos p.H_pos hB)
  obtain ⟨multiplicity,hmult⟩ := exists_finiteSlopeCenter_multiplicity delta p.H hd p.H_pos.le
  obtain ⟨K,hK,hmain⟩ := exists_partitioned_annular_basic_l1 hVariation psi
    (scaledSlopePartition delta hd) beta' chi chi A (p.H*B) c C a M p' multiplicity
    hpsi (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
    (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w F htop hwidth hw hwW hF center hfrequency hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  have hfint : ∀ k, Integrable (f k) planeMeasure := by
    intro k
    exact (bounded_supported_coordinate_integrable fData hfm hfb Fset hFset hFfin hfs k).congr
      (Filter.Eventually.of_forall (fun z => (hf z k).symm))
  let Krow (j : Fin N) : ℕ := ⌈1/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)⌉₊
  let labels := fun j : Fin N => finiteSlopeLabels (Krow j)
  let theta := fun (j : Fin N) (n : labels j) =>
    finiteSlopeCenter (Krow j) delta (w/(topLength/(2:ℝ)^j.val)) n.val
  have hlocal (j : Fin N) : SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
      ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity := by
    simpa only [theta,mul_div_assoc] using hmult (Krow j) (w/(topLength/(2:ℝ)^j.val))
      (div_pos hw (div_pos htop (pow_pos (by norm_num) _)))
  have hscale (k : κ) : |2*Real.pi*center k|≤(p.H*F)/(p.H*w) := by
    rw [mul_div_mul_left F w p.H_pos.ne']
    exact hfrequency k
  have hpad : (p.H*B)*(w/(p.H*width))=B*(w/width) := by field_simp [p.H_pos.ne',hwidth.ne']
  have hlo' (k : κ) : c+(p.H*B)*(w/(p.H*width))≤w*center k := by rw [hpad]; exact hlo k
  have hhi' (k : κ) : w*center k+(p.H*B)*(w/(p.H*width))≤C := by rw [hpad]; exact hhi k
  have hout := hmain N κ (fun _ : Fin N => ℕ) topLength (p.H*width) w (p.H*F)
    htop (mul_pos p.H_pos hwidth) hw (mul_le_mul_of_nonneg_left hwW p.H_pos.le)
    (mul_nonneg p.H_pos.le hF) labels theta center hscale hlo' hhi' hlocal
    u hum f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  rw [partitionedAnnularSum_eq_finitePartitionedBand_l1 psi beta' A (p.H*B) c C delta
    hA (mul_pos p.H_pos hB) p.hc hd hnarrow
    (verticallyRescaledWindow_support beta B p.H p.H_pos hbeta)
    topLength (p.H*width) w htop (mul_pos p.H_pos hwidth) hw labels theta center
    hlo' hhi' u f g] at hout
  rw [finitePartitionedBand_vertical_rescaling_l1 psi (scaledSlopePartition delta hd) beta
    p.H p.H_pos topLength width w labels theta center u f g] at hout
  have hbetaband (k : κ) (eta : ℝ) (hb : beta (symbolY width eta (center k))≠0) : c≤w*eta := by
    exact (vertical_annulus_from_window w width (center k) eta B c C hw hwidth
      (hlo k) (hhi k) ((hbeta _ hb).trans (by linarith))).1
  rw [finitePartitionedBand_eq_diagonal_l1 psi beta Krow topLength width w delta c M (B/2) 1
    htop hwidth hw hd p.hc p.hM.le hbeta center (fun s hs => (hpsi s hs).2) hbetaband
    (fun j => Nat.le_ceil _) u hum hu f g hfint
    (bounded_supported_coordinate_integrable g hgm hgb E hE hEfin hgs)] at hout
  exact hout

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_BandDiagonalBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The basic diagonal estimate with only the original annular support
and bin hypotheses. All packet geometry is constructed internally. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_basic_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,hK,hmain⟩ := exists_finite_diagonal_basic_l1 hVariation psi beta A B c C a M delta
    p hA hB hd hnarrow hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w htop hwidth hw hwW center hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  exact hmain N κ topLength width w (2*Real.pi*C) htop hwidth hw hwW (by positivity)
    center (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).2)
    hlo hhi u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1MultiplierLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite input and test reconstruction for frequency multipliers
with an integrable envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_finset_sum_l1 {ι : Type*} (I : Finset ι)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure) (omega : ℝ×ℝ) :
    planarFourier (fun z => ∑ i∈I, f i z) omega=∑ i∈I, planarFourier (f i) omega := by
  have hi (i : ι) (hi : i∈I) : Integrable (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f i z) planeMeasure := by
    apply (hf i hi).norm.mono'
      ((show Continuous (fun z : ℝ×ℝ => Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by
        fun_prop).aestronglyMeasurable.smul (hf i hi).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  unfold planarFourier
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum I hi

theorem variableFrequencyMultiplier_finset_sum_l1 {ι : Type*} (I : Finset ι)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 m (fun x => ∑ i∈I, f i x) z=
      ∑ i∈I, variableFrequencyMultiplierL1 m (f i) z := by
  unfold variableFrequencyMultiplierL1
  simp_rw [planarFourier_finset_sum_l1 I f hf,Finset.mul_sum,Finset.smul_sum]
  exact integral_finsetSum I (fun i hi =>
    variableFrequencyMultiplier_integrand_integrable_l1 m hm q hq hbound (f i) (hf i hi) z)

theorem variableFrequencyMultiplier_pairing_finset_sum_l1 {ι ν : Type*}
    (I : Finset ι) (J : Finset ν)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure)
    (g : ν → (ℝ×ℝ) → ℂ) (hg : ∀ j∈J, Integrable (g j) planeMeasure) :
    (∫ z, variableFrequencyMultiplierL1 m (fun x => ∑ i∈I, f i x) z*
      star (∑ j∈J, g j z) ∂planeMeasure)=
      ∑ i∈I, ∑ j∈J, ∫ z, variableFrequencyMultiplierL1 m (f i) z*star (g j z) ∂planeMeasure := by
  simp_rw [variableFrequencyMultiplier_finset_sum_l1 I m hm q hq hbound f hf,star_sum,
    Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum I]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum J (fun j hj =>
      variableFrequencyMultiplier_pairing_integrable_l1 m hm q hq hbound (f i) (hf i hi) (g j) (hg j hj))
  · intro i hi
    exact integrable_finsetSum J (fun j hj =>
      variableFrequencyMultiplier_pairing_integrable_l1 m hm q hq hbound (f i) (hf i hi) (g j) (hg j hj))

theorem planarFourier_real_smul_l1 (a : ℝ) (f : ℝ×ℝ → ℂ) (omega : ℝ×ℝ) :
    planarFourier (fun z => a • f z) omega=a • planarFourier f omega := by
  unfold planarFourier
  simp_rw [smul_comm (Real.fourierChar _) a]
  exact integral_smul a _

theorem variableFrequencyMultiplier_real_smul_l1 (a : ℝ)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 m (fun x => a • f x) z=
      a • variableFrequencyMultiplierL1 m f z := by
  unfold variableFrequencyMultiplierL1
  simp_rw [planarFourier_real_smul_l1,mul_smul_comm,smul_comm (Real.fourierChar _) a]
  exact integral_smul a _

theorem variableFrequencyMultiplier_pairing_real_smul_l1 (a b : ℝ)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (f g : ℝ×ℝ → ℂ) :
    (∫ z, variableFrequencyMultiplierL1 m (fun x => a • f x) z*
      star (b • g z) ∂planeMeasure)=
      (a*b) • ∫ z, variableFrequencyMultiplierL1 m f z*star (g z) ∂planeMeasure := by
  simp_rw [variableFrequencyMultiplier_real_smul_l1,star_smul,star_trivial,
    smul_mul_smul_comm]
  exact integral_smul (a*b) _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalAmplitudeReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the actual finite diagonal form from its
measurable amplitude slices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {κ : Type} [Fintype κ]

theorem amplitudeApprox_coordinate (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (I : Finset ℤ) (z : ℝ×ℝ) (k : κ) :
    amplitudeApprox f I z k=∑ i∈I, (2:ℝ)^i • (amplitudePiece f i z k) := by
  simp only [amplitudeApprox,Finset.sum_apply]
  change WithLp.ofLp (∑ i∈I, (2:ℝ)^i • amplitudePiece f i z) k=_
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply]

theorem amplitudePiece_coordinate_integrable
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hf2 : MemLp f 2 planeMeasure)
    (i : ℤ) (k : κ) : Integrable (fun z => amplitudePiece f i z k) planeMeasure :=
  bounded_supported_coordinate_integrable (amplitudePiece f i) (amplitudePiece_measurable hfm i)
    (amplitudePiece_bounded f i) (amplitudeLevel f i) (amplitudeLevel_measurable hfm.norm i)
    (amplitudeLevel_finite planeMeasure hf2 i) (amplitudePiece_supported f i) k

theorem finiteDiagonalBand_amplitude_reconstruction {N : ℕ}
    (psi beta : SchwartzMap ℝ ℂ) (topLength width M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hgm : Measurable g)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) (I J : Finset ℤ) :
    finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
      (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudePiece f i z k) (amplitudePiece g j) := by
  classical
  have hU : 0≤U := (abs_nonneg (u 0)).trans (hu 0)
  have hterm (s : Fin N) (k : κ) :
      (∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
        (fun x => amplitudeApprox f I x k) z*star (amplitudeApprox g J z k) ∂planeMeasure)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        ∫ z, variableFrequencyMultiplierL1
          (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
          (fun x => amplitudePiece f i x k) z*star (amplitudePiece g j z k) ∂planeMeasure := by
    obtain ⟨q,hq,hbound⟩ := exists_annularBandSymbol_envelope psi beta
      (topLength/(2:ℝ)^s.val) width (center k) M B U
      (div_pos htop (pow_pos (by norm_num) _)) hwidth hU hpsi hbeta u hu
    simp_rw [amplitudeApprox_coordinate]
    rw [variableFrequencyMultiplier_pairing_finset_sum_l1 I J _
      (annularBandSymbol_measurable psi beta _ width (center k) u hum) q hq hbound
      (fun i x => (2:ℝ)^i • amplitudePiece f i x k)
      (fun i _ => (amplitudePiece_coordinate_integrable f hfm hf2 i k).smul ((2:ℝ)^i))
      (fun j x => (2:ℝ)^j • amplitudePiece g j x k)
      (fun j _ => (amplitudePiece_coordinate_integrable g hgm hg2 j k).smul ((2:ℝ)^j))]
    simp only [variableFrequencyMultiplier_pairing_real_smul_l1]
  unfold finiteDiagonalBandL1
  simp_rw [hterm,Finset.smul_sum]
  calc
    _=∑ s : Fin N, ∑ i∈I, ∑ j∈J, ∑ k : κ,
        ((2:ℝ)^i*(2:ℝ)^j) • ∫ z, variableFrequencyMultiplierL1
          (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
          (fun x => amplitudePiece f i x k) z*star (amplitudePiece g j z k) ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAmplitudeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual diagonal form changes by a controlled amount when all
logarithmically discarded amplitude levels are removed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_amplitude_error (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable (fun z => ‖f z‖) planeMeasure → Integrable (fun z => ‖g z‖) planeMeasure →
    ∀ (F E Q C0 L : ℝ), 0<F → 0<E → 0≤Q → 0≤L →
      (∀ z, ‖f z‖≤Q) → (∀ z, ‖g z‖≤Q) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤Q*F → (∫ z, ‖g z‖ ∂planeMeasure)≤Q*E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)-
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudeApprox f
            (I.filter (fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4)) z k)
          (amplitudeApprox g (J.filter (fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4)))‖≤
        K*(amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
          (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L)*
          Real.sqrt F*Real.sqrt E := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_basic_l1 hVariation psi beta B c C a M
    hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w htop hwidth hw hwW center hlo hhi u hum hu
    f g hfm hgm hf2 hg2 hf1 hg1 F E Q C0 L hF hE hQ hL hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
  let P := fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4
  let R := fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4
  let aa := fun i => (2:ℝ)^i*Real.sqrt (planeMeasure.real (amplitudeLevel f i)/F)
  let bb := fun j => (2:ℝ)^j*Real.sqrt (planeMeasure.real (amplitudeLevel g j)/E)
  let pair := fun i j => finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
    (fun k z => amplitudePiece f i z k) (amplitudePiece g j)
  have hpair (i j : ℤ) : ‖pair i j‖≤
      K*Real.sqrt (planeMeasure.real (amplitudeLevel f i))*Real.sqrt (planeMeasure.real (amplitudeLevel g j)) :=
    hmain N κ topLength width w htop hwidth hw hwW center hlo hhi u hum hu
      (fun k z => amplitudePiece f i z k) (amplitudePiece f i) (amplitudePiece g j)
      (fun _ _ => rfl) (amplitudePiece_measurable hfm i) (amplitudePiece_measurable hgm j)
      (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
      (amplitudeLevel g j) (amplitudeLevel f i)
      (amplitudeLevel_measurable hgm.norm j) (amplitudeLevel_measurable hfm.norm i)
      (amplitudeLevel_finite planeMeasure hg2 j) (amplitudeLevel_finite planeMeasure hf2 i)
      (amplitudePiece_supported g j) (amplitudePiece_supported f i)
  have herror := finite_matrix_discard_bound I J P R aa bb
    (fun i j => ((2:ℝ)^i*(2:ℝ)^j) • pair i j) (K*Real.sqrt F*Real.sqrt E)
    (by positivity) (fun _ _ => by dsimp only [aa]; positivity) (fun _ _ => by dsimp only [bb]; positivity)
    (fun i _ j _ => weighted_pair_bound_normalized (pair i j) _ _ K _ _ F E
      (by positivity) (by positivity) measureReal_nonneg measureReal_nonneg hF hE (hpair i j))
  have hsumF := amplitudeLevel_all_weights planeMeasure f hf2 hfm.norm hf1 I F Q C0 L
    hF hQ hL hfb hF1 hF2 hFi
  have hsumG := amplitudeLevel_all_weights planeMeasure g hg2 hgm.norm hg1 J E Q C0 L
    hE hQ hL hgb hG1 hG2 hGj
  have htailF := amplitudeLevel_discarded_sum planeMeasure f hf2 hfm.norm hf1
    (I.filter (fun i => ¬P i)) F Q L hF hQ hfb hF1
    (fun i hi => hFi i (Finset.mem_filter.mp hi).1)
    (fun _ hi => lt_of_not_ge (Finset.mem_filter.mp hi).2)
  have htailG := amplitudeLevel_discarded_sum planeMeasure g hg2 hgm.norm hg1
    (J.filter (fun j => ¬R j)) E Q L hE hQ hgb hG1
    (fun j hj => hGj j (Finset.mem_filter.mp hj).1)
    (fun _ hj => lt_of_not_ge (Finset.mem_filter.mp hj).2)
  rw [finiteDiagonalBand_amplitude_reconstruction psi beta topLength width M (B/2) 1
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center u hum hu f g hfm hgm hf2 hg2 I J,
    finiteDiagonalBand_amplitude_reconstruction psi beta topLength width M (B/2) 1
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center u hum hu f g hfm hgm hf2 hg2 (I.filter P) (J.filter R)]
  apply herror.trans
  have hsa : 0≤∑ i∈I, aa i := by dsimp only [aa]; positivity
  have hsb : 0≤∑ j∈J, bb j := by dsimp only [bb]; positivity
  have hta : 0≤∑ i∈I.filter (fun i => ¬P i), aa i := by dsimp only [aa]; positivity
  have htb : 0≤∑ j∈J.filter (fun j => ¬R j), bb j := by dsimp only [bb]; positivity
  have hcost := amplitudeTailCost_nonneg Q L hQ
  calc
    _≤(K*Real.sqrt F*Real.sqrt E)*
        (amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
          (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul htailF hsumG hsb hcost)
        (mul_le_mul hsumF htailG htb (add_nonneg (retainedAmplitudeCost_nonneg _ _) hcost))
    _=_ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_BandDiagonalHighL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate with all auxiliary geometry removed.
A fixed multiple of the band width specifies the retained low endpoint. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ → 0<planeMeasure.real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      planeMeasure.real E=ratio^2*planeMeasure.real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z)) f g‖≤
        K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,L0,hK,hL0,hmain⟩ := exists_finite_diagonal_high_l1 hVariation hLL psi beta
    A B c C a M delta (2*Real.pi*C) (2*Real.pi*c) p hA hB hd hnarrow
    (by positivity) (by positivity) hpsi hbeta
  let D := 4*(p.H+M/c+delta)
  have hD : 0<D := by dsimp only [D]; positivity [p.H_pos]
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center
    hlo hhi field hfield hfieldBound f fData g hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs l r ratio widthScale
    hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
  have hlength' (j : Fin N) : (p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))≤3/4 := by
    have hlen : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have hdiv := (div_le_one hlen).mpr (hlength j)
    have heq : D*w/(topLength/(2:ℝ)^j.val)=
        4*((p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))) := by dsimp only [D]; ring
    rw [heq] at hdiv
    linarith
  exact hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength' center
    (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).1)
    (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).2)
    hlo hhi field hfield hfieldBound f fData g hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs l r ratio widthScale
    hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAmplitudeHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_retained_amplitude_pair (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
    ∀ (i j : ℤ), 0<planeMeasure.real (amplitudeLevel f i) →
      0<planeMeasure.real (amplitudeLevel g j) →
      |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4 →
      |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4 →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudePiece f i z k) (amplitudePiece g j)‖≤
        K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real (amplitudeLevel f i))*
          Real.sqrt (planeMeasure.real (amplitudeLevel g j)) := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_high_l1 hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog i j
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  obtain ⟨hr',heq'⟩ := sqrt_mass_ratio _ _ hFi hGj
  obtain ⟨hlo',hhi'⟩ := retained_amplitude_disparity F E _ _ ratio L
    hF hE hFi hGj hr heq hlog hlogf hlogg
  apply hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength
    center hlo hhi field hfield hfieldBound
    (fun k z => amplitudePiece f i z k) (amplitudePiece f i) (amplitudePiece g j)
    (fun _ _ => rfl) (amplitudePiece_measurable hfm i) (amplitudePiece_measurable hgm j)
    (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
    (amplitudeLevel g j) (amplitudeLevel f i)
    (amplitudeLevel_measurable hgm.norm j) (amplitudeLevel_measurable hfm.norm i)
    (amplitudeLevel_finite planeMeasure hg2 j) (amplitudeLevel_finite planeMeasure hf2 i)
    hFi (amplitudePiece_supported g j) (amplitudePiece_supported f i)
    l r (Real.sqrt (planeMeasure.real (amplitudeLevel g j)/planeMeasure.real (amplitudeLevel f i)))
    widthScale hstrip _ _ hr' hlo' hhi' heq' hwlo hwhi hweq
  · intro z hz
    exact hgstrip z (norm_pos_iff.mp ((zpow_pos (by norm_num) _).trans hz.1))
  · intro z hz
    exact hfstrip z (norm_pos_iff.mp ((zpow_pos (by norm_num) _).trans hz.1))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAmplitudeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_retained_amplitude_sum (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
    ∀ (F E ratio C0 : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      (∀ i∈I, |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4) →
      (∀ j∈J, |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center
          (fun z => field (planeCoordinates z))
          (fun k z => amplitudePiece f i z k) (amplitudePiece g j)‖≤
        K*L^(-20:ℝ)*(retainedAmplitudeCost C0 L)^2*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_retained_amplitude_pair hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio C0 hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hL0' : 0≤L := (by linarith : 0≤L0).trans hL
  have hout := retained_amplitude_matrix_bound planeMeasure f g hfm hgm hf2 hg2 I J
    F E C0 C0 (K*L^(-20:ℝ)) L hF hE (by positivity) hL0' hEf hEg hFi hGj
    (fun i hi => (hlogf i hi).trans (by linarith))
    (fun j hj => (hlogg j hj).trans (by linarith))
    (fun i j => finiteDiagonalBandL1 (N:=N) psi beta topLength width center
      (fun z => field (planeCoordinates z))
      (fun k z => amplitudePiece f i z k) (amplitudePiece g j))
    (fun i hi j hj => hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength
      center hlo hhi field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog
      i j (hFi i hi) (hGj j hj) (hlogf i hi) (hlogg j hj)
      l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq)
  convert hout using 1 <;> first | rfl | ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandRetainedApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_retained_approximation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
    ∀ (F E ratio C0 : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      (∀ i∈I, |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4) →
      (∀ j∈J, |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)‖≤
        K*L^(-20:ℝ)*(retainedAmplitudeCost C0 L)^2*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_retained_amplitude_sum hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio C0 hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  rw [finiteDiagonalBand_amplitude_reconstruction psi beta topLength width M (B/2) (1/4)
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center
    (fun z => field (planeCoordinates z)) (product_slope_lipschitz field hfield).continuous.measurable
    (fun z => hfieldBound _) f g hfm hgm hf2 hg2 I J]
  exact hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio C0 hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandRetainedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_retained_decay (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) (C0 : ℝ) (hC0 : 0<C0) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      (∀ i∈I, |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4) →
      (∀ j∈J, |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)‖≤
        K*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_retained_approximation hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  let K' := 128*K*C0*(2/Real.log 2+5)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D,K',L0,hD,by dsimp only [K']; positivity,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hout := hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio C0 hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (retainedAmplitudeCost_decay K C0 L hK.le hC0.le (by linarith))
      (Real.sqrt_nonneg F)) (Real.sqrt_nonneg E))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandFiniteAmplitudeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_finite_amplitude_bound (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) (C0 Qbase Qrate : ℝ) (hC0 : 0<C0) (hQbase : 0<Qbase) (hQrate : 0≤Qrate) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable (fun z => ‖f z‖) planeMeasure → Integrable (fun z => ‖g z‖) planeMeasure →
    ∀ (F E ratio Q : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      0≤Q → Q≤Qbase*Real.exp (Qrate*L^(9/10:ℝ)) →
      (∀ z, ‖f z‖≤Q) → (∀ z, ‖g z‖≤Q) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤Q*F → (∫ z, ‖g z‖ ∂planeMeasure)≤Q*E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)‖≤
        K*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  classical
  obtain ⟨D,Kr,Lr,hD,hKr,hLr,hret⟩ := band_diagonal_retained_decay hVariation hLL psi beta
    B c C a M hB hc hC ha hM hpsi hbeta C0 hC0
  obtain ⟨Ke,hKe,herror⟩ := band_diagonal_amplitude_error hVariation psi beta
    B c C a M hB hc hC ha hM hpsi hbeta
  obtain ⟨Lt,hLt⟩ := Filter.eventually_atTop.mp (eventually_amplitude_error_decay Qbase Qrate C0 hQbase hQrate)
  refine ⟨D,Kr+Ke,max Lr Lt,hD,by positivity,le_trans hLr (le_max_left _ _),?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hLr' : Lr≤L := (le_max_left _ _).trans hL
  have hLt' : Lt≤L := (le_max_right _ _).trans hL
  have hL0 : 0≤L := by linarith
  let Ip := I.filter (fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4)
  let Jp := J.filter (fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4)
  have hretained := hret L hLr' N κ topLength width w htop hwidth hw hwW htime hlength
    center hlo hhi field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog hF2 hG2
    Ip Jp (fun i hi => hFi i (Finset.mem_filter.mp hi).1)
    (fun j hj => hGj j (Finset.mem_filter.mp hj).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun _ hj => (Finset.mem_filter.mp hj).2)
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have herr := herror N κ topLength width w htop hwidth hw hwW center hlo hhi
    (fun z => field (planeCoordinates z)) (product_slope_lipschitz field hfield).continuous.measurable
    (fun z => (hfieldBound _).trans (by norm_num)) f g hfm hgm hf2 hg2 hf1 hg1
    F E Q C0 L hF hE hQ hL0 hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
  have hsmall := hLt L hLt' Q hQ hQbound
  have herr' := herr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hKe.le)
      (Real.sqrt_nonneg F)) (Real.sqrt_nonneg E))
  have htriangle := norm_sub_norm_le
    (finiteDiagonalBandL1 (N:=N) psi beta topLength width center (fun z => field (planeCoordinates z))
      (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J))
    (finiteDiagonalBandL1 (N:=N) psi beta topLength width center (fun z => field (planeCoordinates z))
      (fun k z => amplitudeApprox f Ip z k) (amplitudeApprox g Jp))
  calc
    _≤Ke*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+Kr*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
      dsimp only [Ip,Jp] at hretained htriangle
      linarith
    _=_ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalAmplitudeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite diagonal forms converge under the actual amplitude
exhaustion. This removes all amplitude cutoffs without an L2 continuity
assumption on the operator being estimated. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

variable {κ : Type} [Fintype κ]

theorem vector_coordinate_integrable (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f planeMeasure) (k : κ) :
    Integrable (fun z => f z k) planeMeasure := by
  apply hf1.norm.mono'
    (((measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hfm)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun z => PiLp.norm_apply_le (f z) k)

theorem finiteDiagonalBand_amplitude_limit {N : ℕ}
    (psi beta : SchwartzMap ℝ ℂ) (topLength width M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hgm : Measurable g)
    (hf1 : Integrable f planeMeasure) (hg1 : Integrable g planeMeasure)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) :
    Tendsto (fun n : ℕ => finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
      (fun k z => amplitudeApprox f
        ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<planeMeasure.real (amplitudeLevel f i))) z k)
      (amplitudeApprox g ((Finset.Icc (-(n:ℤ)) n).filter (fun j => 0<planeMeasure.real (amplitudeLevel g j)))))
      atTop (𝓝 (finiteDiagonalBandL1 (N:=N) psi beta topLength width center u (fun k z => f z k) g)) := by
  classical
  have hU : 0≤U := (abs_nonneg (u 0)).trans (hu 0)
  unfold finiteDiagonalBandL1
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro k _
  obtain ⟨q,hq,hbound⟩ := exists_annularBandSymbol_envelope psi beta
    (topLength/(2:ℝ)^s.val) width (center k) M B U
    (div_pos htop (pow_pos (by norm_num) _)) hwidth hU hpsi hbeta u hu
  apply variableFrequencyMultiplier_pairing_tendsto_dominated _
    (annularBandSymbol_measurable psi beta _ width (center k) u hum) q hq hbound
  · exact vector_coordinate_integrable f hfm hf1 k
  · exact vector_coordinate_integrable g hgm hg1 k
  · intro n
    exact vector_coordinate_integrable _ (amplitudeApprox_measurable hfm _)
      (amplitudeApprox_integrable planeMeasure f hfm hf1 _) k
  · intro n
    exact vector_coordinate_integrable _ (amplitudeApprox_measurable hgm _)
      (amplitudeApprox_integrable planeMeasure g hgm hg1 _) k
  · intro n
    exact Filter.Eventually.of_forall (fun z => amplitudeApprox_coordinate_norm_le f _ z k)
  · intro n
    exact Filter.Eventually.of_forall (fun z => amplitudeApprox_coordinate_norm_le g _ z k)
  · filter_upwards [amplitudeApprox_positive_tendsto_ae planeMeasure f hf2] with z hz
    exact (PiLp.continuous_apply 2 (fun _ : κ => ℂ) k).continuousAt.tendsto.comp hz
  · filter_upwards [amplitudeApprox_positive_tendsto_ae planeMeasure g hg2] with z hz
    exact (PiLp.continuous_apply 2 (fun _ : κ => ℂ) k).continuousAt.tendsto.comp hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandMeasurableHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_measurable_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) (C0 Qbase Qrate : ℝ) (hC0 : 0<C0) (hQbase : 0<Qbase) (hQrate : 0≤Qrate) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable (fun z => ‖f z‖) planeMeasure → Integrable (fun z => ‖g z‖) planeMeasure →
    ∀ (F E ratio Q : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      0≤Q → Q≤Qbase*Real.exp (Qrate*L^(9/10:ℝ)) →
      (∀ z, ‖f z‖≤Q) → (∀ z, ‖g z‖≤Q) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤Q*F → (∫ z, ‖g z‖ ∂planeMeasure)≤Q*E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => f z k) g‖≤
        K*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ := band_diagonal_finite_amplitude_bound hVariation hLL
    psi beta B c C a M hB hc hC ha hM hpsi hbeta C0 Qbase Qrate hC0 hQbase hQrate
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hf1' : Integrable f planeMeasure := hf1.mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_refl _))
  have hg1' : Integrable g planeMeasure := hg1.mono' hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_refl _))
  have hlim := finiteDiagonalBand_amplitude_limit (N:=N) psi beta topLength width M (B/2) (1/4)
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center
    (fun z => field (planeCoordinates z)) (product_slope_lipschitz field hfield).continuous.measurable
    (fun z => hfieldBound _) f g hfm hgm hf1' hg1' hf2 hg2
  apply le_of_tendsto hlim.norm
  apply Filter.Eventually.of_forall
  intro n
  exact hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2
    ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<planeMeasure.real (amplitudeLevel f i)))
    ((Finset.Icc (-(n:ℤ)) n).filter (fun j => 0<planeMeasure.real (amplitudeLevel g j)))
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun _ hj => (Finset.mem_filter.mp hj).2)
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed real smooth bin profile whose squared translates sum to one.
The trigonometric construction avoids a variable normalization denominator. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinProfileReal_sq (x : ℝ) :
    (verticalBinProfileReal x)^2=binSquareStep (x+1)-binSquareStep x := by
  by_cases hx : x≤0
  · simp [verticalBinProfileReal,binSquareStep,Real.smoothTransition.zero_of_nonpos hx]
  · have hx1 : 1≤x+1 := by linarith
    have hs := Real.sin_sq_add_cos_sq (Real.pi/2*Real.smoothTransition x)
    simp only [verticalBinProfileReal,binSquareStep,Real.smoothTransition.one_of_one_le hx1,
      mul_one,Real.sin_pi_div_two,one_mul,one_pow]
    linarith

theorem verticalBinProfile_apply (x : ℝ) : verticalBinProfile x=(verticalBinProfileReal x : ℂ) := rfl

theorem verticalBinProfileReal_sum_sq (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, (verticalBinProfileReal (x-(n:ℝ)))^2)=
      binSquareStep (x+1)-binSquareStep (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,verticalBinProfileReal_sq]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteVerticalBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite real square partition of a positive vertical band.
Only bins meeting the original band are retained. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinWindow_apply (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) (eta : ℝ) :
    verticalBinWindow K W n eta=verticalBinProfile (W*eta+K-n) := by
  unfold verticalBinWindow verticalBinCenter
  congr 1
  field_simp
  ring

theorem verticalBinLabels_center_bounds (K : ℕ) (w W c C : ℝ)
    (n : verticalBinLabels K w W c C) :
    c-w/W≤w*verticalBinCenter K W n ∧ w*verticalBinCenter K W n≤C+w/W :=
  (Finset.mem_filter.mp n.property).2

theorem verticalBinLabels_admissible_centers (K : ℕ) (w W c C : ℝ)
    (hsmall : 5*(w/W) ≤ c/2) (hcC : c/2≤C)
    (n : verticalBinLabels K w W c C) :
    c/2+4*(w/W)≤w*verticalBinCenter K W n ∧
      w*verticalBinCenter K W n+4*(w/W)≤2*C := by
  obtain ⟨hlo,hhi⟩ := verticalBinLabels_center_bounds K w W c C n
  constructor <;> linarith

theorem verticalBinLabels_card (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hC : 0≤C) :
    ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(C*W/w)+3 := by
  have hcard : (verticalBinLabels ⌈C*W/w⌉₊ w W c C).card≤2*⌈C*W/w⌉₊+1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hcard' : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(⌈C*W/w⌉₊:ℝ)+1 := by
    exact_mod_cast hcard
  have hceil := (Nat.ceil_lt_add_one (show 0≤C*W/w by positivity)).le
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed enlarged vertical cutoff equals one on every bin profile.
The finite bin partition is exact throughout the prescribed annulus. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinPlateau_support (x : ℝ) (hx : verticalBinPlateau x≠0) : |x|≤2 := by
  by_contra h
  have ha : 2 < |x| := lt_of_not_ge h
  have hxx : x≤-2 ∨ 2≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at ha
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at ha
      exact Or.inr ha.le
  exact hx (by change (verticalBinPlateauReal x:ℂ)=0; rw [verticalBinPlateauReal_zero x hxx]; rfl)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem modulatedTimeKernel_fourier (K : ℝ → ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (modulatedTimeKernel K W center) eta=𝓕 K (W*(eta-center)) := by
  rw [←scaledTimeKernel_fourier K W hW (eta-center)]
  rw [Real.fourier_eq,Real.fourier_eq]
  simp only [Real.inner_apply,modulatedTimeKernel]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_smul,←Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

theorem modulatedTimeKernel_norm (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    ‖modulatedTimeKernel K W center t‖=W⁻¹*‖K (t/W)‖ := by
  rw [modulatedTimeKernel,Circle.norm_smul,scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hW.le]

theorem modulatedTimeKernel_l1 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, ‖modulatedTimeKernel K W center t‖)=∫ t, ‖K t‖ := by
  simp_rw [modulatedTimeKernel_norm K W center _ hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖K t‖) W,
    abs_of_pos hW,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem verticalProfileKernel_fourier (q : SchwartzMap ℝ ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (verticalProfileKernel q W center) eta=q (W*(eta-center)) := by
  rw [verticalProfileKernel,modulatedTimeKernel_fourier _ W center eta hW]
  have h : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q := fourier_fourierInv_eq q
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (W*(eta-center))) h

theorem verticalConvolution_uniform_bound (K : ℝ → ℂ) (hK : Integrable K)
    (f : ℝ×ℝ → ℂ) (C : ℝ) (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖verticalConvolution K f z‖≤C*∫ t, ‖K t‖ := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (z.1,z.2-t)‖≤C*‖K t‖ from by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [verticalConvolution,integral_const_mul] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution acts on actual measurable planar functions.
Its L1 and uniform bounds are independent of bin width and carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1))
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1)) := by
    exact (hKm.comp measurable_fst).mul (hfm.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable hf).const_mul (K t)
  · have heq (t : ℝ) : (∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖ ∂planeMeasure) := by
      simp_rw [norm_mul]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalConvolution K f) planeMeasure :=
  (verticalConvolution_joint_integrable K hK hKm f hfm hf).integral_prod_right

theorem verticalConvolution_l1_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    (∫ z, ‖verticalConvolution K f z‖ ∂planeMeasure)≤
      (∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi := verticalConvolution_joint_integrable K hK hKm f hfm hf
  calc
    _ ≤ ∫ z, ∫ t, ‖K t*f (z.1,z.2-t)‖ ∂volume ∂planeMeasure := by
      apply integral_mono (verticalConvolution_integrable K hK hKm f hfm hf).norm
        hi.norm.integral_prod_right
      exact fun z => norm_integral_le_integral_norm _
    _ = ∫ t, ∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure ∂volume :=
      integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [norm_mul,integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖)]
      rw [integral_mul_const]

theorem verticalConvolution_horizontal_support (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ)
    (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalConvolution K f z=0 := by
  intro z hz
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun t => by
    change K t*f (z.1,z.2-t)=0
    rw [hf (z.1,z.2-t) hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalInverseMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse-frequency representation of vertical convolution. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem vertical_inverse_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (x : ℝ×ℝ) :
    verticalConvolution k (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    x.1*omega.1+(x.2-t)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1,x.2-t) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.2))) := by
      dsimp [phase]
      ring
    rw [hp, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  calc
    _ = ∫ t, ∫ omega, H (t,omega) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ omega, (∫ t, H (t,omega) ∂volume) ∂planeMeasure := integral_integral_swap hH
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)


theorem schwartz_vertical_multiplier (K : ℝ → ℂ) (hK : Integrable K)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K f z=
      planarInverse (fun omega => 𝓕 K omega.2*planarFourier f omega) z := by
  have h := vertical_inverse_multiplier K (planarFourier f) hK (planarFourier_integrable f) z
  simpa only [funext (planarFourier_inversion f),planarInverse] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzVerticalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_eq_convolution (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    schwartzVerticalProjection q W center f z=
      verticalConvolution (verticalProfileKernel q W center) f z := by
  rw [schwartz_vertical_multiplier (verticalProfileKernel q W center)
    (modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW)]
  simp_rw [verticalProfileKernel_fourier q W center _ hW]
  rw [schwartzVerticalProjection,planarInverseSchwartz_apply]
  congr 1
  funext omega
  rw [SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality-independent square-function energy for the finite vertical bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem binSquareStep_nonneg (x : ℝ) : 0≤binSquareStep x := sq_nonneg _

theorem binSquareStep_le_one (x : ℝ) : binSquareStep x≤1 := by
  exact Real.sin_sq_le_one _

theorem verticalBinProfile_sum_norm_sq_le (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, ‖verticalBinProfile (x-(n:ℝ))‖^2)≤1 := by
  have hn (y : ℝ) : ‖verticalBinProfile y‖^2=verticalBinProfileReal y^2 := by
    simp only [verticalBinProfile_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp_rw [hn]
  rw [verticalBinProfileReal_sum_sq]
  exact (sub_le_self _ (binSquareStep_nonneg _)).trans (binSquareStep_le_one _)

theorem verticalBinWindow_sum_norm_sq_le (K : ℕ) (W : ℝ) (hW : 0<W)
    (eta : ℝ) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ‖verticalBinWindow K W n eta‖^2)≤1 := by
  calc
    _ ≤ ∑ n∈Finset.range (2*K+1), ‖verticalBinWindow K W n eta‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => sq_nonneg _)
    _ ≤ 1 := by
      simp_rw [verticalBinWindow_apply K W hW]
      exact verticalBinProfile_sum_norm_sq_le (W*eta+K) (2*K+1)

theorem planar_integral_norm_sq_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure)=∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_inner_fourier f f
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change (∫ omega, ((‖planarFourier f omega‖^2 : ℝ) : ℂ) ∂planeMeasure)=
    (∫ z, ((‖f z‖^2 : ℝ) : ℂ) ∂planeMeasure) at h
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem verticalBin_schwartz_energy_le (f : SchwartzMap (ℝ×ℝ) ℂ)
    (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ∫ z, ‖schwartzVerticalProjection verticalBinProfile W
      (verticalBinCenter K W n) f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  have hp (n : ℕ) := planar_integral_norm_sq_fourier
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f)
  have hpi (n : ℕ) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ n∈I, ∫ omega, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure := by
      exact Finset.sum_congr rfl (fun n _ => (hp n).symm)
    _ = ∫ omega, ∑ n∈I, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure :=
      (integral_finsetSum I (fun n _ => hpi n)).symm
    _ ≤ ∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure := by
      apply integral_mono (integrable_finsetSum I (fun n _ => hpi n))
      · simpa only [planarFourierSchwartz_apply] using
          ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
      · intro omega
        simp only [schwartzVerticalProjection_fourier,norm_mul,mul_pow]
        rw [←Finset.sum_mul]
        exact mul_le_of_le_one_left (sq_nonneg _) (verticalBinWindow_sum_norm_sq_le
          K W hW omega.2 I hI)
    _ = _ := planar_integral_norm_sq_fourier f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution on the L2 quotient, with its actual integral representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_congr_ae (K : ℝ → ℂ) (f g : ℝ×ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (hfg : f=ᵐ[planeMeasure] g) :
    verticalConvolution K f=ᵐ[planeMeasure] verticalConvolution K g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂planeMeasure,
      f (z.1,z.2-t)=g (z.1,z.2-t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (verticalTranslation_measurePreserving t).quasiMeasurePreserving.ae hfg
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | f (p.2.1,p.2.2-p.1)=g (p.2.1,p.2.2-p.1)} :=
    measurableSet_eq_fun (hf.comp (by fun_prop)) (hg.comp (by fun_prop))
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem verticalConvolution_integrand_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*f (z.1,z.2-t)) := by
  filter_upwards [(verticalConvolution_energy_joint_integrable K hK hKm f hfm hf).prod_left_ae]
    with z hz
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (z.1,z.2-t)‖) hKm.norm (hfm.norm.comp (by fun_prop))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem verticalConvolution_sub_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f g : ℝ×ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    verticalConvolution K (f-g)=ᵐ[planeMeasure]
      (verticalConvolution K f-verticalConvolution K g) := by
  filter_upwards [verticalConvolution_integrand_ae K hK hKm f hfm hf,
    verticalConvolution_integrand_ae K hK hKm g hgm hg] with z hfz hgz
  change (∫ t, K t*(f (z.1,z.2-t)-g (z.1,z.2-t)))=_
  simp_rw [mul_sub]
  exact integral_sub hfz hgz

theorem verticalConvolutionLp_coe (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    (verticalConvolutionLp K hK hKm f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] verticalConvolution K f :=
  MemLp.coeFn_toLp _

theorem verticalConvolutionLp_toLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (hf.toLp f)=
      (verticalConvolution_energy_bound K hK hKm f hfm hf).1.toLp (verticalConvolution K f) := by
  apply Lp.ext
  exact (verticalConvolutionLp_coe K hK hKm _).trans
    ((verticalConvolution_congr_ae K _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable hfm hf.coeFn_toLp).trans
      (MemLp.coeFn_toLp _).symm)

theorem verticalConvolutionLp_sub (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f g : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (f-g)=
      verticalConvolutionLp K hK hKm f-verticalConvolutionLp K hK hKm g := by
  apply Lp.ext
  have hc := verticalConvolution_congr_ae K (show Lp ℂ 2 planeMeasure from f-g) ((f : (ℝ×ℝ)→ℂ)-(g : (ℝ×ℝ)→ℂ))
    (Lp.stronglyMeasurable (f-g)).measurable ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  have hs := verticalConvolution_sub_ae K hK hKm f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [verticalConvolutionLp_coe K hK hKm (f-g),hc,hs,
    verticalConvolutionLp_coe K hK hKm f,verticalConvolutionLp_coe K hK hKm g,
    Lp.coeFn_sub (verticalConvolutionLp K hK hKm f) (verticalConvolutionLp K hK hKm g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem verticalConvolutionLp_norm (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    ‖verticalConvolutionLp K hK hKm f‖≤(∫ t, ‖K t‖)*‖f‖ := by
  have h := (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖verticalConvolutionLp K hK hKm f‖^2≤(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤∫ t, ‖K t‖ := integral_nonneg (fun t => norm_nonneg (K t))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  simpa only [mul_pow] using h

theorem verticalConvolutionLp_continuous (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K) :
    Continuous (verticalConvolutionLp K hK hKm) := by
  apply LipschitzWith.continuous (K:=⟨∫ t, ‖K t‖,integral_nonneg fun _ => norm_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←verticalConvolutionLp_sub]
  exact verticalConvolutionLp_norm K hK hKm (f-g)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bin square-function bound on the actual L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinLp_continuous (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) :
    Continuous (verticalBinLp K W hW n) :=
  verticalConvolutionLp_continuous _
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable

theorem verticalBinLp_schwartz (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalBinLp K W hW n (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).toLp 2
        planeMeasure := by
  apply Lp.ext
  have hi := verticalConvolutionLp_toLp
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalBinLp K W hW n (f.toLp 2 planeMeasure)=_ at hi
  rw [hi]
  have hmem := (verticalConvolution_energy_bound
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [MemLp.coeFn_toLp hmem,
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).coeFn_toLp
      2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W _ hW]

theorem verticalBinLp_energy (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ)
    (hI : I⊆Finset.range (2*K+1)) (f : Lp ℂ 2 planeMeasure) :
    (∑ n∈I, ‖verticalBinLp K W hW n f‖^2)≤‖f‖^2 := by
  let P := fun f : Lp ℂ 2 planeMeasure => (∑ n∈I, ‖verticalBinLp K W hW n f‖^2)≤‖f‖^2
  apply DenseRange.induction_on (p:=P)
    (SchwartzMap.denseRange_toLpCLM (E:=ℝ×ℝ) (F:=ℂ) (μ:=planeMeasure)
      (by norm_num : (2:ℝ≥0∞)≠⊤)) f
  · apply isClosed_le
    · exact continuous_finsetSum _ (fun n _ => ((verticalBinLp_continuous K W hW n).norm).pow 2)
    · exact continuous_norm.pow 2
  · intro g
    dsimp only [P]
    simp only [SchwartzMap.toLpCLM_apply,verticalBinLp_schwartz]
    simp_rw [planar_toL2_norm_sq]
    exact verticalBin_schwartz_energy_le g K W hW I hI

theorem verticalBin_measurable_energy (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ)
    (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ∫ z, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2 ∂planeMeasure)≤
      ∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := verticalBinLp_energy K W hW I hI (hf.toLp f)
  rw [memLp_toL2_norm_sq] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro n hn
  rw [verticalBinLp,verticalConvolutionLp_toLp _ _ _ f hfm hf,memLp_toL2_norm_sq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinVector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite vectors of vertical projections, including their energy,
L1, uniform, and horizontal support bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem euclidean_norm_le_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖≤∑ i, ‖v i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem verticalBinVector_norm_le_sum (I : Finset ℕ) (K : ℕ) (W : ℝ) (f : ℝ×ℝ → ℂ)
    (z : ℝ×ℝ) :
    ‖verticalBinVector I K W f z‖≤∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ := by
  have h := euclidean_norm_le_sum (verticalBinVector I K W f z)
  change ‖verticalBinVector I K W f z‖≤∑ n : I, ‖verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ at h
  rw [Finset.sum_coe_sort I (fun n : ℕ => ‖verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖)] at h
  exact h

theorem verticalBinVector_measurable (I : Finset ℕ) (K : ℕ) (W : ℝ)
    (f : ℝ×ℝ → ℂ) (hf : Measurable f) : Measurable (verticalBinVector I K W f) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro n
  exact verticalConvolution_measurable _ (verticalProfileKernel_continuous _ _ _).measurable f hf

theorem verticalBinVector_energy (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (hI : I⊆Finset.range (2*K+1)) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (verticalBinVector I K W f) 2 planeMeasure ∧
      (∫ z, ‖verticalBinVector I K W f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  have hi (n : ℕ) : Integrable (fun z => ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2) planeMeasure :=
    (verticalConvolution_energy_bound _ (verticalProfileKernel_integrable _ _ _ hW)
      (verticalProfileKernel_continuous _ _ _).measurable f hfm hf).1.integrable_norm_pow (by decide : 2≠0)
  have heq (z : ℝ×ℝ) : ‖verticalBinVector I K W f z‖^2=∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ n : I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2)=_
    exact Finset.sum_coe_sort I (fun n : ℕ => ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2)
  have hint : Integrable (fun z => ‖verticalBinVector I K W f z‖^2) planeMeasure := by
    simp_rw [heq]
    exact integrable_finsetSum I (fun n _ => hi n)
  refine ⟨(memLp_two_iff_integrable_sq_norm (verticalBinVector_measurable I K W f hfm).aestronglyMeasurable).2 hint,?_⟩
  simp_rw [heq]
  rw [integral_finsetSum I (fun n _ => hi n)]
  exact verticalBin_measurable_energy f hfm hf K W hW I hI

theorem verticalBinVector_l1 (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalBinVector I K W f) planeMeasure ∧
      (∫ z, ‖verticalBinVector I K W f z‖ ∂planeMeasure)≤
        I.card*verticalBinKernelCost*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi (n : ℕ) := verticalConvolution_integrable
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable _ _ _ hW)
    (verticalProfileKernel_continuous _ _ _).measurable f hfm hf
  have hs : Integrable (fun z => ∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖) planeMeasure :=
    integrable_finsetSum I (fun n _ => (hi n).norm)
  have hv : Integrable (verticalBinVector I K W f) planeMeasure :=
    hs.mono' (verticalBinVector_measurable I K W f hfm).aestronglyMeasurable
      (Filter.Eventually.of_forall (verticalBinVector_norm_le_sum I K W f))
  refine ⟨hv,?_⟩
  calc
    _ ≤ ∫ z, ∑ n∈I, ‖verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ ∂planeMeasure :=
      integral_mono hv.norm hs (verticalBinVector_norm_le_sum I K W f)
    _ = ∑ n∈I, ∫ z, ‖verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ ∂planeMeasure :=
      integral_finsetSum I (fun n _ => (hi n).norm)
    _ ≤ ∑ _n∈I, verticalBinKernelCost*(∫ z, ‖f z‖ ∂planeMeasure) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [verticalBinKernelCost,verticalProfileKernel,
        modulatedTimeKernel_l1 _ W _ hW] using
        verticalConvolution_l1_bound _ (verticalProfileKernel_integrable _ _ _ hW)
          (verticalProfileKernel_continuous _ _ _).measurable f hfm hf
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem verticalBinVector_uniform (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (f : ℝ×ℝ → ℂ) (M : ℝ) (hf : ∀ z, ‖f z‖≤M) (z : ℝ×ℝ) :
    ‖verticalBinVector I K W f z‖≤I.card*verticalBinKernelCost*M := by
  apply (verticalBinVector_norm_le_sum I K W f z).trans
  calc
    _ ≤ ∑ _n∈I, M*verticalBinKernelCost := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [verticalBinKernelCost,verticalProfileKernel,
        modulatedTimeKernel_l1 _ W _ hW] using
        verticalConvolution_uniform_bound _ (verticalProfileKernel_integrable _ _ _ hW) f M hf z
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem verticalBinVector_horizontal_support (I : Finset ℕ) (K : ℕ) (W : ℝ)
    (f : ℝ×ℝ → ℂ) (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalBinVector I K W f z=0 := by
  intro z hz
  apply (WithLp.ext_iff 2).mpr
  funext n
  exact verticalConvolution_horizontal_support _ f S hf z hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The number of retained vertical bins has the allowed exponential growth. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinKernelCost_nonneg : 0≤verticalBinKernelCost :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem verticalBinVectorCost_nonneg (w W c C : ℝ) : 0≤verticalBinVectorCost w W c C :=
  mul_nonneg (Nat.cast_nonneg _) verticalBinKernelCost_nonneg

theorem verticalBinVectorCost_growth (w W c C L m : ℝ) (hw : 0<w) (hW : 0<W)
    (hC : 0<C) (hL : 0≤L) (hWm : W=m*w) (hm : m≤2*Real.exp (L^(9/10:ℝ))) :
    verticalBinVectorCost w W c C≤
      ((4*C+3)*(verticalBinKernelCost+1))*Real.exp (L^(9/10:ℝ)) := by
  have hcard := verticalBinLabels_card w W c C hw hW hC.le
  have hquot : C*W/w=C*m := by rw [hWm]; field_simp
  have hcardBound : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(C*m)+3 := by
    calc
      _ ≤ 2*(C*W/w)+3 := hcard
      _ = _ := by rw [hquot]
  have he : 1≤Real.exp (L^(9/10:ℝ)) := Real.one_le_exp (Real.rpow_nonneg hL _)
  have hcard' : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤
      (4*C+3)*Real.exp (L^(9/10:ℝ)) := by nlinarith
  have hcost := mul_le_mul_of_nonneg_right hcard' verticalBinKernelCost_nonneg
  dsimp only [verticalBinVectorCost]
  have hdiff : 0≤(4*C+3)*Real.exp (L^(9/10:ℝ)) := by positivity
  nlinarith only [hcost,hdiff]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandProjectedHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved high-diagonal estimate for the actual vertically projected
input vectors. All projection size and energy hypotheses are discharged. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_projected_high_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W) ≤ c/2 → c/2≤C →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → ℂ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable f planeMeasure → Integrable g planeMeasure →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
      ‖finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
        (fun n : I => verticalBinCenter ⌈C*W/w⌉₊ W n)
        (fun z => field (planeCoordinates z))
        (fun n z => verticalConvolution
          (verticalProfileKernel verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)) f z)
        (verticalBinVector I ⌈C*W/w⌉₊ W g)‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  let Qbase := (4*C+3)*(verticalBinKernelCost+1)
  have hQbase : 0<Qbase := mul_pos (by linarith) (by linarith [verticalBinKernelCost_nonneg])
  obtain ⟨D,A,L0,hD,hA,hL0,hmain⟩ := band_diagonal_measurable_high hVariation hLL
    psi verticalBinPlateau 4 (c/2) (2*C) a M (by norm_num) (by positivity) (by positivity) ha hM
    hpsi (fun y hy => by simpa only [show (4:ℝ)/2=2 by norm_num] using verticalBinPlateau_support y hy)
    1 Qbase 1 (by norm_num) hQbase (by norm_num)
  refine ⟨D,A,L0,hD,hA,hL0,?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio hF hE hr heq hlog
    hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
  let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
  let fv := verticalBinVector I ⌈C*W/w⌉₊ W f
  let gv := verticalBinVector I ⌈C*W/w⌉₊ W g
  have hI : I⊆Finset.range (2*⌈C*W/w⌉₊+1) := Finset.filter_subset _ _
  have hfe := verticalBinVector_energy I ⌈C*W/w⌉₊ W hW hI f hfm hf2
  have hge := verticalBinVector_energy I ⌈C*W/w⌉₊ W hW hI g hgm hg2
  have hfl := verticalBinVector_l1 I ⌈C*W/w⌉₊ W hW f hfm hf1
  have hgl := verticalBinVector_l1 I ⌈C*W/w⌉₊ W hW g hgm hg1
  have hQ := verticalBinVectorCost_nonneg w W c C
  have hQgrowth : verticalBinVectorCost w W c C≤Qbase*Real.exp (1*L^(9/10:ℝ)) := by
    simpa only [one_mul,Qbase] using verticalBinVectorCost_growth w W c C L m hw hW hC
      (by linarith) hWeq hmhi
  have hfbound (z) : ‖fv z‖≤verticalBinVectorCost w W c C := by
    simpa only [fv,I,verticalBinVectorCost,mul_one] using
      verticalBinVector_uniform I ⌈C*W/w⌉₊ W hW f 1 hfInf z
  have hgbound (z) : ‖gv z‖≤verticalBinVectorCost w W c C := by
    simpa only [gv,I,verticalBinVectorCost,mul_one] using
      verticalBinVector_uniform I ⌈C*W/w⌉₊ W hW g 1 hgInf z
  have hf1v : (∫ z, ‖fv z‖ ∂planeMeasure)≤verticalBinVectorCost w W c C*F :=
    hfl.2.trans (mul_le_mul_of_nonneg_left hfL1 hQ)
  have hg1v : (∫ z, ‖gv z‖ ∂planeMeasure)≤verticalBinVectorCost w W c C*E :=
    hgl.2.trans (mul_le_mul_of_nonneg_left hgL1 hQ)
  have hfvstrip : ∀ z, fv z≠0 → z.1∈Icc l r := by
    intro z hz
    by_contra h
    exact hz (verticalBinVector_horizontal_support I ⌈C*W/w⌉₊ W f (Icc l r) hfstrip z h)
  have hgvstrip : ∀ z, gv z≠0 → z.1∈Icc l r := by
    intro z hz
    by_contra h
    exact hz (verticalBinVector_horizontal_support I ⌈C*W/w⌉₊ W g (Icc l r) hgstrip z h)
  exact hmain L hL N I topLength W w htop hW hw hwW htime hlength
    (fun n => verticalBinCenter ⌈C*W/w⌉₊ W n)
    (fun n => (verticalBinLabels_admissible_centers _ w W c C hsmall hcC n).1)
    (fun n => (verticalBinLabels_admissible_centers _ w W c C hsmall hcC n).2)
    field hfield hfieldBound fv gv (verticalBinVector_measurable I _ W f hfm)
    (verticalBinVector_measurable I _ W g hgm) hfe.1 hge.1 hfl.1.norm hgl.1.norm
    F E ratio (verticalBinVectorCost w W c C) hF hE hr heq hlog hQ hQgrowth hfbound hgbound
    hf1v hg1v (by simpa only [one_mul] using hfe.2.trans hfE)
    (by simpa only [one_mul] using hge.2.trans hgE)
    l r m hstrip hfvstrip hgvstrip hmlo hmhi hWeq

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.band_projected_high_oai := @OAI.LipschitzHilbert.PacketRepresentation.band_projected_high_oai
