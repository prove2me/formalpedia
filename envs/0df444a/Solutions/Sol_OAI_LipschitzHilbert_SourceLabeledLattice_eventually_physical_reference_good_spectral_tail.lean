-- Prove2me | solution 1 for OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:28:16.601394+00:00
-- url     : https://prove2.me/submissions/f1fd98f2-f9be-4d70-af42-c28ff564dde5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_SourceLatticePacket_masked_mixed_reference_uniform_moments
import Theorems.Thm_OAI_LipschitzHilbert_SourceLatticePacket_reference_uniform_moments

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationPerturbation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-summable error in the smooth/dyadic comparison controls
its entire cubic variation, uniformly in the number of scales. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_add_rpow {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (1 / 3 : ℝ) ≤
      (finiteCubicVariation F N) ^ (1 / 3 : ℝ) +
        (finiteCubicVariation G N) ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖(F (p i.succ) + G (p i.succ)) -
        (F (p i.castSucc) + G (p i.castSucc))‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (1 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    calc
      _ ≤ (∑ i : Fin N, (‖F (p i.succ) - F (p i.castSucc)‖ +
          ‖G (p i.succ) - G (p i.castSucc)‖) ^ 3) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [add_sub_add_comm]
        exact norm_add_le _ _
      _ ≤ (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) +
          (∑ i : Fin N, ‖G (p i.succ) - G (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) := by
        simpa only [Real.rpow_ofNat] using Real.Lp_add_le_of_nonneg
          (Finset.univ : Finset (Fin N)) (by norm_num : (1 : ℝ) ≤ 3)
          (f := fun i => ‖F (p i.succ) - F (p i.castSucc)‖)
          (g := fun i => ‖G (p i.succ) - G (p i.castSucc)‖)
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      _ ≤ _ := add_le_add
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation F N p hmono)
          (by norm_num))
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation G N p hmono)
          (by norm_num))
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    exact add_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg G N) _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem cubicVariation_nonneg {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    0 ≤ cubicVariation F N := Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _

theorem cubicVariation_finset_sum {ι E : Type*} [NormedAddCommGroup E]
    (F : ι → ℕ → E) (s : Finset ι) (N : ℕ) :
    cubicVariation (fun n => ∑ i ∈ s, F i n) N ≤ ∑ i ∈ s, cubicVariation (F i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicVariation, finiteCubicVariation]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (finiteCubicVariation_add_rpow (F i) (fun n => ∑ j ∈ s, F j n) N).trans
      (add_le_add le_rfl ih)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact behavior of finite interval-sum variation under a common scalar.
This keeps polynomial localization independent of the number of scales. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (F : ℕ → E) (N : ℕ) :
    finiteCubicVariation (fun i => c • F i) N = |c| ^ 3 * finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  rw [Finset.mul₀_sup' (pow_nonneg (abs_nonneg c) 3)]
  congr 1
  funext p
  split_ifs with hp
  · simp only [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, Finset.mul_sum]
  · exact (mul_zero _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem tileEnvelope_nonneg (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ tileEnvelope a b l W n z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_VariationPacketL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of packet partial sums is bounded by the sum of packet
norms. This is used for the long-scale spatial oscillation and error terms. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem monotone_partition_crossing_unique {N j : ℕ}
    (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p)
    {i k : Fin N} (hi : (p i.castSucc).val ≤ j ∧ j < (p i.succ).val)
    (hk : (p k.castSucc).val ≤ j ∧ j < (p k.succ).val) : i = k := by
  rcases lt_trichotomy i k with hik | hik | hik
  · have h := hp (show i.succ ≤ k.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show i.val < k.val from hik)))
    have h' : (p i.succ).val ≤ (p k.castSucc).val := h
    omega
  · exact hik
  · have h := hp (show k.succ ≤ i.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show k.val < i.val from hik)))
    have h' : (p k.succ).val ≤ (p i.castSucc).val := h
    omega

theorem partition_single_step_cube_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3) ≤ ‖v‖ ^ 3 := by
  classical
  have hterm (i : Fin N) : ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3 =
      if (p i.castSucc).val ≤ j ∧ j < (p i.succ).val then ‖v‖ ^ 3 else 0 := by
    have hle : (p i.castSucc).val ≤ (p i.succ).val := hp (Fin.castSucc_le_succ i)
    by_cases hlow : j < (p i.castSucc).val
    · have hhigh : j < (p i.succ).val := hlow.trans_le hle
      simp [hlow, hhigh, Nat.not_le.mpr hlow]
    · by_cases hhigh : j < (p i.succ).val
      · simp [hlow, hhigh, Nat.le_of_not_gt hlow]
      · simp [hlow, hhigh]
  simp_rw [hterm]
  by_cases hex : ∃ i : Fin N, (p i.castSucc).val ≤ j ∧ j < (p i.succ).val
  · obtain ⟨k,hk⟩ := hex
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro i _ hik
      have hi : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
        fun hi => hik (monotone_partition_crossing_unique p hp hi hk)
      simp [hi]
    · simp
  · have hz (i : Fin N) : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
      fun hi => hex ⟨i,hi⟩
    simp only [hz, ite_false, if_false, Finset.sum_const_zero]
    positivity

theorem cubicVariation_single_step_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) : cubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ := by
  classical
  have hcube : finiteCubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ ^ 3 := by
    apply Finset.sup'_le
    intro p _
    split_ifs with hp
    · exact partition_single_step_cube_le v j N p hp
    · positivity
  have h := Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hcube (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hpow : (‖v‖ ^ 3) ^ (1 / 3 : ℝ) = ‖v‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg v)]
    norm_num
  simpa only [cubicVariation, hpow] using h

theorem cubicVariation_packetPartialSum_le {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (f : Fin N → E) : cubicVariation (packetPartialSum f) N ≤ ∑ j, ‖f j‖ := by
  change cubicVariation (fun n => ∑ j : Fin N, if j.val < n then f j else 0) N ≤ _
  exact (cubicVariation_finset_sum (fun (j : Fin N) (n : ℕ) => if j.val < n then f j else 0) Finset.univ N).trans
    (Finset.sum_le_sum (fun j _ => cubicVariation_single_step_le (f j) j.val N))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_HilbertPacketSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Hilbert packet sums are continuous and agree with the generic
partial sums used for spatial oscillation estimates. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem partialBandSum_continuous {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (partialBandSum f n) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using (f j).continuous
  · simpa only [ite_eq_right hj] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem hilbertPartialBandSum_continuous {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (hilbertPartialBandSum f n) := by
  exact (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
    (continuous_pi (fun k => partialBandSum_continuous (fun j => f j k) n))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coefficient decomposes exactly into its frozen main part
and the angular error whose positive majorant was proved above. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_sub {Ω σ κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (area : σ → ℝ) (f h : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ)
    (hf : ∀ i k, Integrable (fun z => g z k * conj (f i k z)) μ)
    (hh : ∀ i k, Integrable (fun z => g z k * conj (h i k z)) μ) (i : σ) :
    analyzingCoefficient μ area (fun i k z => f i k z-h i k z) g i =
      analyzingCoefficient μ area f g i - analyzingCoefficient μ area h g i := by
  ext k
  change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z-h i k z) ∂μ) =
    ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z) ∂μ) -
      ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (h i k z) ∂μ)
  simp only [map_sub, mul_sub]
  rw [integral_sub (hf i k) (hh i k)]
  ring

theorem angularErrorWave_eq_sub {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) :
    angularErrorWave b ψ u t d i k z =
      b i k (u z) * ψ i k z - (if |u z-t| ≤ d then b i k t * ψ i k z else 0) := by
  unfold angularErrorWave multiplierError
  split_ifs <;> ring

theorem angularCoefficient_decomposition {ι κ : Type*}
    (area : ι → ℝ) (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (hOriginal : ∀ i k, Integrable (fun z => g z k * conj (b i k (u z) * ψ i k z)))
    (hMain : ∀ i k, Integrable (fun z => g z k *
      conj (if |u z-t| ≤ d then b i k t * ψ i k z else 0))) (i : ι) :
    analyzingCoefficient volume area (fun i k z => b i k (u z)*ψ i k z) g i =
      analyzingCoefficient volume area (fun i k z =>
        if |u z-t| ≤ d then b i k t*ψ i k z else 0) g i +
      analyzingCoefficient volume area (angularErrorWave b ψ u t d) g i := by
  have heq : angularErrorWave b ψ u t d = (fun i k z =>
      b i k (u z)*ψ i k z - (if |u z-t| ≤ d then b i k t*ψ i k z else 0)) := by
    funext i k z
    exact angularErrorWave_eq_sub b ψ u t d i k z
  rw [heq, analyzingCoefficient_sub volume area _ _ g hOriginal hMain]
  abel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product-measure dilation in the horizontal coordinate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem map_referenceHorizontalDilation (r : ℝ) (hr : r ≠ 0) :
    Measure.map (referenceHorizontalDilation r hr) (volume.prod volume) =
      ENNReal.ofReal |r⁻¹| • (volume.prod volume) := by
  change Measure.map (Prod.map id (fun x : ℝ => r*x)) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume measurable_id (by fun_prop),Measure.map_id]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,Measure.prod_smul_right]

theorem integral_referenceHorizontalDilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (r : ℝ) (hr : r ≠ 0) :
    (∫ z, f (referenceHorizontalDilation r hr z) ∂volume.prod volume) =
      |r⁻¹| • (∫ z, f z ∂volume.prod volume) := by
  rw [← integral_map_equiv (referenceHorizontalDilation r hr),map_referenceHorizontalDilation,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationContinuous
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite variation function. This permits
pointwise interval John--Nirenberg bounds, without exceptional lines. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem continuous_finiteCubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : X) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Continuous (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact continuous_finsetSum _ (fun i _ => ((hF _).sub (hF _)).norm.pow 3)
    · simp only [g, ite_eq_right hp]
      exact continuous_const
  have hs := Continuous.finset_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

theorem continuous_cubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => cubicVariation (fun n => F n x) N) := by
  apply (continuous_finiteCubicVariation F hF N).rpow_const
  intro x
  exact Or.inr (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Perturbing finite variation by a short-scale sequence. -/

noncomputable section

namespace LipschitzHilbert

theorem cubicVariation_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E) (N : ℕ) : cubicVariation (fun n => -F n) N = cubicVariation F N := by
  have heq : (fun n => -F n) = fun n => (-1 : ℝ) • F n := by funext n; simp
  rw [heq, cubicVariation, finiteCubicVariation_smul]
  norm_num [cubicVariation]

theorem cubicVariation_add_le {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) : cubicVariation (fun n => F n + G n) N ≤
      cubicVariation F N + cubicVariation G N := finiteCubicVariation_add_rpow F G N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_LinePacketFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite packet data on a reference line, with local coefficient
budgets kept explicit. No concentration or synthesis estimate is part of
the data. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem continuous_variation (P : LinePacketFamily N κ ι) : Continuous P.variation :=
  continuous_cubicVariation _ (hilbertPartialBandSum_continuous P.packets) N

end LinePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PolynomialLineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply a common horizontal top weight to actual line packets. The
coefficient budget is unchanged, and the packet order is fixed by the
weight degree, independently of the moment order. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert.LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem cubicVariation_smul_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E) (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    cubicVariation (fun n => c • F n) N = c * cubicVariation F N := by
  rw [cubicVariation, finiteCubicVariation_smul, abs_of_nonneg hc,
    Real.mul_rpow (pow_nonneg hc 3) (finiteCubicVariation_nonneg F N)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
  norm_num

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ)^n * (7*((n:ℝ)*Q)^n+R^n) ≤ (16*(Q+R+1)*(n:ℝ))^n := by
  let S := Q+R+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (n:ℝ)*Q ≤ (n:ℝ)*S := by dsimp [S]; nlinarith
  have hB : R ≤ (n:ℝ)*S := by
    have h := mul_le_mul_of_nonneg_right hnR hS
    dsimp [S] at h ⊢
    nlinarith
  have hAn := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hQ) hA n
  have hBn := pow_le_pow_left₀ hR hB n
  have h8 : (8:ℝ) ≤ 8^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hn
  calc
    _ ≤ 2^n * (8*((n:ℝ)*S)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ 2^n * (8^n*((n:ℝ)*S)^n) := by gcongr
    _ = (16*(Q+R+1)*(n:ℝ))^n := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      dsimp [S]
      ring

theorem ennreal_polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7*ENNReal.ofReal (((n:ℝ)*Q)^(n:ℝ)) +
      (ENNReal.ofReal R)^(n:ℝ)) ≤ ENNReal.ofReal ((16*(Q+R+1)*(n:ℝ))^n) := by
  have h := ENNReal.ofReal_le_ofReal (polynomial_moment_majorant Q R hQ hR n hn)
  simpa only [Real.rpow_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^n),
    ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 7*((n:ℝ)*Q)^n) (pow_nonneg hR n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow hR,
    ENNReal.ofReal_ofNat] using h

theorem lineMomentBase_pos (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching) :
    0 < lineMomentBase C D branching := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold lineMomentBase
  positivity

theorem line_moment_expression_le (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7 * ENNReal.ofReal
      ((((n:ℝ)*((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2))))/Real.log (3/2))^(n:ℝ)) +
      (ENNReal.ofReal (Real.sqrt D))^(n:ℝ)) ≤
    ENNReal.ofReal ((lineMomentBase C D branching*(n:ℝ))^n) := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hQ : 0 ≤ ((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2)))/Real.log (3/2) := by
    positivity
  simpa only [lineMomentBase, mul_div_assoc] using
    ennreal_polynomial_moment_majorant _ _ hQ (Real.sqrt_nonneg D) n hn

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MomentSuperlevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Use a natural moment at its chosen order to obtain a geometric
exceptional-set bound. No asymptotic or unspecified tail input is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem moment_superlevel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A threshold : ℝ) (ht : 0 < threshold) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | threshold ≤ |F x|} ≤
      ((ENNReal.ofReal A)/(ENNReal.ofReal threshold))^n*M := by
  have hsub : {x | threshold ≤ |F x|} ⊆
      {x | (ENNReal.ofReal threshold)^n ≤ (ENNReal.ofReal |F x|)^n} := by
    intro x hx
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
  have hmark := (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hF.norm.ennreal_ofReal.pow_const n) _).trans hm)
  have he0 : (ENNReal.ofReal threshold)^n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
  have het : (ENNReal.ofReal threshold)^n ≠ ⊤ := by finiteness
  calc
    _ = ((ENNReal.ofReal threshold)^n)⁻¹ *
        ((ENNReal.ofReal threshold)^n * μ {x | threshold ≤ |F x|}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
    _ ≤ ((ENNReal.ofReal threshold)^n)⁻¹ * ((ENNReal.ofReal A)^n*M) :=
      mul_le_mul' le_rfl hmark
    _ = _ := by rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]; ring

theorem moment_superlevel_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A : ℝ) (hA : 0 < A) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | 4*A ≤ |F x|} ≤ (1/4:ℝ≥0∞)^n*M := by
  have h := moment_superlevel μ F hF n A (4*A) (by positivity) M hm
  have hr : (ENNReal.ofReal A)/(ENNReal.ofReal (4*A)) = (1/4:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have ha : A/(4*A) = (1/4:ℝ) := by field_simp [hA.ne']
    rw [ha]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    norm_num
  simpa only [hr] using h

theorem quarter_pow_exp (n : ℕ) :
    (1/4:ℝ)^n = Real.exp (-(Real.log 4)*(n:ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarHorizontalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a top's horizontal length while retaining its packet
lattice and its original analyzing coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem horizontalRescale_mainCoefficient (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).mainCoefficient d
      (fun z => v (z.1,r*z.2)) (fun z => g (z.1,r*z.2)) j i = P.mainCoefficient d v g j i := by
  ext k
  simp only [mainCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑((P.horizontalRescale r hr).length j*P.width) : ℂ)⁻¹)*
      (∫ z, g (z.1,r*z.2) k * conj ((P.horizontalRescale r hr).selectedWave d
        (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z) ∂volume.prod volume) = _
  have heq : (fun z : ℝ × ℝ => g (z.1,r*z.2) k * conj
      ((P.horizontalRescale r hr).selectedWave d (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z)) =
      (fun z => (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w))
        (referenceHorizontalDilation r hr.ne' z)) := by
    funext z
    rfl
  have hint := integral_referenceHorizontalDilation
    (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w)) r hr.ne'
  rw [heq,hint,horizontalRescale_length,abs_of_pos (inv_pos.mpr hr)]
  change ((↑((P.length j/r)*P.width) : ℂ)⁻¹)*(r⁻¹ • _) =
    ((↑(P.length j*P.width) : ℂ)⁻¹)*_
  rw [Complex.real_smul]
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  rfl

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PositivePacketDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual derivative bounds for the positive packet square function. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem envelope_continuous (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) :
    Continuous (P.envelope j i) := by
  exact continuous_iff_continuousAt.mpr (fun x =>
    (lineEnvelope_three_hasDerivAt (P.centerX j i) (P.length j) x).continuousAt.mul continuousAt_const)

theorem positiveScale_continuous (P : LinePacketFamily N κ ι) (j : Fin N) :
    Continuous (P.positiveScale j) :=
  continuous_finsetSum _ (fun i _ => (P.envelope_continuous j i).const_mul _)

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SquareLineConcentration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every-line BMO and moments of the positive packet square function. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem squareSum_nonneg (P : LinePacketFamily N κ ι) (x : ℝ) : 0 ≤ P.squareSum x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squareSum_continuous (P : LinePacketFamily N κ ι) : Continuous P.squareSum :=
  continuous_finsetSum _ (fun j _ => (P.positiveScale_continuous j).pow 2)

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen selector values multiply the original Schwartz profiles.
They preserve the common seminorm bound, geometry and physical spectrum;
no new packet or concentration assumption is introduced. -/

noncomputable section
namespace LipschitzHilbert

theorem modulatedPlanarJet_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    modulatedPlanarJet (c • f) a cy l W delta frequency scale y hl i =
      c • modulatedPlanarJet f a cy l W delta frequency scale y hl i := by
  ext x
  simp only [modulatedPlanarJet,modulatedPlanarSlice_apply,planarProfileJet_eq,
    planarVerticalJet_smul,smul_smul,smul_apply,smul_eq_mul]
  ring

theorem physicalPlanarPacket_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a b l W theta frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    physicalPlanarPacket (c • f) a b l W theta frequency hl hW =
      c • physicalPlanarPacket f a b l W theta frequency hl hW := by
  ext z
  simp only [physicalPlanarPacket_apply,smul_apply,smul_eq_mul]
  ring

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

@[simp] theorem frozenProfile_raw (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (P.frozenProfile c hc).raw i j u k y = c j u k • P.raw i j u k y := by
  exact modulatedPlanarJet_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j)
    (P.frequency k) P.scale y (P.length_pos j).ne' i

@[simp] theorem frozenProfile_physicalPacket (t : ℝ) (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalPacket t j u k = c j u k • P.physicalPacket t j u k := by
  exact physicalPlanarPacket_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u+t*P.actualX j u) (P.length j) P.width
    (t+P.rowSlope j) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-family analyzing coefficients are exactly the
original physical packet integrals. Swapping coordinates and applying
the reference slope shear preserves product Lebesgue measure, including
for the totalized Bochner integral without an integrability premise. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem sourceReferenceToPhysical_measurePreserving (t : ℝ) :
    MeasurePreserving (sourceReferenceToPhysical t)
      (volume.prod volume) (volume.prod volume) :=
  (slopeShear_measurePreserving t).comp Measure.measurePreserving_swap

theorem integral_sourceReferenceToPhysical (t : ℝ) (F : ℝ × ℝ → ℂ) :
    (∫ z, F (sourceReferenceToPhysical t z) ∂volume.prod volume) =
      ∫ z, F z ∂volume.prod volume :=
  (sourceReferenceToPhysical_measurePreserving t).integral_comp
    (sourceReferenceToPhysical t).measurableEmbedding F

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

theorem family_selectedWave_physical (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ × ℝ) :
    P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) q k z =
      P.physicalSelectedWave t d v q k (sourceReferenceToPhysical t z) := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.2)
    (P.raw_eq_physical_slice 0 q.1 q.2 k z.1 t)
  change P.raw 0 q.1 q.2 k z.1 z.2 =
    P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) at h
  change (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.raw 0 q.1 q.2 k z.1 z.2 else 0) =
    (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) else 0)
  split_ifs
  · exact h
  · rfl

/-- The normalized coefficient is unchanged by passing from the
physical packets to their reference-line family. Both the original
field and the original test function are pulled back by the same map. -/
theorem family_mainCoefficient_physical (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) :
    P.family.mainCoefficient d (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) j u =
      P.physicalCoefficient t d v g j u := by
  ext k
  simp only [PlanarPacketFamily.mainCoefficient, physicalCoefficient, analyzingCoefficient,
    WithLp.ofLp_toLp, family_length]
  change ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g (sourceReferenceToPhysical t z) k * conj
        (P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) ⟨j, u⟩ k z)
          ∂volume.prod volume) =
    ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z)
        ∂volume.prod volume)
  congr 1
  simp_rw [P.family_selectedWave_physical]
  exact integral_sourceReferenceToPhysical t
    (fun z => g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z))

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only a nonzero frozen selector needs annular separation. Zero
selectors give zero packets, so empty scales and unused labels impose no
artificial spectral hypothesis. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

/-- Freezing a selector multiplies the original integral coefficient by
its complex conjugate. The assertion includes zero selectors. -/
theorem frozenProfile_mainCoefficient (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k =
      conj (c j u k)*P.family.mainCoefficient d v g j u k := by
  have hsel (z : ℝ×ℝ) :
      (P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z =
        c j u k*P.family.selectedWave d v ⟨j,u⟩ k z := by
    change (if v z ≤ d j then (P.frozenProfile c hc).raw 0 j u k z.1 z.2 else 0) =
      c j u k*(if v z ≤ d j then P.raw 0 j u k z.1 z.2 else 0)
    rw [P.frozenProfile_raw]
    by_cases h : v z ≤ d j <;> simp [h,smul_apply,smul_eq_mul]
  simp only [PlanarPacketFamily.mainCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change (↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj ((P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z)) =
    conj (c j u k)*((↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj (P.family.selectedWave d v ⟨j,u⟩ k z)))
  have heq : (fun z => g z k*conj ((P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z)) =
      (fun z => conj (c j u k)*(g z k*conj (P.family.selectedWave d v ⟨j,u⟩ k z))) := by
    funext z
    rw [hsel,map_mul]
    ring
  rw [heq,integral_const_mul]
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceTailOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A moment order proportional to the source parameter gives any fixed
exponential tail while its threshold loses only two polynomial powers. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_reference_tail_order (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧ 4*(n:ℝ) ≤ L^2 ∧
      (1/4:ℝ)^n ≤ Real.exp (-J*L) := by
  let d := J/Real.log 4+1
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [eventually_ge_atTop (max 1 (4*d+4))] with L hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hLd : 4*d+4 ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let n := ⌈d*L⌉₊
  have hlo : d*L ≤ (n:ℝ) := Nat.le_ceil _
  have hhi : (n:ℝ) ≤ d*L+1 := (Nat.ceil_lt_add_one (mul_pos hd hL0).le).le
  refine ⟨n,Nat.ceil_pos.mpr (mul_pos hd hL0),?_,?_⟩
  · nlinarith
  · rw [quarter_pow_exp]
    apply Real.exp_le_exp.mpr
    have hmult := mul_le_mul_of_nonneg_left hlo hlog.le
    have heq : Real.log 4*(d*L) = (J+Real.log 4)*L := by
      dsimp [d]
      field_simp [hlog.ne']
    rw [heq] at hmult
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBadEventUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finitely many deterministic residual events may be combined
before selecting a spatial point or a mass cutoff. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

/-- Fixed polynomial losses are absorbed by one extra unit in the
exponential decay rate. -/
theorem eventually_source_polynomial_exp (C a J : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, C*L^a*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 (by norm_num : (0:ℝ) < 1)
  filter_upwards [hdecay.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 1/C))] with L hL
  have hsmall : C*(L^a*Real.exp (-L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hL.le hC.le
    have heq : C*(1/C) = 1 := by field_simp
    simpa only [one_mul,neg_mul,heq] using h
  calc
    _ = (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) := by
      rw [show (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) =
        C*L^a*(Real.exp (-L)*Real.exp (-J*L)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ 1*Real.exp (-J*L) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Union measure on an actual interval, with the exact number of
square/error/shift events retained until exponential absorption. -/
theorem source_bad_event_union {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (events : Finset ι) (bad : ι → Set X) (δ : ℝ)
    (htail : ∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal δ*μ univ) :
    μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal ((events.card:ℝ)*δ)*μ univ := by
  calc
    _ ≤ ∑ i ∈ events, μ (bad i) := measure_biUnion_finset_le events bad
    _ ≤ ∑ _i ∈ events, ENNReal.ofReal δ*μ univ := Finset.sum_le_sum htail
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg events.card)]
      norm_cast
      ring


/-- The polynomial number of shift events loses one unit of exponential
rate, uniformly in all measurable spaces and finite event lists. -/
theorem eventually_source_bad_event_tail (a J : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι X : Type*) [MeasurableSpace X]
      (μ : Measure X) (events : Finset ι) (bad : ι → Set X),
      (events.card:ℝ) ≤ L^a →
      (∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*μ univ) →
      μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal (Real.exp (-J*L))*μ univ := by
  filter_upwards [eventually_source_polynomial_exp 1 a J (by norm_num)] with L hL
  intro ι X _ μ events bad hcard htail
  apply (source_bad_event_union μ events bad (Real.exp (-(J+1)*L)) htail).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans
    (by simpa only [one_mul] using hL)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCoefficientIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable tests make the original physical analyzing
integrals integrable, so coefficient polarization uses genuine linearity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem physicalSelectedWave_measurable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Measurable (P.physicalSelectedWave t d v q k) :=
  Measurable.ite (measurableSet_le hv measurable_const)
    (P.physicalPacket t q.1 q.2 k).continuous.measurable measurable_const

theorem physicalSelectedWave_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Integrable (P.physicalSelectedWave t d v q k) (volume.prod volume) :=
  (P.physicalPacket t q.1 q.2 k).integrable.indicator (measurableSet_le hv measurable_const)

theorem physical_analyzing_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (q : Σ j, ι j) (k : κ) :
    Integrable (fun z => g z k*conj (P.physicalSelectedWave t d v q k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalSelectedWave_integrable t d v hv q k).norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (P.physicalSelectedWave_measurable t d v hv q k))).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_mul,norm_star]
  have hk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (norm_nonneg _)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A symmetric reference cutoff is exactly three one-sided cutoffs,
including its boundary. No level-set nullity is required. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem physicalCenteredWave_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) :
    P.physicalCenteredWave s t d v q k z =
      P.physicalSelectedWave s (fun j => t+d j) v q k z+
      P.physicalSelectedWave s (fun j => d j-t) (fun z => -v z) q k z-
      P.physicalSelectedWave s (fun _ => 0) (fun _ => 0) q k z := by
  have heq : |v z-t| ≤ d q.1 ↔ v z ≤ t+d q.1 ∧ -v z ≤ d q.1-t := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold physicalCenteredWave physicalSelectedWave
  simp only [heq]
  by_cases hu : v z ≤ t+d q.1 <;> by_cases hl : -v z ≤ d q.1-t
  · simp [hu,hl]
  · simp [hu,hl]
  · simp [hu,hl]
  · exfalso
    linarith [hd q.1]

/-- Exact coefficient identity used for symmetric frozen selectors.
All three terms have monotone thresholds whenever the original d does. -/
theorem physicalCenteredCoefficient_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (u : ι j) :
    P.physicalCenteredCoefficient s t d v g j u =
      P.physicalCoefficient s (fun j => t+d j) v g j u+
      P.physicalCoefficient s (fun j => d j-t) (fun z => -v z) g j u-
      P.physicalCoefficient s (fun _ => 0) (fun _ => 0) g j u := by
  ext k
  have hU := P.physical_analyzing_integrable s (fun j => t+d j) v hv g hg hg1 ⟨j,u⟩ k
  have hD := P.physical_analyzing_integrable s (fun j => d j-t) (fun z => -v z)
    hv.neg g hg hg1 ⟨j,u⟩ k
  have hT := P.physical_analyzing_integrable s (fun _ => 0) (fun _ => 0)
    measurable_const g hg hg1 ⟨j,u⟩ k
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z) ∂volume.prod volume) = _
  simp_rw [P.physicalCenteredWave_eq s t d hd v,map_sub,map_add,mul_sub,mul_add]
  have hsub := integral_sub (hU.add hD) hT
  simp only [Pi.add_apply] at hsub
  rw [hsub,integral_add hU hD]
  change _ = ((↑(P.length j*P.width):ℂ)⁻¹)*_+
    ((↑(P.length j*P.width):ℂ)⁻¹)*_-((↑(P.length j*P.width):ℂ)⁻¹)*_
  ring

theorem centered_upper_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => t+d j) := by
  intro i j h
  dsimp only
  linarith [hd h]

theorem centered_lower_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => d j-t) := fun _ _ h => sub_le_sub_right (hd h) t

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual top masks restricted to the affine reference line. The
bandwidth and derivative costs retain the exact top length and slope. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.SlopeBox

theorem mask_on_reference_line (T : SlopeBox) (L A t y x : ℝ) :
    T.mask L A (x,y+t*x) = sincProductMask ⌈L⌉₊
      (T.maskLineA L A*x+T.maskLineB L A)
      (T.maskLineC L A t*x+T.maskLineD L A y) := by
  unfold mask topSincMask horizontal transverse
  congr 1 <;> dsimp only [maskLineA,maskLineB,maskLineC,maskLineD] <;> ring

theorem mask_on_scaled_reference_line (T : SlopeBox) (L A t y R x : ℝ) :
    T.mask L A (R*x,y+t*(R*x)) = sincProductMask ⌈L⌉₊
      ((R*T.maskLineA L A)*x+T.maskLineB L A)
      ((R*T.maskLineC L A t)*x+T.maskLineD L A y) := by
  rw [T.mask_on_reference_line]
  congr 1 <;> ring

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smallness of the actual top-mask derivative and Fourier radius
follows from packet shortness and the fixed narrow cone. All scale
parameters cancel before choosing the large manuscript parameter. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SlopeBox

/-- The source exponent A is fixed before choosing L. In particular no
factor involving the number or lengths of packets enters this choice. -/
theorem eventually_mask_scalar_small {A cone lo : ℝ} (hA : 1 < A)
    (hcone : 0 ≤ cone) (hlo : 0 < lo) :
    ∀ᶠ L : ℝ in atTop,
      (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo) := by
  let eps := min 1 (Real.pi*lo)
  have heps : 0 < eps := lt_min (by norm_num) (mul_pos Real.pi_pos hlo)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hA)).eventually_ge_atTop (4*(1+cone)/eps)]
    with L hL hpow
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have h := (Nat.ceil_lt_add_one hL0.le).le
    linarith
  have hLp : 0 < L^(A-1) := Real.rpow_pos_of_pos hL0 _
  have hbudget : 4*(1+cone) ≤ eps*L^(A-1) := by
    have h := (div_le_iff₀ heps).mp hpow
    simpa only [mul_comm] using h
  have hpower : L^A = L*L^(A-1) := by
    calc
      _ = L^(1+(A-1)) := by congr 1; ring
      _ = L^1*L^(A-1) := Real.rpow_add hL0 _ _
      _ = _ := by rw [Real.rpow_one]
  change _ ≤ eps
  calc
    _ ≤ (2*(2*L)/L^A)*(1+cone) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hceil (by norm_num))
        (Real.rpow_nonneg hL0.le _)) (by linarith)
    _ = (4*(1+cone))/L^(A-1) := by rw [hpower]; field_simp; ring
    _ ≤ eps := (div_le_iff₀ hLp).mpr hbudget

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-line packets are normalized at their actual horizontal
length before applying the published scalar variation input. The local
coefficient budget is independent of that length, the number of scales,
and the Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

@[simp] theorem referenceAnalyzedLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • P.family.mainCoefficient d v g j u := by
  dsimp only [referenceAnalyzedLine,PlanarPacketFamily.analyzedLine]
  dsimp only [referencePlanarFamily]
  rw [PlanarPacketFamily.horizontalRescale_mainCoefficient]
  rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMixedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference moments with distinct analyzing and synthesizing profiles.
The selector is frozen only in the analyzing coefficient; it is not
multiplied into the synthesis a second time. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

@[simp] theorem mixedReferenceLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  (P.frozenProfile c hc).referenceAnalyzedLine_coeff d v hv g hg hg1 y j u

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked reference family synthesizes the original physical top
mask and alternate packet. Its analyzing coefficient is unchanged, so
the normalization is the original `constant * pi^2`, not its doubled
synthesis-envelope constant. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

variable (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

variable (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
  (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)

@[simp] theorem maskedMixedReferenceLine_coeff (j : Fin N) (u : ι j) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  P.mixedReferenceLine_coeff c hc alt hAlt d v hv g hg hg1 y j u

@[simp] theorem maskedMixedReferenceLine_wave (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).wave j u k x =
      ((T j u).mask L A (P.topLength*x,y+t*(P.topLength*x)):ℂ)*
        (P.withProfile alt hAlt).raw 0 j u k y (P.topLength*x) := by
  rw [maskedMixedReferenceLine,LinePacketFamily.sincMasked_wave,
    P.mixedReferenceLine_wave,← (T j u).mask_on_scaled_reference_line]

theorem maskedMixedReferenceLine_partial (x : ℝ) (n : ℕ) :
    hilbertPartialBandSum
      (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).packets n x =
      (P.constant*Real.pi^2)⁻¹ • packetPartialSum
        (fun j => P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x)) n := by
  ext k
  simp only [hilbertPartialBandSum,partialBandSum,packetPartialSum,
    LinePacketFamily.packets,packetSynthesis_apply,maskedMixedReferenceBand,
    WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [P.maskedMixedReferenceLine_coeff,P.maskedMixedReferenceLine_wave,PiLp.smul_apply]
    simp only [Complex.real_smul]
    ring
  · simp only [ite_eq_right hj,WithLp.ofLp_zero,Pi.zero_apply,smul_zero]

theorem maskedMixedReferenceBand_variation (x : ℝ) :
    cubicVariation (packetPartialSum
      (fun j => P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x))) N =
      (P.constant*Real.pi^2)*
        (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).variation x := by
  have hD : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have heq : packetPartialSum (fun j =>
      P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x)) =
      fun n => (P.constant*Real.pi^2) • hilbertPartialBandSum
        (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).packets n x := by
    funext n
    rw [P.maskedMixedReferenceLine_partial c hc alt hAlt d v hv g hg hg1 T L A t y hrate x n,
      smul_smul,mul_inv_cancel₀ hD.ne',one_smul]
  rw [heq,LinePacketFamily.cubicVariation_smul_nonneg _ N _ hD.le]
  rfl

/-- In physical coordinates the frozen selector appears exactly once,
conjugated in the original analyzing coefficient. The synthesis packet
and its mask are the original physical ones. -/
theorem maskedMixedReferenceBand_physical (j : Fin N) (x : ℝ) :
    P.maskedMixedReferenceBand c hc alt hAlt d
      (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) T L A t y j x =
      WithLp.toLp 2 (fun k => ∑ u : ι j,
        (conj (c j u k)*P.physicalCoefficient t d v g j u k)*
          ((T j u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x)) := by
  ext k
  simp only [maskedMixedReferenceBand,WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.frozenProfile_mainCoefficient c hc,P.family_mainCoefficient_physical]
  have hraw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j u k y t)
  change (P.withProfile alt hAlt).raw 0 j u k y x =
    (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x) at hraw
  rw [hraw]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-order forms of the exact reference moments. The moment grid
may have fixed binary branching, independent of the source angular step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SourceLatticePacket

theorem referenceSquareMomentBase_pos (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) :
    0 < referenceSquareMomentBase B grid := by
  have hR : 0 ≤ LinePacketFamily.squareMeanConstant B := by
    unfold LinePacketFamily.squareMeanConstant
    positivity
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold referenceSquareMomentBase
  positivity

theorem reference_square_moment_majorant (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B)
    (n : ℕ) (hn : 1 ≤ n) :
    referenceSquareMomentCost B grid (2*(n:ℝ)) ≤
      ENNReal.ofReal ((referenceSquareMomentBase B grid*(n:ℝ))^n) := by
  have hR : 0 ≤ LinePacketFamily.squareMeanConstant B := by
    unfold LinePacketFamily.squareMeanConstant
    positivity
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hQ : 0 ≤ (((grid.branching:ℝ)+2)*(2*LinePacketFamily.squareMeanConstant B+
      48*(4*Real.pi)^4))/Real.log (3/2) := by positivity
  have h := ennreal_polynomial_moment_majorant _ _ hQ hR n hn
  simpa only [referenceSquareMomentCost,referenceSquareMomentBase,
    show 2*(n:ℝ)/2 = n by ring,mul_div_assoc] using h

theorem reference_variation_moment_majorant (M C B : ℝ) (grid : FiniteLineGrid)
    (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    referenceVariationMomentCost M C B grid n ≤
      ENNReal.ofReal ((lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ))^n) := by
  exact line_moment_expression_le C (M*C^2*B+1) grid.branching
    hC (Nat.cast_nonneg _) n hn

theorem reference_variation_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) (hF : Measurable F)
    (M C B : ℝ) (grid : FiniteLineGrid) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^(n:ℝ) ∂μ) ≤
      referenceVariationMomentCost M C B grid n*μ univ) :
    μ {x | 4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ |F x|} ≤
      (1/4:ℝ≥0∞)^n*μ univ := by
  have hbase := lineMomentBase_pos C (M*C^2*B+1) grid.branching hC (Nat.cast_nonneg _)
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply moment_superlevel_quarter μ F hF n _ (mul_pos hbase hnR)
  simpa only [ENNReal.rpow_natCast,ENNReal.ofReal_pow (mul_pos hbase hnR).le]
    using hm.trans (mul_le_mul' (reference_variation_moment_majorant M C B grid hC n hn) le_rfl)

/-- The square reference quantity has an exponential tail for its square;
this avoids any loss from taking roots in the moment estimate. -/
theorem reference_square_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) (hF : Measurable F)
    (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^(2*(n:ℝ)) ∂μ) ≤
      referenceSquareMomentCost B grid (2*(n:ℝ))*μ univ) :
    μ {x | 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ (F x)^2} ≤
      (1/4:ℝ≥0∞)^n*μ univ := by
  have hbase := referenceSquareMomentBase_pos B grid hB
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpow (x : X) : (ENNReal.ofReal |(F x)^2|)^n =
      (ENNReal.ofReal |F x|)^(2*(n:ℝ)) := by
    have hncast : 2*(n:ℝ) = ((2*n:ℕ):ℝ) := by push_cast; ring
    rw [hncast,ENNReal.rpow_natCast,abs_pow,ENNReal.ofReal_pow (abs_nonneg _),pow_mul]
  have hm' : (∫⁻ x, (ENNReal.ofReal |(F x)^2|)^n ∂μ) ≤
      (ENNReal.ofReal (referenceSquareMomentBase B grid*(n:ℝ)))^n*μ univ := by
    simp_rw [hpow]
    rw [← ENNReal.ofReal_pow (mul_pos hbase hnR).le]
    exact hm.trans (mul_le_mul' (reference_square_moment_majorant B grid hB n hn) le_rfl)
  have ht := moment_superlevel_quarter μ (fun x => (F x)^2) (hF.pow_const 2) n
    (referenceSquareMomentBase B grid*(n:ℝ)) (mul_pos hbase hnR) (μ univ) hm'
  simpa only [abs_sq] using ht

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed binary reference grids give polynomial thresholds with arbitrarily
strong exponential tails. The angular grid branching never enters this bound. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLatticePacket

/-- The reference variation constant grows at most linearly with the
packet envelope constant. All other parameters precede the packet family. -/
theorem binary_lineMomentBase_le (M B C : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hC : 0 ≤ C) :
    lineMomentBase C (M*C^2*B+1) 2 ≤
      lineMomentBase 1 (M*B+1) 2*(C+1) := by
  let t := C+1
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hCt : C ≤ t := by dsimp [t]; linarith
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hsq : C^2 ≤ t^2 := pow_le_pow_left₀ hC hCt 2
  have hone : (1:ℝ) ≤ t^2 := one_le_pow₀ ht
  have hD : M*C^2*B+1 ≤ (M*B+1)*t^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hMB]
  have hsqrt : Real.sqrt (M*C^2*B+1) ≤ Real.sqrt (M*B+1)*t := by
    apply (Real.sqrt_le_sqrt hD).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  calc
    _ ≤ 16*((4*(2*(Real.sqrt (M*B+1)*t)+4*(t*(4*Real.pi)^2)))/
        Real.log (3/2)+Real.sqrt (M*B+1)*t+t) := by
      unfold lineMomentBase
      norm_num only
      gcongr
    _ = _ := by dsimp [lineMomentBase,t]; ring

/-- One natural moment order works for every reference packet family,
line position, and binary grid. Its threshold is a fixed power of L. -/
theorem eventually_reference_thresholds (M B a J : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧
      (1/4:ℝ)^n ≤ Real.exp (-J*L) ∧ 1 ≤ L^(a+4) ∧
      ∀ (grid : FiniteLineGrid) (C : ℝ), grid.branching = 2 →
        0 ≤ C → C ≤ L^a →
        4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ L^(a+4) ∧
        4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ L^(a+4) := by
  let S := 16*((4*(2*LinePacketFamily.squareMeanConstant B+48*(4*Real.pi)^4))/
    Real.log (3/2)+LinePacketFamily.squareMeanConstant B+1)
  let V := lineMomentBase 1 (M*B+1) 2
  let K := max S V
  have hV : 0 < V := lineMomentBase_pos _ _ _ (by norm_num) (by norm_num)
  have hK : 0 < K := lt_of_lt_of_le hV (le_max_right _ _)
  filter_upwards [eventually_source_reference_tail_order J hJ,
    eventually_ge_atTop (max 2 (2*K))] with L hn hlarge
  obtain ⟨n,hn,hnL,hdecay⟩ := hn
  have hL : 1 ≤ L := le_trans (by norm_num : (1:ℝ) ≤ 2)
    ((le_max_left _ _).trans hlarge)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKL : 2*K ≤ L := (le_max_right _ _).trans hlarge
  have hLa : 1 ≤ L^a := Real.one_le_rpow hL ha
  refine ⟨n,hn,hdecay,Real.one_le_rpow hL (by linarith),?_⟩
  intro grid C hb hC hCL
  have hbase : referenceSquareMomentBase B grid = S := by
    unfold referenceSquareMomentBase
    rw [hb]
    norm_num only [Nat.cast_ofNat]
    rfl
  have hCb : C+1 ≤ 2*L^a := by linarith
  have hfactor : K*(C+1) ≤ L^a*L := by
    calc
      _ ≤ K*(2*L^a) := mul_le_mul_of_nonneg_left hCb hK.le
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hKL (Real.rpow_nonneg hL0.le a)]
  have hpoly : (L^a*L)*L^2 ≤ L^(a+4) := by
    calc
      _ = L^(a+3) := by
        rw [Real.rpow_add hL0]
        rw [show L^(3:ℝ) = L^(3:ℕ) from Real.rpow_natCast L 3]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hbound (b : ℝ) (hb : b ≤ K*(C+1)) : 4*(b*(n:ℝ)) ≤ L^(a+4) := by
    calc
      _ = b*(4*(n:ℝ)) := by ring
      _ ≤ (K*(C+1))*(4*(n:ℝ)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (L^a*L)*L^2 := mul_le_mul hfactor hnL (by positivity) (by positivity)
      _ ≤ _ := hpoly
  constructor
  · apply hbound
    rw [hbase]
    exact (le_max_left S V).trans (by nlinarith)
  · apply hbound
    rw [hb]
    norm_num only [Nat.cast_ofNat]
    exact (binary_lineMomentBase_le M B C hM hB hC).trans
      (mul_le_mul_of_nonneg_right (le_max_right S V) (by linarith))

/-- The moment hypotheses are the exact previously proved reference moment
bounds; no concentration or path estimate is assumed. -/
theorem reference_polynomial_tails_of_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F V : X → ℝ) (hF : Measurable F) (hV : Measurable V)
    (M B C T : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (n : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hs : 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ T)
    (hv : 4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ T)
    (hsm : (∫⁻ x, (ENNReal.ofReal |F x|)^(2*(n:ℝ)) ∂μ) ≤
      referenceSquareMomentCost B grid (2*(n:ℝ))*μ univ)
    (hvm : (∫⁻ x, (ENNReal.ofReal |V x|)^(n:ℝ) ∂μ) ≤
      referenceVariationMomentCost M C B grid n*μ univ) :
    μ {x | T ≤ |F x|} ≤ (1/4:ℝ≥0∞)^n*μ univ ∧
      μ {x | T ≤ |V x|} ≤ (1/4:ℝ≥0∞)^n*μ univ := by
  constructor
  · apply (measure_mono (show {x | T ≤ |F x|} ⊆
        {x | 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ (F x)^2} from ?_)).trans
      (reference_square_tail μ F hF B grid hB n hn hsm)
    intro x hx
    have h1 : 1 ≤ |F x| := hT.trans hx
    have : |F x| ≤ (F x)^2 := by nlinarith [sq_abs (F x)]
    exact hs.trans (hx.trans this)
  · exact (measure_mono (fun x hx => hv.trans hx)).trans
      (reference_variation_tail μ V hV M C B grid hC n hn hvm)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedPhysicalTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial thresholds for the actual masked mixed reference
family. Shortness and the narrow cone supply the mask hypotheses for
every sufficiently large L; no separate mask spectrum is assumed. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem masked_mixed_reference_polynomial_tails (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∃ rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j,
    ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) →
      let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
      grid.lineMeasure {x | L^(q+5) ≤ |Q.squareFunction x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ ∧
      grid.lineMeasure {x | L^(q+5) ≤ |Q.variation x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  obtain ⟨B,M,hB,hM,hm⟩ := masked_mixed_reference_uniform_moments hVariation hlo hhi
  filter_upwards [eventually_reference_thresholds M B (q+1) J hM.le hB.le (by linarith) hJ,
    SlopeBox.eventually_mask_scalar_small hA hcone hlo,
    eventually_ge_atTop (2:ℝ)] with L hthreshold hsmall hL2
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hL2
  obtain ⟨n,hn,hdecay,hT,hthreshold⟩ := hthreshold
  rw [show (q+1)+4 = q+5 by ring] at hT hthreshold
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh hSlow hShigh T t hshort hcone'
  let rate := P.physicalReferenceMaskRate T L A t cone lo hL hshort hcone' hsmall
  refine ⟨rate,?_⟩
  intro y grid hb hwidth
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
  have hC : 2*P.constant ≤ L^(q+1) := by
    calc
      _ ≤ L*L^q := mul_le_mul hL2 hP P.constant_pos.le hL.le
      _ = _ := by rw [Real.rpow_add hL,Real.rpow_one]; ring
  have hC0 : 0 ≤ 2*P.constant := mul_nonneg (by norm_num) P.constant_pos.le
  have hb' : 1 < grid.branching := by omega
  have hmoment := hm N κ ι P c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh hSlow hShigh T L A t cone hL hshort hcone' hsmall y grid hb' hwidth
  have ht := hthreshold grid (2*P.constant) hb hC0 hC
  have htail := reference_polynomial_tails_of_moments grid.lineMeasure Q.squareFunction Q.variation
    (Q.squareSum_continuous.sqrt.measurable) Q.continuous_variation.measurable
    M B (2*P.constant) (L^(q+5)) grid hB.le hC0 n hn hT ht.1 ht.2
    (hmoment (2*(n:ℝ)) (by positivity)).1 (hmoment n (by positivity)).2
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact ⟨htail.1.trans (mul_le_mul' hdecay' le_rfl),
    htail.2.trans (mul_le_mul' hdecay' le_rfl)⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local measure scaling from normalized reference lines to
physical intervals. Relative exceptional-set measure has no scale loss. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

/-- The Jacobian cancels exactly against the interval length. -/
theorem source_line_rescale_measure (r u H : ℝ) (hr : 0 < r)
    (bad : Set ℝ) (hbad : MeasurableSet bad) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) bad =
      ENNReal.ofReal r*(volume.restrict (Ico u (u+H)))
        ((fun x : ℝ => r*x) ⁻¹' bad) := by
  let s := Ico u (u+H) ∩ ((fun x : ℝ => r*x) ⁻¹' bad)
  have hs : MeasurableSet s := measurableSet_Ico.inter (hbad.preimage (by fun_prop))
  have hmap : Measure.map (fun x : ℝ => x/r) volume = ENNReal.ofReal r • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one,inv_inv,
      abs_of_pos hr,div_eq_mul_inv,mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hr.ne'))
  have hpre : (fun x : ℝ => x/r) ⁻¹' s = Ico (r*u) (r*(u+H)) ∩ bad := by
    ext x
    simp only [s,mem_preimage,mem_inter_iff,mem_Ico]
    rw [le_div_iff₀ hr,div_lt_iff₀ hr]
    have heq : r*(x/r) = x := by field_simp
    rw [heq]
    constructor <;> intro h <;> simpa only [mul_comm] using h
  have heq := congrArg (fun μ : Measure ℝ => μ s) hmap
  rw [Measure.map_apply (by fun_prop) hs,hpre] at heq
  rw [Measure.restrict_apply hbad,Measure.restrict_apply (hbad.preimage (by fun_prop))]
  simpa only [Measure.smul_apply,smul_eq_mul,inter_comm] using heq

/-- A normalized relative measure bound holds on its physical interval
with exactly the same relative constant. -/
theorem source_line_rescale_tail (r u H δ : ℝ) (hr : 0 < r) (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hsmall : (volume.restrict (Ico u (u+H))) ((fun x : ℝ => r*x) ⁻¹' bad) ≤
      ENNReal.ofReal δ*ENNReal.ofReal H) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) bad ≤
      ENNReal.ofReal δ*ENNReal.ofReal (r*H) := by
  rw [source_line_rescale_measure r u H hr bad hbad,ENNReal.ofReal_mul hr.le]
  calc
    _ ≤ ENNReal.ofReal r*(ENNReal.ofReal δ*ENNReal.ofReal H) := mul_le_mul' le_rfl hsmall
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore the physical horizontal variable and the exact coefficient
normalization after proving the normalized reference tail. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LipschitzHilbert

/-- An exact normalized-packet identity transfers a relative tail to the
original physical interval. The interval scale introduces no loss. -/
theorem source_physical_tail (r c u H δ small large : ℝ) (hr : 0 < r) (hc : 0 < c)
    (F Q : ℝ → ℝ) (hF : Measurable F) (heq : ∀ x, F (r*x) = c*Q x)
    (hthreshold : c*small ≤ large)
    (htail : (volume.restrict (Ico u (u+H))) {x | small ≤ |Q x|} ≤
      ENNReal.ofReal δ*ENNReal.ofReal H) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) {x | large ≤ |F x|} ≤
      ENNReal.ofReal δ*ENNReal.ofReal (r*H) := by
  apply source_line_rescale_tail r u H δ hr _ (measurableSet_le measurable_const (by simpa only [Real.norm_eq_abs] using hF.norm))
  apply (measure_mono (show (fun x : ℝ => r*x) ⁻¹' {x | large ≤ |F x|} ⊆
    {x | small ≤ |Q x|} from ?_)).trans htail
  intro x hx
  change large ≤ |F (r*x)| at hx
  rw [heq x,abs_mul,abs_of_pos hc] at hx
  exact (mul_le_mul_iff_right₀ hc).mp (hthreshold.trans hx)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedVariationTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked reference variation tail in original physical variables.
The interval may have any origin and any positive length containing the
retained packet lengths. Neither its scale nor its origin enters the
relative exceptional-measure constant. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

variable (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

theorem physicalMaskedBand_eq_reference (j : Fin N) (x : ℝ) :
    P.physicalMaskedBand c alt hAlt d v g T L A t y j x =
      P.maskedMixedReferenceBand c hc alt hAlt d
        (fun z => v (sourceReferenceToPhysical t z))
        (fun z => g (sourceReferenceToPhysical t z)) T L A t y j x :=
  (P.maskedMixedReferenceBand_physical c hc alt hAlt d v g T L A t y j x).symm

theorem physicalMaskedVariation_normalization
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)
    (x : ℝ) :
    P.physicalMaskedVariation c alt hAlt d v g T L A t y (P.topLength*x) =
      (P.constant*Real.pi^2)*
      (P.maskedMixedReferenceLine c hc alt hAlt d
        (fun z => v (sourceReferenceToPhysical t z))
        (hv.comp (sourceReferenceToPhysical t).measurable)
        (fun z => g (sourceReferenceToPhysical t z))
        (hg.comp (sourceReferenceToPhysical t).measurable)
        (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate).variation x := by
  unfold physicalMaskedVariation
  simp_rw [P.physicalMaskedBand_eq_reference c alt hAlt d v g T L A t y hc]
  exact P.maskedMixedReferenceBand_variation c hc alt hAlt d _
    (hv.comp (sourceReferenceToPhysical t).measurable) _
    (hg.comp (sourceReferenceToPhysical t).measurable)
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate x

include hc in
theorem physicalMaskedVariation_continuous
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    Continuous (P.physicalMaskedVariation c alt hAlt d v g T L A t y) := by
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d
    (fun z => v (sourceReferenceToPhysical t z))
    (hv.comp (sourceReferenceToPhysical t).measurable)
    (fun z => g (sourceReferenceToPhysical t z))
    (hg.comp (sourceReferenceToPhysical t).measurable)
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate
  have heq : P.physicalMaskedVariation c alt hAlt d v g T L A t y =
      fun x => (P.constant*Real.pi^2)*Q.variation (x/P.topLength) := by
    funext x
    have h := P.physicalMaskedVariation_normalization c alt hAlt d v g T L A t y hc
      hv hg hg1 rate (x/P.topLength)
    simpa only [mul_div_cancel₀ _ P.topLength_pos.ne'] using h
  rw [heq]
  exact continuous_const.mul (Q.continuous_variation.comp (continuous_id.div_const P.topLength))

/-- The actual physical masked variation has an arbitrary exponential
tail at a fixed polynomial threshold, uniformly over packet and interval
scales. The exceptional event is measurable by the exact normalization. -/
theorem physical_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalMaskedVariation c alt hAlt d v g T L A t y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt d v g T L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [masked_mixed_reference_polynomial_tails hVariation hlo hhi q J A cone hq hJ hA hcone,
    eventually_ge_atTop (max 1 (Real.pi^2))] with L htail hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hv' := hv.comp (sourceReferenceToPhysical t).measurable
  have hg' := hg.comp (sourceReferenceToPhysical t).measurable
  obtain ⟨rate,htail⟩ := htail N κ ι P hP c hc alt hAlt d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) hd hAlow hAhigh hSlow hShigh T t hshort hcone'
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u/P.topLength,
      width := H/P.topLength, width_pos := div_pos hH P.topLength_pos, depth := 0 }
  have hwidth' : ∀ j (_i : ι j), P.length j ≤ P.topLength*grid.width := by
    intro j i
    simpa only [grid,mul_div_cancel₀ _ P.topLength_pos.ne'] using hwidth j i
  have ht := (htail y grid rfl hwidth').2
  have hmass : grid.lineMeasure univ = ENNReal.ofReal (H/P.topLength) := by
    change (volume.restrict (Ico (u/P.topLength) (u/P.topLength+H/P.topLength))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rw [hmass] at ht
  have hcont := P.physicalMaskedVariation_continuous c alt hAlt d v g T L A t y hc hv hg hg1 rate
  refine ⟨hcont.measurable,?_⟩
  have hthreshold : (P.constant*Real.pi^2)*L^(q+5) ≤ L^(2*q+6) := by
    calc
      _ ≤ (L^q*L)*L^(q+5) := mul_le_mul_of_nonneg_right
        (mul_le_mul hP ((le_max_right _ _).trans hlarge) (sq_nonneg _)
          (Real.rpow_nonneg hL.le _)) (Real.rpow_nonneg hL.le _)
      _ = (L^q*L^(1:ℝ))*L^(q+5) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hL,← Real.rpow_add hL]
        congr 1
        ring
  have h := source_physical_tail P.topLength (P.constant*Real.pi^2)
    (u/P.topLength) (H/P.topLength) (Real.exp (-J*L)) (L^(q+5)) (L^(2*q+6))
    P.topLength_pos (mul_pos P.constant_pos (pow_pos Real.pi_pos _))
    (P.physicalMaskedVariation c alt hAlt d v g T L A t y) Q.variation hcont.measurable
    (fun x => P.physicalMaskedVariation_normalization c alt hAlt d v g T L A t y hc
      hv hg hg1 rate x) hthreshold ht
  have hlo' : P.topLength*(u/P.topLength) = u := mul_div_cancel₀ _ P.topLength_pos.ne'
  have hhi' : P.topLength*(u/P.topLength+H/P.topLength) = u+H := by
    rw [mul_add,mul_div_cancel₀ _ P.topLength_pos.ne',mul_div_cancel₀ _ P.topLength_pos.ne']
  have hlen : P.topLength*(H/P.topLength) = H := mul_div_cancel₀ _ P.topLength_pos.ne'
  rwa [hlo',hhi',hlen] at h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredMaskedVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric frozen coefficients in the actual masked synthesis.
The exact three-cutoff identity gives a fixed three-event loss, with no
assumption about the measure of selector boundary sets. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

theorem physicalCenteredMaskedBand_continuous (j : Fin N) :
    Continuous (P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro u _
  have hline : Continuous (fun x : ℝ => (x,y+t*x)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j u).mask_continuous L A).comp hline))).mul
      (((P.withProfile alt hAlt).physicalPacket t j u k).continuous.comp hline)

theorem physicalCenteredMaskedVariation_continuous :
    Continuous (P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredMaskedBand_continuous c alt hAlt d v g T L A t y j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem physicalCenteredMaskedBand_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x =
      P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x+
      P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x-
      P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x := by
  ext k
  simp only [physicalCenteredMaskedBand,physicalMaskedBand,WithLp.ofLp_toLp,
    PiLp.add_apply,PiLp.sub_apply]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.physicalCenteredCoefficient_eq t t d hd v hv g hg hg1]
  simp only [PiLp.add_apply,PiLp.sub_apply]
  ring

private theorem partial_add_sub {E : Type*} [AddCommGroup E]
    (F G H : Fin N → E) (n : ℕ) :
    packetPartialSum (fun j => F j+G j-H j) n =
      packetPartialSum F n+packetPartialSum G n-packetPartialSum H n := by
  unfold packetPartialSum
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem physicalCenteredMaskedPartial_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) (n : ℕ) :
    packetPartialSum (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x) n =
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x) n+
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x) n-
      packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x) n := by
  have hband : (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x) =
      fun j => P.physicalMaskedBand c alt hAlt (fun j => t+d j) v g T L A t y j x+
        P.physicalMaskedBand c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y j x-
        P.physicalMaskedBand c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y j x := by
    funext j
    exact P.physicalCenteredMaskedBand_eq c alt hAlt d v g T L A t y hd hv hg hg1 j x
  rw [hband]
  exact partial_add_sub _ _ _ n

private theorem cubic_variation_add_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F G H : ℕ → E) (n : ℕ) :
    cubicVariation (fun k => F k+G k-H k) n ≤
      cubicVariation F n+cubicVariation G n+cubicVariation H n := by
  have heq : (fun k => F k+G k-H k) = fun k => (F k+G k)+(-H k) := by
    funext k
    exact sub_eq_add_neg _ _
  rw [heq]
  apply (cubicVariation_add_le (fun k => F k+G k) (fun k => -H k) n).trans
  rw [cubicVariation_neg]
  exact add_le_add (cubicVariation_add_le F G n) le_rfl

theorem physicalCenteredMaskedVariation_le (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) :
    P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x ≤
      P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x+
      P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x+
      P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x := by
  have heq := funext (P.physicalCenteredMaskedPartial_eq c alt hAlt d v g T L A t y hd hv hg hg1 x)
  unfold physicalCenteredMaskedVariation
  rw [heq]
  exact cubic_variation_add_sub_le _ _ _ N

/-- The fixed three-cutoff loss costs one extra polynomial power and
one unit in the exponential rate. -/
theorem physical_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_masked_variation_tail hVariation hlo hhi q (J+1) A cone hq
    (by linarith) hA hcone,eventually_source_polynomial_exp 3 0 J (by norm_num),
    eventually_ge_atTop (4:ℝ)] with L htail hdecay hL4
  have hL : 0 < L := by linarith
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hmono hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hargs := htail N κ ι P hP c hc alt hAlt
  obtain ⟨_hU,hU⟩ := hargs (fun j => t+d j) v hv g hg hg1 (centered_upper_monotone t hmono)
    hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  obtain ⟨_hD,hD⟩ := hargs (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1
    (centered_lower_monotone t hmono) hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  obtain ⟨_hT,hT⟩ := hargs (fun _ => 0) (fun _ => 0) measurable_const g hg hg1
    (fun _ _ _ => le_rfl) hAlow hAhigh hSlow hShigh T t hshort hcone' y u H hH hwidth
  let U := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x|}
  let D := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x|}
  let S := {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x|}
  have hthreshold : 3*L^(2*q+6) ≤ L^(2*q+7) := by
    calc
      _ ≤ L*L^(2*q+6) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
        calc
          _ = L^(1:ℝ)*L^(2*q+6) := by rw [Real.rpow_one]
          _ = L^(1+(2*q+6)) := (Real.rpow_add hL _ _).symm
          _ = _ := by congr 1; ring
  have hsub : {x | L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x|} ⊆ U∪D∪S := by
    intro x hx
    by_contra hn
    have hnU : ¬x ∈ U := fun h => hn (Or.inl (Or.inl h))
    have hnD : ¬x ∈ D := fun h => hn (Or.inl (Or.inr h))
    have hnS : ¬x ∈ S := fun h => hn (Or.inr h)
    have hu : P.physicalMaskedVariation c alt hAlt (fun j => t+d j) v g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnU)
    have hv' : P.physicalMaskedVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnD)
    have hs : P.physicalMaskedVariation c alt hAlt (fun _ => 0) (fun _ => 0) g T L A t y x < L^(2*q+6) :=
      (le_abs_self _).trans_lt (lt_of_not_ge hnS)
    have hc0 := cubicVariation_nonneg
      (packetPartialSum (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x)) N
    change L^(2*q+7) ≤ |P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x| at hx
    change 0 ≤ P.physicalCenteredMaskedVariation c alt hAlt d v g T L A t y x at hc0
    rw [abs_of_nonneg hc0] at hx
    have hb := P.physicalCenteredMaskedVariation_le c alt hAlt d v g T L A t y hd hv hg hg1 x
    linarith
  let mu := volume.restrict (Ico u (u+H))
  have hunion := (measure_union_le (μ := mu) (U∪D) S).trans
    (add_le_add (measure_union_le U D) le_rfl)
  have hsum := add_le_add (add_le_add hU hD) hT
  refine ⟨(P.physicalCenteredMaskedVariation_continuous c alt hAlt d v g T L A t y).measurable,?_⟩
  apply (measure_mono hsub).trans (hunion.trans (hsum.trans ?_))
  calc
    _ = ENNReal.ofReal (3*Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenCenteredCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freezing a selector commutes with the actual physical centered
coefficient. This is an identity of totalized integrals, so no extra
integrability or boundary-level hypothesis is needed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

theorem frozenProfile_physicalCenteredWave (s t : ℝ) (d : Fin N → ℝ)
    (v : ℝ×ℝ → ℝ) (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) :
    (P.frozenProfile c hc).physicalCenteredWave s t d v q k z =
      c q.1 q.2 k*P.physicalCenteredWave s t d v q k z := by
  unfold physicalCenteredWave
  rw [P.frozenProfile_physicalPacket]
  by_cases h : |v z-t| ≤ d q.1 <;> simp [h,smul_apply,smul_eq_mul]

/-- The frozen selector contributes its conjugate to the analyzing
coefficient, including when it is zero and on cutoff boundaries. -/
theorem frozenProfile_physicalCenteredCoefficient (s t : ℝ) (d : Fin N → ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalCenteredCoefficient s t d v g j u k =
      conj (c j u k)*P.physicalCenteredCoefficient s t d v g j u k := by
  simp only [physicalCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change (↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj ((P.frozenProfile c hc).physicalCenteredWave s t d v ⟨j,u⟩ k z)
        ∂volume.prod volume) =
    conj (c j u k)*((↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z)
        ∂volume.prod volume))
  have heq : (fun z => g z k*conj
      ((P.frozenProfile c hc).physicalCenteredWave s t d v ⟨j,u⟩ k z)) =
      fun z => conj (c j u k)*(g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z)) := by
    funext z
    rw [P.frozenProfile_physicalCenteredWave,map_mul]
    ring
  rw [heq,integral_const_mul]
  ring

/-- The centered masked band is the original alternate synthesis with
the genuine centered coefficient of the frozen analyzing packet. -/
theorem physicalCenteredMaskedBand_eq_frozen
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
    (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ) (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x =
      WithLp.toLp 2 (fun k => ∑ u : ι j,
        (P.frozenProfile c hc).physicalCenteredCoefficient t t d v g j u k*
          ((T j u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x)) := by
  ext k
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp,
    P.frozenProfile_physicalCenteredCoefficient]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalPositiveScale
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact positive envelopes of the original physical coefficients.
The symmetric cutoff is controlled by the three actual one-sided
reference families, with no exceptional boundary convention. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem positiveEnvelope_nonneg (j : Fin N) (u : ι j) (y x : ℝ) :
    0 ≤ P.positiveEnvelope j u y x :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem physicalCenteredPositiveScale_nonneg (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalCenteredPositiveScale s t d v g j y x :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (norm_nonneg _) (P.positiveEnvelope_nonneg j u y x))

theorem physicalCenteredPositiveScale_le (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (y x : ℝ) :
    P.physicalCenteredPositiveScale s t d v g j y x ≤
      P.physicalPositiveScale s (fun j => t+d j) v g j y x+
      P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x+
      P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x := by
  unfold physicalCenteredPositiveScale physicalPositiveScale
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [P.physicalCenteredCoefficient_eq s t d hd v hv g hg hg1]
  have h := (norm_sub_le (P.physicalCoefficient s (fun j => t+d j) v g j u+
      P.physicalCoefficient s (fun j => d j-t) (fun z => -v z) g j u)
      (P.physicalCoefficient s (fun _ => 0) (fun _ => 0) g j u)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  have hmul := mul_le_mul_of_nonneg_right h (P.positiveEnvelope_nonneg j u y x)
  simpa only [add_mul] using hmul

theorem physicalCenteredPositiveScale_square_sum_le (s t : ℝ) (d : Fin N → ℝ)
    (hd : ∀ j, 0 ≤ d j) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) :
    (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2) ≤
      3*((∑ j, P.physicalPositiveScale s (fun j => t+d j) v g j y x^2)+
        (∑ j, P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2)+
        (∑ j, P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2)) := by
  have hpoint (j : Fin N) : P.physicalCenteredPositiveScale s t d v g j y x^2 ≤
      3*(P.physicalPositiveScale s (fun j => t+d j) v g j y x^2+
        P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2+
        P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2) := by
    let U := P.physicalPositiveScale s (fun j => t+d j) v g j y x
    let D := P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x
    let T := P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x
    have h := P.physicalCenteredPositiveScale_le s t d hd v hv g hg hg1 j y x
    have h0 := P.physicalCenteredPositiveScale_nonneg s t d v g j y x
    change _ ≤ U+D+T at h
    have hs := mul_self_le_mul_self h0 h
    change _ ≤ 3*(U^2+D^2+T^2)
    nlinarith [sq_nonneg (U-D),sq_nonneg (U-T),sq_nonneg (D-T)]
  calc
    _ ≤ ∑ j, 3*(P.physicalPositiveScale s (fun j => t+d j) v g j y x^2+
        P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2+
        P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem referenceAnalyzedLine_envelope (y : ℝ) (j : Fin N) (u : ι j) (x : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).envelope j u x =
      P.positiveEnvelope j u y (P.topLength*x) := by
  change lineEnvelope (P.referencePlanarFamily.centerX j u)
      (P.referencePlanarFamily.length j) 3 x*
    lineEnvelope (P.referencePlanarFamily.centerZ j u) P.width 2 y = _
  rw [referencePlanarFamily,PlanarPacketFamily.horizontalRescale_centerX,
    PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
    P.family_centerX,P.family_centerZ,P.family_length,
    lineEnvelope_horizontalDilation _ _ _ _ _ P.topLength_pos.ne']
  rfl

theorem referenceAnalyzedLine_positiveScale (t y x : ℝ) (j : Fin N) :
    (P.referenceAnalyzedLine d (fun z => v (sourceReferenceToPhysical t z))
      (hv.comp (sourceReferenceToPhysical t).measurable)
      (fun z => g (sourceReferenceToPhysical t z))
      (hg.comp (sourceReferenceToPhysical t).measurable) (fun _ => hg1 _) y).positiveScale j x =
      (P.constant*Real.pi^2)⁻¹*P.physicalPositiveScale t d v g j y (P.topLength*x) := by
  unfold LinePacketFamily.positiveScale physicalPositiveScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.referenceAnalyzedLine_coeff,P.family_mainCoefficient_physical,
    P.referenceAnalyzedLine_envelope,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (mul_pos P.constant_pos (pow_pos Real.pi_pos _)))]
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalReferenceSquare
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical positive main square is exactly the normalized
reference square function times its coefficient normalization. This
connects the symmetric frozen main term to three proved line estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

variable (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem physicalPositiveScale_eq_reference (j : Fin N) (y x : ℝ) :
    P.physicalPositiveScale t d v g j y x = (P.constant*Real.pi^2)*
      (P.physicalReferenceLine t d v hv g hg hg1 y).positiveScale j (x/P.topLength) := by
  have h := P.referenceAnalyzedLine_positiveScale d v hv g hg hg1 t y (x/P.topLength) j
  have hx : P.topLength*(x/P.topLength) = x := by field_simp [P.topLength_pos.ne']
  rw [hx] at h
  change _ = (P.constant*Real.pi^2)*_
  dsimp only [physicalReferenceLine]
  rw [h,← mul_assoc,mul_inv_cancel₀ (mul_pos P.constant_pos (pow_pos Real.pi_pos _)).ne',one_mul]

theorem physicalPositiveScale_square_sum_eq (y x : ℝ) :
    (∑ j, P.physicalPositiveScale t d v g j y x^2) =
      (P.constant*Real.pi^2)^2*(P.physicalReferenceSquare t d v hv g hg hg1 y x)^2 := by
  unfold physicalReferenceSquare LinePacketFamily.squareFunction
  rw [Real.sq_sqrt ((P.physicalReferenceLine t d v hv g hg hg1 y).squareSum_nonneg _)]
  unfold LinePacketFamily.squareSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [P.physicalPositiveScale_eq_reference t d v hv g hg hg1,mul_pow]

theorem physicalCenteredPositiveScale_square_reference (s : ℝ)
    (hd : ∀ j, 0 ≤ d j) (y x : ℝ) :
    (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2) ≤
      (3*(P.constant*Real.pi^2)^2)*
        ((P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x)^2+
         (P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x)^2+
         (P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x)^2) := by
  have h := P.physicalCenteredPositiveScale_square_sum_le s t d hd v hv g hg hg1 y x
  rw [P.physicalPositiveScale_square_sum_eq s (fun j => t+d j) v hv g hg hg1,
    P.physicalPositiveScale_square_sum_eq s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1,
    P.physicalPositiveScale_square_sum_eq s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredSquareBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical centered main square is controlled by three
reference squares. The resulting exceptional-set inclusion is exact. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

 theorem physicalCenteredSquare_nonneg (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    0 ≤ P.physicalCenteredSquare s t d v g y x := Real.sqrt_nonneg _

 theorem physicalCenteredSquare_sq (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    (P.physicalCenteredSquare s t d v g y x)^2 =
      ∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

 theorem physicalCenteredSquare_continuous (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y : ℝ) :
    Continuous (P.physicalCenteredSquare s t d v g y) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro j _
  apply Continuous.pow
  apply continuous_finsetSum
  intro u _
  unfold positiveEnvelope lineEnvelope
  apply Continuous.mul continuous_const
  apply Continuous.mul _ continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

 theorem physicalCenteredSquare_bad_subset (s t : ℝ) (d : Fin N → ℝ)
    (hd : ∀ j, 0 ≤ d j) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y small large : ℝ) (hsmall : 0 < small)
    (hlarge : 4*(P.constant*Real.pi^2)*small ≤ large) :
    {x | large ≤ P.physicalCenteredSquare s t d v g y x} ⊆
      {x | small ≤ |P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x|} ∪
      {x | small ≤ |P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x|} ∪
      {x | small ≤ |P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x|} := by
  intro x hx
  by_contra hn
  simp only [Set.mem_union,Set.mem_ofPred_eq,not_or] at hn
  have hU := lt_of_not_ge hn.1.1
  have hD := lt_of_not_ge hn.1.2
  have hT := lt_of_not_ge hn.2
  have hUsq : (P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hU.le 2
  have hDsq : (P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hD.le 2
  have hTsq : (P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hT.le 2
  have hbound := P.physicalCenteredPositiveScale_square_reference t d v hv g hg hg1 s hd y x
  rw [← P.physicalCenteredSquare_sq s t d v g] at hbound
  have hC : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have hCs : 0 < (P.constant*Real.pi^2)*small := mul_pos hC hsmall
  have hsum : (P.physicalCenteredSquare s t d v g y x)^2 ≤
      9*(P.constant*Real.pi^2)^2*small^2 := by
    have hscaled := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hUsq hDsq) hTsq)
      (by positivity : 0 ≤ 3*(P.constant*Real.pi^2)^2)
    nlinarith
  have h0 := P.physicalCenteredSquare_nonneg s t d v g y x
  have hpoint : P.physicalCenteredSquare s t d v g y x ≤ 3*(P.constant*Real.pi^2)*small := by
    nlinarith
  change large ≤ P.physicalCenteredSquare s t d v g y x at hx
  nlinarith

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalSquareTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive main square has a tail on every original physical
interval, with the exact reference coordinate change and no interval
scale in its constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

 theorem physical_reference_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
    ∀ (t y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalReferenceSquare t d v hv g hg hg1 y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(q+4) ≤ |P.physicalReferenceSquare t d v hv g hg hg1 y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  obtain ⟨B,M,hB,hM,hm⟩ := reference_uniform_moments hVariation hlo hhi
  have hB0 : 0 ≤ B/Real.pi^4 := by positivity
  filter_upwards [eventually_reference_thresholds M (B/Real.pi^4) q J hM.le hB0 hq hJ]
    with L hthreshold
  obtain ⟨n,hn,hdecay,hT,hthreshold⟩ := hthreshold
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hlow hhigh t y u H hH hwidth
  let Q := P.physicalReferenceLine t d v hv g hg hg1 y
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u/P.topLength,
      width := H/P.topLength, width_pos := div_pos hH P.topLength_pos, depth := 0 }
  have hv' := hv.comp (sourceReferenceToPhysical t).measurable
  have hg' := hg.comp (sourceReferenceToPhysical t).measurable
  have hwidth' : ∀ j (_i : ι j), P.length j ≤ P.topLength*grid.width := by
    intro j i
    simpa only [grid,mul_div_cancel₀ _ P.topLength_pos.ne'] using hwidth j i
  have hmoment := hm N κ ι P d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) hd hlow hhigh y grid (by decide : 1 < 2)
    hwidth'
  have ht := hthreshold grid P.constant rfl P.constant_pos.le hP
  have htail := (reference_polynomial_tails_of_moments grid.lineMeasure Q.squareFunction Q.variation
    (Q.squareSum_continuous.sqrt.measurable) Q.continuous_variation.measurable
    M (B/Real.pi^4) P.constant (L^(q+4)) grid hB0 P.constant_pos.le n hn hT ht.1 ht.2
    (hmoment (2*(n:ℝ)) (by positivity)).1 (hmoment n (by positivity)).2).1
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  have hmass : grid.lineMeasure univ = ENNReal.ofReal (H/P.topLength) := by
    change (volume.restrict (Ico (u/P.topLength) (u/P.topLength+H/P.topLength))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  have htail' := htail.trans (mul_le_mul' hdecay' le_rfl)
  rw [hmass] at htail'
  have hmeas : Measurable (P.physicalReferenceSquare t d v hv g hg hg1 y) :=
    Q.squareSum_continuous.sqrt.measurable.comp (measurable_id.div_const P.topLength)
  refine ⟨hmeas,?_⟩
  have h := source_physical_tail P.topLength 1 (u/P.topLength) (H/P.topLength)
    (Real.exp (-J*L)) (L^(q+4)) (L^(q+4)) P.topLength_pos zero_lt_one
    (P.physicalReferenceSquare t d v hv g hg hg1 y) Q.squareFunction hmeas
    (fun x => by
      change Q.squareFunction ((P.topLength*x)/P.topLength) = 1*Q.squareFunction x
      rw [mul_div_cancel_left₀ _ P.topLength_pos.ne',one_mul])
    (by simp only [one_mul,le_refl]) htail'
  have hlo' : P.topLength*(u/P.topLength) = u := mul_div_cancel₀ _ P.topLength_pos.ne'
  have hhi' : P.topLength*(u/P.topLength+H/P.topLength) = u+H := by
    rw [mul_add,mul_div_cancel₀ _ P.topLength_pos.ne',mul_div_cancel₀ _ P.topLength_pos.ne']
  have hlen : P.topLength*(H/P.topLength) = H := mul_div_cancel₀ _ P.topLength_pos.ne'
  rwa [hlo',hhi',hlen] at h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredSquareTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual symmetric frozen main coefficient has a single
polynomial exceptional threshold on every physical interval. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

 theorem physical_centered_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
    ∀ (s t y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalCenteredSquare s t d v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_reference_square_tail hVariation hlo hhi q (J+1) hq (by linarith),
    eventually_source_polynomial_exp 3 0 J (by norm_num),
    eventually_ge_atTop (max 1 (4*Real.pi^2))] with L htail hdecay hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hmono hlow hhigh s t y u H hH hwidth
  obtain ⟨_hU,hU⟩ := htail N κ ι P hP (fun j => t+d j) v hv g hg hg1
    (centered_upper_monotone t hmono) hlow hhigh s y u H hH hwidth
  obtain ⟨_hD,hD⟩ := htail N κ ι P hP (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1
    (centered_lower_monotone t hmono) hlow hhigh s y u H hH hwidth
  obtain ⟨_hT,hT⟩ := htail N κ ι P hP (fun _ => 0) (fun _ => 0) measurable_const g hg hg1
    (fun _ _ _ => le_rfl) hlow hhigh s y u H hH hwidth
  have hthreshold : 4*(P.constant*Real.pi^2)*L^(q+4) ≤ L^(2*q+6) := by
    have hpi : 4*Real.pi^2 ≤ L := (le_max_right _ _).trans hlarge
    have hC : 0 ≤ P.constant := P.constant_pos.le
    calc
      _ = (4*Real.pi^2)*P.constant*L^(q+4) := by ring
      _ ≤ L*L^q*L^(q+4) := by gcongr
      _ = L^(2*q+5) := by
        calc
          _ = (L^(1:ℝ)*L^q)*L^(q+4) := by rw [Real.rpow_one]
          _ = L^(1+q+(q+4)) := by rw [← Real.rpow_add hL,← Real.rpow_add hL]
          _ = _ := by congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  let U := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x|}
  let D := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x|}
  let T := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x|}
  have hsub : {x | L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x|} ⊆ U∪D∪T := by
    intro x hx
    apply P.physicalCenteredSquare_bad_subset s t d hd v hv g hg hg1 y
      (L^(q+4)) (L^(2*q+6)) (Real.rpow_pos_of_pos hL _) hthreshold
    change L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x| at hx
    change L^(2*q+6) ≤ P.physicalCenteredSquare s t d v g y x
    simpa only [abs_of_nonneg (P.physicalCenteredSquare_nonneg s t d v g y x)] using hx
  let mu := volume.restrict (Ico u (u+H))
  have hunion : mu (U∪D∪T) ≤
      (ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H+
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H)+
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
    calc
      _ ≤ (mu U+mu D)+mu T :=
        (measure_union_le (U∪D) T).trans (add_le_add (measure_union_le U D) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hU hD) hT
  refine ⟨(P.physicalCenteredSquare_continuous s t d v g y).measurable,?_⟩
  apply (measure_mono hsub).trans (hunion.trans ?_)
  calc
    _ = ENNReal.ofReal (3*Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

end LipschitzHilbert.SourceLatticePacket

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

theorem labelAtSlot_at {A : Type*} {B : ℕ} (e : A ↪ Fin B) (i : A) :
    labelAtSlot e (e i) = some i := by
  classical
  unfold labelAtSlot
  split_ifs with h
  · congr 1
    exact e.injective h.choose_spec
  · exact (h ⟨i, rfl⟩).elim

theorem labelAtSlot_eq_some {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    (b : Fin B) (i : A) : labelAtSlot e b = some i ↔ e i = b := by
  classical
  constructor
  · unfold labelAtSlot
    split_ifs with h
    · intro hi
      have heq : h.choose = i := Option.some.inj hi
      simpa only [heq] using h.choose_spec
    · simp
  · intro hi
    rw [← hi]
    exact labelAtSlot_at e i

theorem slotItem_label {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} {b : Fin B} (p : SlotItem e Item b) :
    labelAtSlot e b = some p.1.1 :=
  (labelAtSlot_eq_some e b p.1.1).mpr p.2

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

/-- Splitting by slots is an exact identity for arbitrary finite packet
sums, not an estimate and not a change to the waves. -/
theorem sum_slotted {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ b : Fin B, ∑ p : P.SlotItem hcard b j, f p.1.1 p.1.2) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.slotItemsEquiv hcard j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ b : Fin B, P.SlotItem hcard b j, f p.2.1.1 p.2.1.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

theorem slotValue_item (b : Fin B) (j : Fin N) (f : P.labels j → ℝ)
    (p : P.SlotItem hcard b j) : P.slotValue hcard b j f = f p.1.1 := by
  unfold slotValue
  rw [SourceSlopeLabels.slotItem_label (P.slotEmbedding hcard j) p]
  rfl

@[simp] theorem slotted_actualX (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualX j p = P.actualX j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originX j) + P.length j * (P.site j p.1.1 p.1.2).1 = _
  rw [P.slotValue_item hcard b j (P.originX j) p]
  rfl

@[simp] theorem slotted_actualZ (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualZ j p = P.actualZ j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originZ j) +
    P.slotValue hcard b j (P.rowSlope j) * P.length j * (P.site j p.1.1 p.1.2).1 +
      P.width * (P.site j p.1.1 p.1.2).2 = _
  rw [P.slotValue_item hcard b j (P.originZ j) p,
    P.slotValue_item hcard b j (P.rowSlope j) p]
  rfl

theorem slotted_rowSlope (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).rowSlope j = P.rowSlope j p.1.1 :=
  P.slotValue_item hcard b j (P.rowSlope j) p

@[simp] theorem slotted_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    (P.slotted hcard b).raw i j p k y = P.raw i j p.1.1 p.1.2 k y := by
  unfold SourceLatticePacket.raw raw
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

@[simp] theorem slotted_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    (P.slotted hcard b).physicalPacket t j p k = P.physicalPacket t j p.1.1 p.1.2 k := by
  unfold SourceLatticePacket.physicalPacket physicalPacket
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCoefficientSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original labeled physical coefficient splits into its centered
frozen selector and angular error, without changing synthesis packets. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem physicalMultiplierCoefficient_split (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    P.physicalMultiplierCoefficient t b v g j l u =
      P.physicalFrozenCenteredCoefficient t a b v g j l u+
        P.physicalAngularErrorCoefficient t a b v g j l u := by
  apply angularCoefficient_decomposition (fun _ : Item j l => P.length j*P.width)
    (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k) v t (a*(2:ℝ)^j.val) g
  · intro u k
    exact P.physical_multiplier_analyzing_integrable t (fun z => b j l k (v z))
      ((hb j l k).comp hv) (fun z => hb1 j l k (v z)) g hg hg1 j l u k
  · intro u k
    have hdist : Measurable (fun z => |v z-t|) := by
      simpa only [Real.norm_eq_abs] using (hv.sub_const t).norm
    have hm : Measurable (fun z : ℝ×ℝ =>
        if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0) :=
      Measurable.ite (measurableSet_le hdist measurable_const)
        measurable_const measurable_const
    have hm1 (z : ℝ×ℝ) :
        ‖if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0‖ ≤ 1 := by
      split_ifs
      · exact hb1 j l k t
      · simp only [norm_zero,zero_le_one]
    have h := P.physical_multiplier_analyzing_integrable t _ hm hm1 g hg hg1 j l u k
    simpa only [Measure.volume_eq_prod,ite_mul,zero_mul] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise norms of actual vector packets are controlled by the
same positive main and error envelopes used in the reference tails. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_packet_value_norm (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : Item j l) (c : EuclideanSpace ℂ κ) (y x : ℝ) :
    ‖P.rawPacketValue i j l u c y x‖ ≤
      P.absoluteConstant*(‖c‖*tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) := by
  have h := diagonal_packet_norm c (fun k => P.raw i j l u k y x)
    (mul_nonneg P.absoluteConstant_pos.le (tileEnvelope_nonneg _ _ _ _ _ _))
    (fun k => P.raw_absolute_tileEnvelope horder i j l u k (x,y))
  exact h.trans_eq (by ring)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledPositiveSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source coefficient supplies the positive per-length
main/error bound for every residual subset, with original synthesis waves. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem sum_physicalErrorScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    (∑ j, P.physicalErrorScale t a b v g j y x) =
      P.physicalAngularError t a b v g (x,y+t*x) := by
  unfold physicalErrorScale physicalAngularError
  congr 1
  funext j
  have hy : y+t*x-t*x = y := by ring
  simp only [hy]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlotTails
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed slope slots are summed before taking the source square or
variation. Only the fixed slot count enters the union bound; empty
slots are allowed. The polynomial threshold and exponential rate
absorb this count uniformly before any packet family is chosen. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert

/-- The square of the recombined positive scales costs the sum of the
individual slot squares, with constant one. -/
theorem source_slot_square_le {B N : ℕ} (f : Fin B → Fin N → ℝ) :
    Real.sqrt (∑ j, (∑ b, f b j)^2) ≤
      ∑ b, Real.sqrt (∑ j, f b j^2) := by
  let v (b : Fin B) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (f b)
  have hv (b : Fin B) : ‖v b‖ = Real.sqrt (∑ j, f b j^2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [v,Real.norm_eq_abs,sq_abs]
  have hs : ‖∑ b, v b‖ = Real.sqrt (∑ j, (∑ b, f b j)^2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,Real.norm_eq_abs,sq_abs]
  rw [← hs]
  exact (norm_sum_le _ _).trans_eq (by simp only [hv])

/-- Recombining slots before partial sums does not enlarge cubic
variation beyond the sum of the separate slot variations. -/
theorem source_slot_packet_variation_le {B N : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Fin B → Fin N → E) :
    cubicVariation (packetPartialSum (fun j => ∑ b, f b j)) N ≤
      ∑ b, cubicVariation (packetPartialSum (f b)) N := by
  have heq : packetPartialSum (fun j => ∑ b, f b j) =
      fun n => ∑ b, packetPartialSum (f b) n := by
    funext n
    unfold packetPartialSum
    calc
      _ = ∑ j : Fin N, ∑ b : Fin B, if j.val < n then f b j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := Finset.sum_comm
  rw [heq]
  exact cubicVariation_finset_sum _ Finset.univ N

/-- A positive extra threshold absorbs every fixed finite slot count,
including zero slots. -/
theorem source_slot_bad_subset {B : ℕ} {X : Type*}
    (f : Fin B → X → ℝ) (F : X → ℝ) {small large : ℝ}
    (_hsmall : 0 < small) (hlarge : (B:ℝ)*small < large)
    (hF : ∀ x, |F x| ≤ ∑ b, |f b x|) :
    {x | large ≤ |F x|} ⊆ ⋃ b, {x | small ≤ |f b x|} := by
  classical
  intro x hx
  by_contra hn
  have hpoint (b : Fin B) : |f b x| ≤ small := by
    have h : ¬ small ≤ |f b x| := by
      intro hb
      exact hn (Set.mem_iUnion.mpr ⟨b,hb⟩)
    exact (lt_of_not_ge h).le
  have hsum : (∑ b, |f b x|) ≤ (B:ℝ)*small := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b))
  exact (not_le_of_gt (((hF x).trans hsum).trans_lt hlarge)) hx

/-- General finite-slot union estimate, with an arbitrary reference
mass (in the application it is the physical interval length). -/
theorem source_slot_tail {B : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Fin B → X → ℝ) (F : X → ℝ)
    {small large : ℝ} (hsmall : 0 < small)
    (hlarge : (B:ℝ)*small < large) (hF : ∀ x, |F x| ≤ ∑ b, |f b x|)
    (δ mass : ℝ≥0∞) (htail : ∀ b, μ {x | small ≤ |f b x|} ≤ δ*mass) :
    μ {x | large ≤ |F x|} ≤ (B:ℝ≥0∞)*δ*mass := by
  apply (measure_mono (source_slot_bad_subset f F hsmall hlarge hF)).trans
  calc
    _ ≤ ∑ b : Fin B, μ {x | small ≤ |f b x|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _b : Fin B, δ*mass := Finset.sum_le_sum (fun b _ => htail b)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

/-- The constants are chosen before the slot functions, underlying
space or interval. One polynomial power and one exponential unit pay
for the fixed number of slots. -/
theorem eventually_source_fixed_slot_tail (B : ℕ) (a J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
      (f : Fin B → X → ℝ) (F : X → ℝ) (mass : ℝ≥0∞),
      (∀ x, |F x| ≤ ∑ b, |f b x|) →
      (∀ b, μ {x | L^a ≤ |f b x|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*mass) →
      μ {x | L^(a+1) ≤ |F x|} ≤ ENNReal.ofReal (Real.exp (-J*L))*mass := by
  filter_upwards [eventually_gt_atTop (max (B:ℝ) 0),
    eventually_source_polynomial_exp ((B:ℝ)+1) 0 J (by positivity)] with L hL hdecay
  have hL0 : 0 < L := (le_max_right _ _).trans_lt hL
  have hBL : (B:ℝ) < L := (le_max_left _ _).trans_lt hL
  have hthreshold : (B:ℝ)*L^a < L^(a+1) := by
    calc
      _ < L*L^a := mul_lt_mul_of_pos_right hBL (Real.rpow_pos_of_pos hL0 _)
      _ = L^a*L^(1:ℝ) := by rw [Real.rpow_one,mul_comm]
      _ = _ := (Real.rpow_add hL0 _ _).symm
  have hdecay' : (B:ℝ)*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
    apply (mul_le_mul_of_nonneg_right (show (B:ℝ) ≤ B+1 by linarith)
      (Real.exp_pos _).le).trans
    simpa only [Real.rpow_zero,mul_one] using hdecay
  intro X _ μ f F mass hF htail
  apply (source_slot_tail μ f F (Real.rpow_pos_of_pos hL0 _) hthreshold hF
    (ENNReal.ofReal (Real.exp (-(J+1)*L))) mass htail).trans
  have hc : (B:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(J+1)*L)) ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg B),ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal hdecay'
  exact mul_le_mul' hc le_rfl

end LipschitzHilbert

namespace LipschitzHilbert.SourceLatticePacket

/-- The actual centered positive squares of all narrow-label slots
have one physical exceptional threshold. Each slot may have a different
item type, including an empty item type at any scale. -/
theorem physical_centered_square_slot_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin B → Fin N → Type)
      [Fintype κ] [∀ b j, Fintype (ι b j)]
      (P : ∀ b, SourceLatticePacket N κ (ι b)),
      (∀ b, (P b).constant ≤ L^q) →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 ((P b).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P b).raw 0 j u k y) xi = 0) →
    ∀ (s t y u H : ℝ), 0 < H → (∀ b j (_i : ι b j), (P b).length j ≤ H) →
      Measurable (fun x => ∑ b, (P b).physicalCenteredSquare s t d v g y x) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |∑ b, (P b).physicalCenteredSquare s t d v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_square_tail hVariation hlo hhi q (J+1) hq (by linarith),
    eventually_source_fixed_slot_tail B (2*q+6) J] with L htail hslots
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hmono hlow hhigh s t y u H hH hwidth
  have hs (b : Fin B) := htail N κ (ι b) (P b) (hP b) d v hv g hg hg1 hd hmono
    (hlow b) (hhigh b) s t y u H hH (hwidth b)
  refine ⟨Finset.measurable_sum _ (fun b _ => (hs b).1),?_⟩
  have h := hslots ℝ (volume.restrict (Ico u (u+H)))
    (fun b x => (P b).physicalCenteredSquare s t d v g y x)
    (fun x => ∑ b, (P b).physicalCenteredSquare s t d v g y x)
    (ENNReal.ofReal H) (fun x => Finset.abs_sum_le_sum_abs _ _) (fun b => (hs b).2)
  simpa only [show 2*q+6+1 = 2*q+7 by ring] using h

/-- The actual centered masked variations of the fixed narrow-label
slots have a common physical tail. Recombining their packet bands is
controlled by `source_slot_packet_variation_le`. -/
theorem physical_centered_masked_variation_slot_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin B → Fin N → Type)
      [Fintype κ] [∀ b j, Fintype (ι b j)]
      (P : ∀ b, SourceLatticePacket N κ (ι b)),
      (∀ b, (P b).constant ≤ L^q) →
    ∀ (c : ∀ b j, ι b j → κ → ℂ) (hc : ∀ b j u k, ‖c b j u k‖ ≤ 1)
      (alt : ∀ b j, ι b j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ b j u k,
        planarProfileConstant (alt b j u k) (2*(P b).order) ≤ (P b).profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 (((P b).frozenProfile (c b) (hc b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 (((P b).frozenProfile (c b) (hc b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, |xi| < (lo/(P b).topLength)*(2:ℝ)^j.val →
        𝓕 (((P b).withProfile (alt b) (hAlt b)).raw 0 j u k y) xi = 0) →
      (∀ b j u k y xi, (hi/(P b).topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 (((P b).withProfile (alt b) (hAlt b)).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ b j, ι b j → SlopeBox) (t : ℝ),
      (∀ b j u, (P b).length j ≤ (T b j u).length) →
      (∀ b j u, |t-(T b j u).slope| ≤ cone*(T b j u).width/(P b).length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ b j (_i : ι b j), (P b).length j ≤ H) →
      Measurable (fun x => ∑ b, (P b).physicalCenteredMaskedVariation
        (c b) (alt b) (hAlt b) d v g (T b) L A t y x) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |∑ b, (P b).physicalCenteredMaskedVariation
          (c b) (alt b) (hAlt b) d v g (T b) L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_tail hVariation hlo hhi q (J+1)
    A cone hq (by linarith) hA hcone,
    eventually_source_fixed_slot_tail B (2*q+7) J] with L htail hslots
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hmono hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hs (b : Fin B) := htail N κ (ι b) (P b) (hP b) (c b) (hc b) (alt b) (hAlt b)
    d v hv g hg hg1 hd hmono (hAlow b) (hAhigh b) (hSlow b) (hShigh b)
    (T b) t (hshort b) (hcone' b) y u H hH (hwidth b)
  refine ⟨Finset.measurable_sum _ (fun b _ => (hs b).1),?_⟩
  have h := hslots ℝ (volume.restrict (Ico u (u+H)))
    (fun b x => (P b).physicalCenteredMaskedVariation
      (c b) (alt b) (hAlt b) d v g (T b) L A t y x)
    (fun x => ∑ b, (P b).physicalCenteredMaskedVariation
      (c b) (alt b) (hAlt b) d v g (T b) L A t y x)
    (ENNReal.ofReal H) (fun x => Finset.abs_sum_le_sum_abs _ _) (fun b => (hs b).2)
  simpa only [show 2*q+7+1 = 2*q+8 by ring] using h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive frozen main sum in the original labeled collection
is exactly the sum of the centered positive scales in its fixed slots.
The physical packets, coefficients and snapped envelopes are unchanged. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

theorem slotted_snappedSite (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) :
    (P.slotted hcard s).snappedSite j p = P.snappedSite j p.1.1 p.1.2 := by
  change snappedLatticeSite (P.slotValue hcard s j (P.originX j))
    (P.slotValue hcard s j (P.originZ j)) (P.length j) P.width
    (P.slotValue hcard s j (P.rowSlope j)) (P.site j p.1.1 p.1.2) = _
  rw [P.slotValue_item hcard s j (P.originX j) p,
    P.slotValue_item hcard s j (P.originZ j) p,
    P.slotValue_item hcard s j (P.rowSlope j) p]
  rfl

theorem slotted_positiveEnvelope (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j)
    (y x : ℝ) :
    (P.slotted hcard s).positiveEnvelope j p y x = P.positiveEnvelope j p.1.1 p.1.2 y x := by
  unfold SourceLatticePacket.positiveEnvelope positiveEnvelope
  rw [P.slotted_snappedSite hcard s j p,P.slotted_length hcard]
  rfl

theorem frozenSlot_positiveEnvelope (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1) (s : Fin B) (j : Fin N)
    (p : P.SlotItem hcard s j) (y x : ℝ) :
    (P.frozenSlot hcard t b hb s).positiveEnvelope j p y x =
      P.positiveEnvelope j p.1.1 p.1.2 y x :=
  P.slotted_positiveEnvelope hcard s j p y x

/-- Slotting and freezing reproduce the original centered physical
coefficient, with no integral or cutoff-boundary exception. -/
theorem frozenSlot_physicalCenteredCoefficient (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) :
    (P.frozenSlot hcard t b hb s).physicalCenteredCoefficient t t
        (fun j => a*(2:ℝ)^j.val) v g j p =
      P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2 := by
  have hpacket (k : κ) (z : ℝ×ℝ) :
      (P.frozenSlot hcard t b hb s).physicalCenteredWave t t
          (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z =
        if |v z-t| ≤ a*(2:ℝ)^j.val then
          b j p.1.1 k t*P.physicalPacket t j p.1.1 p.1.2 k z else 0 := by
    unfold SourceLatticePacket.physicalCenteredWave frozenSlot
    rw [(P.slotted hcard s).frozenProfile_physicalPacket,P.slotted_physicalPacket hcard]
    simp only [smul_apply,smul_eq_mul]
  ext k
  simp only [SourceLatticePacket.physicalCenteredCoefficient,
    physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*star ((P.frozenSlot hcard t b hb s).physicalCenteredWave t t
      (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z) ∂volume.prod volume) = _
  simp_rw [hpacket]
  rfl

/-- The original main positive scale is a literal fixed-slot sum. -/
theorem physicalMainScale_eq_slots (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      ∑ s : Fin B, (P.frozenSlot hcard t b hb s).physicalCenteredPositiveScale
        t t (fun j => a*(2:ℝ)^j.val) v g j y x := by
  let f (l : P.labels j) (u : Item j l) : ℝ :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hsum := P.sum_slotted (E := ℝ) hcard j f
  unfold physicalMainScale SourceLatticePacket.physicalCenteredPositiveScale
  symm
  calc
    _ = ∑ s : Fin B, ∑ p : P.SlotItem hcard s j,
        ‖P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2‖*
          P.positiveEnvelope j p.1.1 p.1.2 y x := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro p _
      rw [P.frozenSlot_physicalCenteredCoefficient hcard,
        P.frozenSlot_positiveEnvelope hcard]
    _ = _ := hsum

/-- The exact identity supplies the square domination consumed by the
fixed-slot physical tail theorem. -/
theorem physicalMainSquare_le_slots (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    Real.sqrt (∑ j, P.physicalMainScale t a b v g j y x^2) ≤
      ∑ s : Fin B, (P.frozenSlot hcard t b hb s).physicalCenteredSquare
        t t (fun j => a*(2:ℝ)^j.val) v g y x := by
  simp_rw [P.physicalMainScale_eq_slots hcard t a b hb v g]
  exact source_slot_square_le _

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

/-- Profile replacement commutes with the actual slot constructor. -/
theorem withProfile_slotted (b : Fin B) :
    (P.withProfile alt hAlt).slotted hcard b =
      (P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b) := by
  rfl

theorem slotted_alt_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).raw i j p k y =
      (P.withProfile alt hAlt).raw i j p.1.1 p.1.2 k y := by
  rw [← P.withProfile_slotted hcard alt hAlt b]
  exact (P.withProfile alt hAlt).slotted_raw hcard b i j p k y

theorem slotted_alt_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).physicalPacket t j p k =
      (P.withProfile alt hAlt).physicalPacket t j p.1.1 p.1.2 k := by
  rw [← P.withProfile_slotted hcard alt hAlt b]
  exact (P.withProfile alt hAlt).slotted_physicalPacket hcard b t j p k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMaskedSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Masked centered synthesis in the original labeled family is the
exact sum of its fixed-slot syntheses. In particular the cubic variation
is controlled by the actual centered masked variations already bounded
on physical intervals. No total-label factor occurs. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalCenteredMaskedBand_continuous (j : Fin N) :
    Continuous (P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hline : Continuous (fun x : ℝ => (x,y+t*x)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hline))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hline)

theorem physicalCenteredMaskedVariation_continuous :
    Continuous (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredMaskedBand_continuous alt hAlt t a b v g T L A y j
  · simp only [ite_eq_right hj]
    exact continuous_const

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
  (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)

include hb in
theorem slotCenteredMaskedBand_apply (s : Fin B) (j : Fin N) (x : ℝ) (k : κ) :
    P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x k =
      ∑ p : P.SlotItem hcard s j,
        P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2 k*
          ((T j p.1.1 p.1.2).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j p.1.1 p.1.2 k (x,y+t*x) := by
  have h := (P.slotted hcard s).physicalCenteredMaskedBand_eq_frozen
    (fun j p k => b j p.1.1 k t) (fun j p k => hb j p.1.1 k)
    (P.slottedAlt hcard alt s) (P.slottedAlt_bound hcard alt hAlt s)
    (fun j => a*(2:ℝ)^j.val) v g (fun j p => T j p.1.1 p.1.2) L A t y j x
  have he := congrArg (fun z : EuclideanSpace ℂ κ => z k) h
  change P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x k = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro p _
  have hc := congrArg (fun z : EuclideanSpace ℂ κ => z k)
    (P.frozenSlot_physicalCenteredCoefficient hcard t a b hb v g s j p)
  change ((P.slotted hcard s).frozenProfile (fun j p k => b j p.1.1 k t)
    (fun j p k => hb j p.1.1 k)).physicalCenteredCoefficient t t
      (fun j => a*(2:ℝ)^j.val) v g j p k = _ at hc
  rw [hc,P.slotted_alt_physicalPacket hcard alt hAlt]

include hb in
/-- Exact synthesis recombination, prior to taking any norm. -/
theorem physicalCenteredMaskedBand_eq_slots (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      ∑ s : Fin B, P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x := by
  ext k
  have hsum := P.sum_slotted (E := ℂ) hcard j
    (fun l u => P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  simp_rw [P.slotCenteredMaskedBand_apply alt hAlt t a b v g T L A y hcard hb]
  exact hsum.symm

include hb in
/-- Cubic variation is taken only after restoring the original labeled
packet sum, and costs the fixed sum of slot variations. -/
theorem physicalCenteredMaskedVariation_le_slots (x : ℝ) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x ≤
      ∑ s : Fin B, cubicVariation
        (packetPartialSum (fun j => P.slotCenteredMaskedBand
          alt hAlt t a b v g T L A y hcard s j x)) N := by
  unfold physicalCenteredMaskedVariation
  simp_rw [P.physicalCenteredMaskedBand_eq_slots alt hAlt t a b v g T L A y hcard hb]
  exact source_slot_packet_variation_le _

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical main-square and masked-variation tails after exact
recombination of the fixed narrow-label slots. Constants are selected
before the packet family, its scale range, and the physical interval. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMainSquare_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y : ℝ) :
    Continuous (P.physicalMainSquare t a b v g y) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro j _
  apply Continuous.pow
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  unfold positiveEnvelope lineEnvelope
  apply Continuous.mul continuous_const
  apply Continuous.mul _ continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

theorem physical_main_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ s j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ s j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [SourceLatticePacket.physical_centered_square_slot_tail
    hVariation hlo hhi B q J hq hJ] with L htail
  intro N κ Label Item _ _ P hcard hP t a ha b hb v hv g hg hg1 hlow hhigh y u H hH hwidth
  let Q := P.frozenSlot hcard t b hb
  have hconst (s : Fin B) : (Q s).constant ≤ L^q := hP
  have hd (j : Fin N) : 0 ≤ a*(2:ℝ)^j.val := mul_nonneg ha (by positivity)
  have hmono : Monotone (fun j : Fin N => a*(2:ℝ)^j.val) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) ha
  have hwidth' (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) : (Q s).length j ≤ H :=
    hwidth j p.1.1 p.1.2
  obtain ⟨_hm,ht⟩ := htail N κ (fun s => P.SlotItem hcard s) Q hconst
    (fun j => a*(2:ℝ)^j.val) v hv g hg hg1 hd hmono hlow hhigh t t y u H hH hwidth'
  refine ⟨(P.physicalMainSquare_continuous t a b v g y).measurable,?_⟩
  apply (measure_mono (show {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ⊆
    {x | L^(2*q+7) ≤ |∑ s, (Q s).physicalCenteredSquare t t
      (fun j => a*(2:ℝ)^j.val) v g y x|} from ?_)).trans ht
  intro x hx
  have h := P.physicalMainSquare_le_slots hcard t a b hb v g y x
  change L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x| at hx
  rw [abs_of_nonneg (show 0 ≤ P.physicalMainSquare t a b v g y x from
    Real.sqrt_nonneg _)] at hx
  exact hx.trans (h.trans (le_abs_self _))

theorem physical_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ s j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ s j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ j l u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
      (∀ j l u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, |t-(T j l u).slope| ≤ cone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [SourceLatticePacket.physical_centered_masked_variation_slot_tail
    hVariation hlo hhi B q J A cone hq hJ hA hcone] with L htail
  intro N κ Label Item _ _ P hcard hP alt hAlt t a ha b hb v hv g hg hg1
    hlow hhigh hSlow hShigh T hshort hangle y u H hH hwidth
  let Q := P.slotted hcard
  have hconst (s : Fin B) : (Q s).constant ≤ L^q := hP
  have hd (j : Fin N) : 0 ≤ a*(2:ℝ)^j.val := mul_nonneg ha (by positivity)
  have hmono : Monotone (fun j : Fin N => a*(2:ℝ)^j.val) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) ha
  have hslow (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) (k : κ) (y xi : ℝ)
      (hxi : |xi| < (lo/(Q s).topLength)*(2:ℝ)^j.val) :
      𝓕 (((Q s).withProfile (P.slottedAlt hcard alt s)
        (P.slottedAlt_bound hcard alt hAlt s)).raw 0 j p k y) xi = 0 := by
    rw [P.slotted_alt_raw hcard alt hAlt]
    exact hSlow j p.1.1 p.1.2 k y xi hxi
  have hshigh (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) (k : κ) (y xi : ℝ)
      (hxi : (hi/(Q s).topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 (((Q s).withProfile (P.slottedAlt hcard alt s)
        (P.slottedAlt_bound hcard alt hAlt s)).raw 0 j p k y) xi = 0 := by
    rw [P.slotted_alt_raw hcard alt hAlt]
    exact hShigh j p.1.1 p.1.2 k y xi hxi
  obtain ⟨_hm,ht⟩ := htail N κ (fun s => P.SlotItem hcard s) Q hconst
    (fun s j p k => b j p.1.1 k t) (fun s j p k => hb j p.1.1 k)
    (P.slottedAlt hcard alt) (P.slottedAlt_bound hcard alt hAlt)
    (fun j => a*(2:ℝ)^j.val) v hv g hg hg1 hd hmono hlow hhigh hslow hshigh
    (fun s j p => T j p.1.1 p.1.2) t
    (fun s j p => hshort j p.1.1 p.1.2) (fun s j p => hangle j p.1.1 p.1.2)
    y u H hH (fun s j p => hwidth j p.1.1 p.1.2)
  refine ⟨(P.physicalCenteredMaskedVariation_continuous alt hAlt t a b v g T L A y).measurable,?_⟩
  apply (measure_mono (show
    {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ⊆
    {x | L^(2*q+8) ≤ |∑ s, (Q s).physicalCenteredMaskedVariation
      (fun j p k => b j p.1.1 k t) (P.slottedAlt hcard alt s)
      (P.slottedAlt_bound hcard alt hAlt s) (fun j => a*(2:ℝ)^j.val) v g
      (fun j p => T j p.1.1 p.1.2) L A t y x|} from ?_)).trans ht
  intro x hx
  have h := P.physicalCenteredMaskedVariation_le_slots alt hAlt t a b v g T L A y hcard hb x
  change L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x| at hx
  rw [abs_of_nonneg (show 0 ≤ P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x from
    cubicVariation_nonneg _ _)] at hx
  exact hx.trans (h.trans (le_abs_self _))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed reference collection is a literal restriction of the
original labels. Its new reference coordinates keep every selected
profile, integer site and physical packet unchanged. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

theorem referenceFamily_actualZ (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).actualZ j l u =
      P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
        (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [actualZ,actualX,referenceFamily,length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) (k : κ) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).physicalPacket
      newSlope j l u k =
      P.physicalPacket oldSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  ext z
  simp only [physicalPacket,physicalPlanarPacket_apply]
  rw [P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency,
    P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency]
  have hx : P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u =
      P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
        oldSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by ring
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)) =
      oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by ring
  change Complex.exp (((P.frequency k *
    ((z.2-(P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))-
      (newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)))*(z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))):ℝ)*Complex.I) *
    P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k
      ((z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u)/P.length j,
      ((z.2-(P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))-
      (newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)))*(z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))/P.width) = _
  rw [hx,hs]

theorem referenceFamily_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ j (l : P.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(oldSlope+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) :
    let Q := P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
    ∀ j (l : Q.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (Q.physicalPacket newSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(newSlope+Q.rowSlope j l)*η| ≤ cStar/Q.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta := by
  dsimp only
  intro j l u k ξ η hξ
  rw [P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency j l u k] at hξ
  have h := hspectrum j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k ξ η hξ
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)) = oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by ring
  simpa only [referenceFamily,hs,length] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMainRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

/-- Nonzero frozen selector values force both shortness and narrow
angular membership. Any term annihilated by a zero frozen selector can
therefore be restricted exactly, including positive norm envelopes. -/
theorem sum_reference_frozen {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (c : ∀ l : P.labels j, Item j l → κ → ℂ)
    (f : ∀ l : P.labels j, Item j l → E)
    (hshort : ∀ l u k, c l u k ≠ 0 → P.length j ≤ referenceLength)
    (hsupport : ∀ l u k, c l u k ≠ 0 →
      |oldSlope+P.rowSlope j l-newSlope| ≤ cone*w/P.length j)
    (hvanish : ∀ l u, (∀ k, c l u k = 0) → f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  apply P.sum_referenceLabels_of_zero oldSlope newSlope referenceLength cone w j f
  intro l hout u
  apply hvanish l u
  intro k
  by_contra hn
  exact hout ⟨hshort l u k hn,hsupport l u k hn⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only nonzero frozen selectors enter the positive main scale.
Restricting to their fixed narrow reference cone is exact, and changes
the carrier bound without changing any retained physical packet or
positive envelope. The wide error family is not used in the main tail. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalFrozenCenteredCoefficient_eq_zero (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) (hz : ∀ k, b j l k t = 0) :
    P.physicalFrozenCenteredCoefficient t a b v g j l u = 0 := by
  ext k
  simp only [physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp,
    hz k,zero_mul,ite_self,map_zero,mul_zero,integral_zero,PiLp.zero_apply]

variable (t R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel t t R cone w

/-- The retained main family pays only the narrow cone's carrier
bound. Its absolute envelope constant is unchanged. -/
theorem referenceSelf_constant :
    (Q).constant = P.absoluteConstant*(F*cone+2) := by
  unfold constant absoluteConstant referenceFamily
  ring

theorem referenceSelf_snappedSite (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).snappedSite j l u = P.snappedSite j (orig j l) u := by
  change snappedLatticeSite (P.originX j (orig j l))
    (P.originZ j (orig j l)+(t-t)*P.originX j (orig j l)) (P.length j) P.width
    (P.rowSlope j (orig j l)+(t-t)) (P.site j (orig j l) u) = _
  simp only [sub_self,zero_mul,add_zero]
  rfl

theorem referenceSelf_positiveEnvelope (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (y x : ℝ) :
    (Q).positiveEnvelope j l u y x = P.positiveEnvelope j (orig j l) u y x := by
  unfold positiveEnvelope
  rw [P.referenceSelf_snappedSite t R cone w F hw hcone hF hwide hfrequency]
  rfl

theorem referenceSelf_frozenCenteredCoefficient (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalFrozenCenteredCoefficient t a (fun j l k s => b j (orig j l) k s)
      v g j l u = P.physicalFrozenCenteredCoefficient t a b v g j (orig j l) u := by
  ext k
  simp only [physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*starRingEnd ℂ
      (if |v z-t| ≤ a*(2:ℝ)^j.val then b j (orig j l) k t*(Q).physicalPacket t j l u k z else 0)
      ∂volume.prod volume) = _
  have hp (z : ℝ×ℝ) : (Q).physicalPacket t j l u k z =
      P.physicalPacket t j (orig j l) u k z := congrArg
        (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
        (P.referenceFamily_physicalPacket t t R cone w F hw hcone hF hwide hfrequency j l u k)
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact congrArg (fun f : ℂ => g z k*starRingEnd ℂ
    (if |v z-t| ≤ a*(2:ℝ)^j.val then b j (orig j l) k t*f else 0)) (hp z)

/-- The positive main scale may be restricted to the narrow fixed
reference family before any probabilistic or variational estimate. -/
theorem physicalMainScale_eq_narrow_reference (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      (Q).physicalMainScale t a (fun j l k s => b j (orig j l) k s) v g j y x := by
  let f (l : P.labels j) (u : Item j l) : ℝ :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hsum := P.sum_reference_frozen (E := ℝ) t t R cone w j
    (fun l _u k => b j l k t) f
    (fun l _u k hk => hshort j l k hk)
    (fun l _u k hk => hsupport j l k hk)
    (fun l u hz => by
      dsimp only [f]
      rw [P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz,norm_zero,zero_mul])
  unfold physicalMainScale
  symm
  calc
    _ = ∑ l : P.referenceLabels t t R cone w j, ∑ u : Item j l, f (orig j l) u := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro u _
      rw [P.referenceSelf_frozenCenteredCoefficient t R cone w F hw hcone hF hwide hfrequency,
        P.referenceSelf_positiveEnvelope t R cone w F hw hcone hF hwide hfrequency]
    _ = _ := hsum

theorem physicalMainSquare_eq_narrow_reference (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (y x : ℝ) :
    P.physicalMainSquare t a b v g y x =
      (Q).physicalMainSquare t a (fun j l k s => b j (orig j l) k s) v g y x := by
  unfold physicalMainSquare
  simp_rw [P.physicalMainScale_eq_narrow_reference t R cone w F hw hcone hF hwide hfrequency
    a b v g hshort hsupport]

theorem referenceSelf_alt_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l u k => alt j (orig j l) u k)
      (fun j l u k => hAlt j (orig j l) u k)).physicalPacket t j l u k =
      (P.withProfile alt hAlt).physicalPacket t j (orig j l) u k := by
  exact (P.withProfile alt hAlt).referenceFamily_physicalPacket
    t t R cone w F hw hcone hF hwide hfrequency j l u k

/-- The same exact narrow restriction holds for the masked main
synthesis, retaining the alternate profile and each original top mask. -/
theorem physicalCenteredMaskedBand_eq_narrow_reference
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      (Q).physicalCenteredMaskedBand (fun j l u k => alt j (orig j l) u k)
        (fun j l u k => hAlt j (orig j l) u k) t a
        (fun j l k s => b j (orig j l) k s) v g
        (fun j l u => T j (orig j l) u) L A y j x := by
  ext k
  let f (l : P.labels j) (u : Item j l) : ℂ :=
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)
  have hsum := P.sum_reference_frozen (E := ℂ) t t R cone w j
    (fun l _u k => b j l k t) f
    (fun l _u k hk => hshort j l k hk)
    (fun l _u k hk => hsupport j l k hk)
    (fun l u hz => by
      have hc := congrArg (fun c : EuclideanSpace ℂ κ => c k)
        (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
      dsimp only [f]
      rw [hc]
      simp)
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp]
  symm
  calc
    _ = ∑ l : P.referenceLabels t t R cone w j, ∑ u : Item j l, f (orig j l) u := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro u _
      rw [P.referenceSelf_frozenCenteredCoefficient t R cone w F hw hcone hF hwide hfrequency,
        P.referenceSelf_alt_physicalPacket t R cone w F hw hcone hF hwide hfrequency]
    _ = _ := hsum

theorem physicalCenteredMaskedVariation_eq_narrow_reference
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x =
      (Q).physicalCenteredMaskedVariation (fun j l u k => alt j (orig j l) u k)
        (fun j l u k => hAlt j (orig j l) u k) t a
        (fun j l k s => b j (orig j l) k s) v g
        (fun j l u => T j (orig j l) u) L A y x := by
  unfold physicalCenteredMaskedVariation
  congr 2
  funext j
  exact P.physicalCenteredMaskedBand_eq_narrow_reference
    t R cone w F hw hcone hF hwide hfrequency alt hAlt a b v g T L A y hshort hsupport j x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveReference
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow main reference family retains only labels active at the
frozen direction. Inactive labels contribute exactly zero, so neither
the square nor the masked variation needs spectral assumptions there. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

theorem frozenActiveLabels_card_le (j : Fin N) :
    (P.frozenActiveLabels t b j).card ≤ (P.labels j).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sum_frozenActive_of_zero {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, (∀ k, b j l k t = 0) → ∀ u, f l u = 0) :
    (∑ l : P.frozenActiveLabels t b j, ∑ u : Item j l,
      f (P.frozenActiveOriginalLabel t b j l) u) =
        ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have heq := Equiv.sum_comp (P.frozenActiveLabelsEquiv t b j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j // ¬∃ k, b j l k t ≠ 0},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro u _
    exact hzero l.val (fun k => by
      by_contra hn
      exact l.property ⟨k,hn⟩) u
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun l : P.labels j => ∃ k, b j l k t ≠ 0)
    (fun l => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact heq.trans hsum

theorem physicalMainScale_eq_frozenActive (a : ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      (P.frozenActiveFamily t b).physicalMainScale t a (P.frozenActiveSelector t b) v g j y x := by
  let f (l : P.labels j) (u : Item j l) :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hs := P.sum_frozenActive_of_zero t b (E := ℝ) j f (fun l hz u => by
    dsimp only [f]
    rw [P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz,norm_zero,zero_mul])
  exact hs.symm

theorem physicalMainSquare_eq_frozenActive (a : ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    P.physicalMainSquare t a b v g y x =
      (P.frozenActiveFamily t b).physicalMainSquare t a (P.frozenActiveSelector t b) v g y x := by
  unfold physicalMainSquare
  simp_rw [P.physicalMainScale_eq_frozenActive t b a v g]

theorem physicalCenteredMaskedBand_eq_frozenActive
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ) (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      (P.frozenActiveFamily t b).physicalCenteredMaskedBand
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l)) t a
        (P.frozenActiveSelector t b) v g
        (fun j l => T j (P.frozenActiveOriginalLabel t b j l)) L A y j x := by
  ext k
  let f (l : P.labels j) (u : Item j l) : ℂ :=
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)
  have hs := P.sum_frozenActive_of_zero t b (E := ℂ) j f (fun l hz u => by
    have hc := congrArg (fun c : EuclideanSpace ℂ κ => c k)
      (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
    dsimp only [f]
    rw [hc]
    simp)
  exact hs.symm

theorem physicalCenteredMaskedVariation_eq_frozenActive
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x =
      (P.frozenActiveFamily t b).physicalCenteredMaskedVariation
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l)) t a
        (P.frozenActiveSelector t b) v g
        (fun j l => T j (P.frozenActiveOriginalLabel t b j l)) L A y x := by
  unfold physicalCenteredMaskedVariation
  congr 2
  funext j
  exact P.physicalCenteredMaskedBand_eq_frozenActive t b alt hAlt a v g T L A y j x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledNarrowTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main reference tails use only the fixed narrow cone and the labels
whose frozen selector is nonzero. Thus the wide error-cone carrier bound
never enters the constants, and inactive synthesis profiles need no
annular hypothesis. -/

noncomputable section
open Filter MeasureTheory Set FourierTransform
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem frozenSlot_fourier_eq (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (s : Fin B) (i : Fin 3) (j : Fin N) (u : P.SlotItem hcard s j)
    (k : κ) (y xi : ℝ) :
    𝓕 ((P.frozenSlot hcard t b hb s).raw i j u k y) xi =
      b j u.1.1 k t • 𝓕 (P.raw i j u.1.1 u.1.2 k y) xi := by
  unfold frozenSlot
  rw [SourceLatticePacket.frozenProfile_raw, P.slotted_raw hcard,
    fourier_smul, smul_apply]

theorem physical_main_square_active_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j l u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_main_square_tail hVariation hlo hhi B q J hq hJ] with L htail
  intro N κ Label Item _ _ P hcard hP t a ha b hb v hv g hg hg1 hlow hhigh y u H hH hwidth
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hcardQ (j : Fin N) : (Q.labels j).card ≤ B :=
    (P.frozenActiveLabels_card_le t b j).trans (hcard j)
  have hlowQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hlow j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hhighQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hhigh j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  obtain ⟨hm,ht⟩ := htail N κ Label Item Q hcardQ hP t a ha c hc v hv g hg hg1
    hlowQ hhighQ y u H hH (fun j l i => hwidth j (P.frozenActiveOriginalLabel t b j l) i)
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_frozenActive t b a v g y x
  rw [heq]
  exact ⟨hm,ht⟩

theorem physical_centered_masked_variation_active_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
          𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
          𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, |t-(T j l u).slope| ≤ cone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_tail
    hVariation hlo hhi B q J A cone hq hJ hA hcone] with L htail
  intro N κ Label Item _ _ P hcard hP alt hAlt t a ha b hb v hv g hg hg1
    hlow hhigh hslow hshigh T hshort hangle y u H hH hwidth
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  let altQ := fun j (l : Q.labels j) => alt j (P.frozenActiveOriginalLabel t b j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.frozenActiveOriginalLabel t b j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.frozenActiveOriginalLabel t b j l)
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hcardQ (j : Fin N) : (Q.labels j).card ≤ B :=
    (P.frozenActiveLabels_card_le t b j).trans (hcard j)
  have hlowQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hlow j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hhighQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hhigh j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hslowQ (j : Fin N) (l : Q.labels j) (u : Item j l) (k : κ) (y xi : ℝ)
      (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0 := by
    rw [P.frozenActiveFamily_alt_raw t b alt hAlt]
    exact hslow j _ (P.frozenActiveLabel_nonzero t b j l) u k y xi hxi
  have hshighQ (j : Fin N) (l : Q.labels j) (u : Item j l) (k : κ) (y xi : ℝ)
      (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0 := by
    rw [P.frozenActiveFamily_alt_raw t b alt hAlt]
    exact hshigh j _ (P.frozenActiveLabel_nonzero t b j l) u k y xi hxi
  obtain ⟨hm,ht⟩ := htail N κ Label Item Q hcardQ hP altQ hAltQ t a ha c hc v hv g hg hg1
    hlowQ hhighQ hslowQ hshighQ TQ
    (fun j l u => hshort j (P.frozenActiveOriginalLabel t b j l) u)
    (fun j l u => hangle j (P.frozenActiveOriginalLabel t b j l) u)
    y u H hH (fun j l i => hwidth j (P.frozenActiveOriginalLabel t b j l) i)
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_frozenActive t b alt hAlt a v g T L A y x
  rw [heq]
  exact ⟨hm,ht⟩

theorem physical_narrow_main_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J F cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) →
    let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
    let c := fun j (l : Q.labels j) k s =>
      b j (P.referenceOriginalLabel t t R cone w j l) k s
    (∀ j, (Q.labels j).card ≤ B) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_main_square_active_tail hVariation hlo hhi B (q+1) J
    (by linarith) hJ, eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (F*cone+2)] with L htail hL hFC
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport
  dsimp only
  intro hcard hlow hhigh y u H hH hRH
  let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
  let c := fun j (l : Q.labels j) k s =>
    b j (P.referenceOriginalLabel t t R cone w j l) k s
  have hconst : Q.constant ≤ L^(q+1) := by
    rw [P.referenceSelf_constant t R cone w F hw hcone hF hwide hfrequency]
    calc
      P.absoluteConstant*(F*cone+2) ≤ L^q*L :=
        mul_le_mul hP hFC (by positivity) (Real.rpow_nonneg (by linarith) q)
      _ = L^(q+1) := by rw [Real.rpow_add (by linarith : 0 < L),Real.rpow_one]
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.referenceOriginalLabel t t R cone w j l) k
  have hwidth (j : Fin N) (l : Q.labels j) (_i : Item j l) : Q.length j ≤ H :=
    (P.referenceLabel_bounds t t R cone w j l).1.trans hRH
  have ht := htail N κ Label Item Q hcard hconst t a ha c hc v hv g hg hg1
    hlow hhigh y u H hH hwidth
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_narrow_reference t R cone w F hw hcone hF hwide hfrequency
      a b v g hshort hsupport y x
  rw [heq]
  simpa only [show 2*(q+1)+7 = 2*q+9 by ring] using ht

theorem physical_narrow_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A F cone maskCone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hmaskCone : 0 ≤ maskCone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) →
    let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
    let c := fun j (l : Q.labels j) k s =>
      b j (P.referenceOriginalLabel t t R cone w j l) k s
    let altQ := fun j (l : Q.labels j) => alt j (P.referenceOriginalLabel t t R cone w j l)
    let hAltQ := fun j (l : Q.labels j) => hAlt j (P.referenceOriginalLabel t t R cone w j l)
    (∀ j, (Q.labels j).card ≤ B) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val →
        𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j (l : Q.labels j) u, |t-(T j (P.referenceOriginalLabel t t R cone w j l) u).slope| ≤
        maskCone*(T j (P.referenceOriginalLabel t t R cone w j l) u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_active_tail
    hVariation hlo hhi B (q+1) J A maskCone (by linarith) hJ hA hmaskCone,
    eventually_ge_atTop (1:ℝ), eventually_ge_atTop (F*cone+2)] with L htail hL hFC
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport
  dsimp only
  intro hcard hlow hhigh hslow hshigh T hlength hangle y u H hH hRH
  let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
  let c := fun j (l : Q.labels j) k s =>
    b j (P.referenceOriginalLabel t t R cone w j l) k s
  let altQ := fun j (l : Q.labels j) => alt j (P.referenceOriginalLabel t t R cone w j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.referenceOriginalLabel t t R cone w j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.referenceOriginalLabel t t R cone w j l)
  have hconst : Q.constant ≤ L^(q+1) := by
    rw [P.referenceSelf_constant t R cone w F hw hcone hF hwide hfrequency]
    calc
      P.absoluteConstant*(F*cone+2) ≤ L^q*L :=
        mul_le_mul hP hFC (by positivity) (Real.rpow_nonneg (by linarith) q)
      _ = L^(q+1) := by rw [Real.rpow_add (by linarith : 0 < L),Real.rpow_one]
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.referenceOriginalLabel t t R cone w j l) k
  have hwidth (j : Fin N) (l : Q.labels j) (_i : Item j l) : Q.length j ≤ H :=
    (P.referenceLabel_bounds t t R cone w j l).1.trans hRH
  have ht := htail N κ Label Item Q hcard hconst altQ hAltQ t a ha c hc v hv g hg hg1
    hlow hhigh hslow hshigh TQ
    (fun j l i => hlength j (P.referenceOriginalLabel t t R cone w j l) i)
    hangle y u H hH hwidth
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_narrow_reference
      t R cone w F hw hcone hF hwide hfrequency alt hAlt a b v g T L A y x hshort hsupport
  rw [heq]
  simpa only [show 2*(q+1)+8 = 2*q+10 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveSpectrum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The active narrow reference annuli follow from the original
two-dimensional packet spectrum. The selector's lower angular separation
is used only on labels that occur in the frozen main sum. All three
covariant jets inherit these annuli, including alternate synthesis
profiles on the same physical geometry. -/

noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_fourier_cutoffs_at (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ)
    (hspectrum : ∀ xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : cb*w/P.length j ≤ |P.rowSlope j l| ∧
      |P.rowSlope j l| ≤ Cb*w/P.length j)
    (i : Fin 3) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 (P.raw i j l u k y) xi = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j l)| ∧
      |t-(t+P.rowSlope j l)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
    simpa only [heq,abs_neg] using hselector
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j l u k)
    y t (t+P.rowSlope j l) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb hspectrum hsel (P.frequency k) P.scale i
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← P.raw_eq_physical_slice i j l u k y t,heq,heq] at h
  exact h

variable (t R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel t t R cone w

theorem referenceSelf_active_raw_cutoffs (cStar cEta CEta cb Cb : ℝ)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j l, (∃ k, b j l k t ≠ 0) →
      cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : (Q).labels j) (hactive : ∃ k, b j (orig j l) k t ≠ 0)
    (u : Item j l) (k : κ) (i : Fin 3) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val →
      𝓕 ((Q).raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 ((Q).raw i j l u k y) xi = 0) := by
  have hs := P.referenceFamily_spectrum t t R cone w F hw hcone hF hwide hfrequency
    cStar cEta CEta hspectrum j l u k
  have hsel : cb*w/(Q).length j ≤ |(Q).rowSlope j l| ∧
      |(Q).rowSlope j l| ≤ Cb*w/(Q).length j := by
    simpa only [referenceFamily,sub_self,add_zero,length] using hselector j (orig j l) hactive
  exact (Q).raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
    j l u k hs hsel i y

theorem referenceSelf_active_alt_raw_cutoffs
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j l, (∃ k, b j l k t ≠ 0) →
      cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : (Q).labels j) (hactive : ∃ k, b j (orig j l) k t ≠ 0)
    (u : Item j l) (k : κ) (i : Fin 3) (y : ℝ) :
    let altQ := fun j (l : (Q).labels j) => alt j (orig j l)
    let hAltQ := fun j (l : (Q).labels j) => hAlt j (orig j l)
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val →
      𝓕 (((Q).withProfile altQ hAltQ).raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 (((Q).withProfile altQ hAltQ).raw i j l u k y) xi = 0) := by
  exact (P.withProfile alt hAlt).referenceSelf_active_raw_cutoffs
    t R cone w F hw hcone hF hwide hfrequency cStar cEta CEta cb Cb hcEta hcb hCb
    b hspectrum hselector j l hactive u k i y

theorem physical_narrow_main_square_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (q J F cStar cEta CEta cb Cb : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.referenceLabels t t R Cb w j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  have hlo : 0 < (cEta*cb-cStar)/(2*Real.pi) :=
    div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) Real.pi_pos)
  have hhi : 0 ≤ (CEta*Cb+cStar)/(2*Real.pi) :=
    div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  filter_upwards [physical_narrow_main_square_tail hVariation hlo hhi B q J F Cb hq hJ hF hCb]
    with L htail
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  have hsupport : ∀ j l k, b j l k t ≠ 0 →
      |t+P.rowSlope j l-t| ≤ Cb*w/P.length j := by
    intro j l k hk
    have heq : t+P.rowSlope j l-t = P.rowSlope j l := by ring
    rw [heq]
    exact (hselector j l ⟨k,hk⟩).2
  apply htail N κ Label Item P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport hcard
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).2 xi hxi
  · exact hH
  · exact hRH

theorem physical_narrow_centered_masked_variation_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (q J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.referenceLabels t t R Cb w j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j (l : P.referenceLabels t t R Cb w j) u,
        |t-(T j (P.referenceOriginalLabel t t R Cb w j l) u).slope| ≤
          maskCone*(T j (P.referenceOriginalLabel t t R Cb w j l) u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  have hlo : 0 < (cEta*cb-cStar)/(2*Real.pi) :=
    div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) Real.pi_pos)
  have hhi : 0 ≤ (CEta*Cb+cStar)/(2*Real.pi) :=
    div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  filter_upwards [physical_narrow_centered_masked_variation_tail hVariation hlo hhi
    B q J A F Cb maskCone hq hJ hA hF hCb hmaskCone] with L htail
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  have hsupport : ∀ j l k, b j l k t ≠ 0 →
      |t+P.rowSlope j l-t| ≤ Cb*w/P.length j := by
    intro j l k hk
    have heq : t+P.rowSlope j l-t = P.rowSlope j l := by ring
    rw [heq]
    exact (hselector j l ⟨k,hk⟩).2
  apply htail N κ Label Item P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport hcard
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).2 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_alt_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      alt hAlt cStar cEta CEta cb Cb hcEta hcb hCb b haltSpectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_alt_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      alt hAlt cStar cEta CEta cb Cb hcEta hcb hCb b haltSpectrum hselector j l hl u k 0 y).2 xi hxi
  · exact hlength
  · exact hangle
  · exact hH
  · exact hRH

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveCardTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only frozen-active labels need slots in the main reference tail.
Their cardinality follows from the original local slope multiplicity,
uniformly over the number of vector coordinates and inactive labels. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem frozenActive_referenceLabels_card_le (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) {B : ℕ}
    (hcard : ∀ j, (P.frozenActiveLabels t b j).card ≤ B)
    (oldSlope newSlope R cone w : ℝ) (j : Fin N) :
    ((P.frozenActiveFamily t b).referenceLabels oldSlope newSlope R cone w j).card ≤ B := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (hcard j)

theorem physical_active_narrow_main_square_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (q J F cStar cEta CEta cb Cb : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_narrow_main_square_spectral_tail hVariation B q J F
    cStar cEta CEta cb Cb hq hJ hF hcStar hcEta hCEta hcb hCb hgap] with L htail
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hs : ∀ j l u k xi eta, planarAngularFourier (Q.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact hspectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have ht := htail N κ Label Item Q hP t R w hw hwide hfrequency a ha c hc v hv g hg hg1
    (fun j l k hk => hshort j (P.frozenActiveOriginalLabel t b j l) k hk)
    (P.frozenActive_referenceLabels_card_le t b hcard t t R Cb w) hs
    (fun j l hl => hselector j (P.frozenActiveOriginalLabel t b j l) hl)
    y u H hH hRH
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_frozenActive t b a v g y x
  rw [heq]
  exact ht

theorem physical_active_narrow_centered_masked_variation_spectral_tail
    (hVariation : LepingleInput)
    (B : ℕ) (q J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, P.length j ≤ R → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_narrow_centered_masked_variation_spectral_tail hVariation B q J A F
    cStar cEta CEta cb Cb maskCone hq hJ hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap]
    with L htail
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  let altQ := fun j (l : Q.labels j) => alt j (P.frozenActiveOriginalLabel t b j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.frozenActiveOriginalLabel t b j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.frozenActiveOriginalLabel t b j l)
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hs : ∀ j l u k xi eta, planarAngularFourier (Q.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact hspectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have hsAlt : ∀ j l u k xi eta,
      planarAngularFourier ((Q.withProfile altQ hAltQ).physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact haltSpectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have hangleQ (j : Fin N) (l : Q.referenceLabels t t R Cb w j) (u : Item j l) :
      |t-(TQ j (Q.referenceOriginalLabel t t R Cb w j l) u).slope| ≤
        maskCone*(TQ j (Q.referenceOriginalLabel t t R Cb w j l) u).width/Q.length j := by
    have hbounds := Q.referenceLabel_bounds t t R Cb w j l
    let pl := P.frozenActiveOriginalLabel t b j (Q.referenceOriginalLabel t t R Cb w j l)
    have hslope : Q.rowSlope j (Q.referenceOriginalLabel t t R Cb w j l) =
        P.rowSlope j pl := rfl
    have hlen : Q.length j = P.length j := rfl
    rw [hslope,hlen] at hbounds
    have hr : |P.rowSlope j pl| ≤ Cb*w/P.length j := by
      simpa only [sub_self,add_zero] using hbounds.2
    exact hangle j pl u hbounds.1 hr
  have ht := htail N κ Label Item Q hP altQ hAltQ t R w hw hwide hfrequency a ha c hc v hv g hg hg1
    (fun j l k hk => hshort j (P.frozenActiveOriginalLabel t b j l) k hk)
    (P.frozenActive_referenceLabels_card_le t b hcard t t R Cb w) hs hsAlt
    (fun j l hl => hselector j (P.frozenActiveOriginalLabel t b j l) hl) TQ
    (fun j l u => hlength j (P.frozenActiveOriginalLabel t b j l) u) hangleQ y u H hH hRH
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_frozenActive t b alt hAlt a v g T L A y x
  rw [heq]
  exact ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedBand_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (x : ℝ) :
    P.physicalMaskedBand alt hAlt t b v g T L A y j x =
      P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x+
        P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x := by
  ext k
  simp only [physicalMaskedBand,physicalCenteredMaskedBand,physicalErrorMaskedBand,
    WithLp.ofLp_toLp,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1]
  simp only [PiLp.add_apply]
  ring

private theorem masked_packet_norm (horder : 6 ≤ P.order)
    (j : Fin N) (l : P.labels j) (u : Item j l)
    (c : EuclideanSpace ℂ κ) (x : ℝ) :
    ‖WithLp.toLp 2 (fun k => c k*((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ ≤
      P.absoluteConstant*(‖c‖*tileEnvelope
        (P.length j*(P.snappedSite j l u).1) (P.width*(P.snappedSite j l u).2)
        (P.length j) P.width 6 (x,y)) := by
  have heq : WithLp.toLp 2 (fun k => c k*((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)) =
      (T j l u).mask L A (x,y+t*x) •
        (P.withProfile alt hAlt).rawPacketValue 0 j l u c y x := by
    ext k
    have hw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
      ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j l u k y t)
    change (P.withProfile alt hAlt).raw 0 j l u k y x =
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x) at hw
    simp only [PiLp.smul_apply,rawPacketValue,Complex.real_smul]
    rw [hw]
    ring
  have hm0 : 0 ≤ (T j l u).mask L A (x,y+t*x) := topSincMask_nonneg _ _ _ _
  have hm1 : (T j l u).mask L A (x,y+t*x) ≤ 1 := topSincMask_le_one _ _ _ _
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hm0]
  exact (mul_le_of_le_one_left (norm_nonneg _) hm1).trans
    ((P.withProfile alt hAlt).raw_packet_value_norm horder 0 j l u c y x)

theorem physicalErrorMaskedBand_norm_le (horder : 6 ≤ P.order) (j : Fin N) (x : ℝ) :
    ‖P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x‖ ≤
      P.absoluteConstant*P.physicalErrorScale t a b v g j y x := by
  have heq : P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x =
      ∑ l : P.labels j, ∑ u : Item j l,
        WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)) := by
    ext k
    simp only [physicalErrorMaskedBand,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  rw [heq]
  calc
    _ ≤ ∑ l : P.labels j, ‖∑ u : Item j l,
        WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ := norm_sum_le _ _
    _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
        ‖WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
        P.absoluteConstant*(‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
          tileEnvelope (P.length j*(P.snappedSite j l u).1)
            (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun u _ =>
        P.masked_packet_norm alt hAlt t T L A y horder j l u _ x))
    _ = _ := by simp only [physicalErrorScale,Finset.mul_sum]

/-- The full original masked sequence has the narrow main variation
plus the single carrier-free positive angular-error sum. -/
theorem physicalMaskedVariation_le_main_add_error (horder : 6 ≤ P.order)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) :
    P.physicalMaskedVariation alt hAlt t b v g T L A y x ≤
      P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x+
        P.absoluteConstant*P.physicalAngularError t a b v g (x,y+t*x) := by
  have hp : packetPartialSum (fun j => P.physicalMaskedBand alt hAlt t b v g T L A y j x) =
      fun n => packetPartialSum (fun j => P.physicalCenteredMaskedBand
          alt hAlt t a b v g T L A y j x) n+
        packetPartialSum (fun j => P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x) n := by
    funext n
    unfold packetPartialSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact P.physicalMaskedBand_split alt hAlt t a b v g T L A y hb hb1 hv hg hg1 j x
    · simp
  unfold physicalMaskedVariation
  rw [hp]
  apply (cubicVariation_add_le _ _ _).trans
  apply add_le_add le_rfl
  apply (cubicVariation_packetPartialSum_le _).trans
  calc
    _ ≤ ∑ j, P.absoluteConstant*P.physicalErrorScale t a b v g j y x :=
      Finset.sum_le_sum (fun j _ => P.physicalErrorMaskedBand_norm_le
        alt hAlt t a b v g T L A y horder j x)
    _ = _ := by rw [← Finset.mul_sum,P.sum_physicalErrorScale]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

theorem physicalReferenceEvent_line_zero (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 0} =
      {x | L^e ≤ P.physicalAngularError t a b v g (x,y+t*x)} := by
  ext x
  simp only [physicalReferenceEvent,ite_true, if_true,Set.mem_ofPred_eq]

theorem physicalReferenceEvent_line_one (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 1} =
      {x | L^s ≤ P.physicalMainSquare t a b v g y x} := by
  ext x
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false, if_false,
    ite_true, if_true,Set.mem_ofPred_eq,physicalMainSquareOnPlane,hy]

theorem physicalReferenceEvent_line_two (y : ℝ) :
    {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 2} =
      {x | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} := by
  ext x
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false, if_false,Set.mem_ofPred_eq,hy]

/-- The three actual reference tails lose one unit of exponential rate.
There is no dependence on the number of packets or angular depth. -/
theorem eventually_physicalReferenceBad_tail (rate : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
      (A e s r y u W : ℝ), 0 < W →
      (volume.restrict (Ico u (u+W)))
        {x | L^e ≤ P.physicalAngularError t a b v g (x,y+t*x)} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^s ≤ P.physicalMainSquare t a b v g y x} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ≤
          ENNReal.ofReal (Real.exp (-(rate+1)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t a b v g T L A e s r} ≤
          ENNReal.ofReal (Real.exp (-rate*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_source_bad_event_tail 1 rate,eventually_ge_atTop (3:ℝ)]
    with L htail hL
  intro N κ Label Item _ _ P alt hAlt t a b v g T A e s r y u W _hW he hs hr
  let μ := volume.restrict (Ico u (u+W))
  have hlen : μ univ = ENNReal.ofReal W := by
    simp only [μ,Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  let event := fun i : Fin 3 => {x | (x,y+t*x) ∈
    P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i}
  have he' : μ (event 0) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 0} ≤ _
    rw [P.physicalReferenceEvent_line_zero alt hAlt t a b v g T L A e s r y]
    exact he
  have hs' : μ (event 1) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 1} ≤ _
    rw [P.physicalReferenceEvent_line_one alt hAlt t a b v g T L A e s r y]
    exact hs
  have hr' : μ (event 2) ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L))*μ univ := by
    rw [hlen]
    change μ {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r 2} ≤ _
    rw [P.physicalReferenceEvent_line_two alt hAlt t a b v g T L A e s r y]
    exact hr
  have ht := htail (Fin 3) ℝ μ Finset.univ event
    (by simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,Real.rpow_one] using hL) (by
      intro i _
      fin_cases i
      · exact he'
      · exact hs'
      · exact hr')
  have hset : {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t a b v g T L A e s r} =
      ⋃ i ∈ (Finset.univ : Finset (Fin 3)),
        {x | (x,y+t*x) ∈ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i} := by
    ext x
    simp only [physicalReferenceBad,mem_ofPred_eq,mem_iUnion,Finset.mem_univ,exists_prop,true_and]
  rwa [← hset,hlen] at ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual narrow main-variation tail with the positive
angular-error tail costs a single extra polynomial power. The cutoff
exponent is fixed independently of the mass stopping threshold. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem variation_two_term_bad_subset {X : Type*} (F U E : X → ℝ)
    {L A a r s : ℝ} (hL : 2 ≤ L) (_hA : 0 ≤ A) (hAb : A ≤ L^a)
    (hF : ∀ x, |F x| ≤ |U x|+A*|E x|) :
    {x | L^(max r (a+s)+1) ≤ |F x|} ⊆
      {x | L^r ≤ |U x|} ∪ {x | L^s ≤ |E x|} := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  intro x hx
  by_contra hn
  have hU : |U x| < L^r := by
    by_contra h
    exact hn (Or.inl (not_lt.mp h))
  have hE : |E x| < L^s := by
    by_contra h
    exact hn (Or.inr (not_lt.mp h))
  have hAE : A*|E x| ≤ L^(a+s) := by
    calc
      _ ≤ L^a*L^s := mul_le_mul hAb hE.le (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
      _ = _ := (Real.rpow_add hL0 _ _).symm
  have hsmall : |F x| < L^r+L^(a+s) :=
    (hF x).trans_lt (add_lt_add_of_lt_of_le hU hAE)
  have hbig : L^r+L^(a+s) ≤ L^(max r (a+s)+1) := by
    calc
      _ ≤ L^(max r (a+s))+L^(max r (a+s)) := add_le_add
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
      _ = 2*L^(max r (a+s)) := by ring
      _ ≤ L*L^(max r (a+s)) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  exact (not_le_of_gt (hsmall.trans_le hbig)) hx

theorem eventually_variation_two_term_tail (a r s J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
      (F U E : X → ℝ) (A : ℝ) (mass : ℝ≥0∞),
      0 ≤ A → A ≤ L^a → (∀ x, |F x| ≤ |U x|+A*|E x|) →
      μ {x | L^r ≤ |U x|} ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*mass →
      μ {x | L^s ≤ |E x|} ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*mass →
      μ {x | L^(max r (a+s)+1) ≤ |F x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*mass := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    eventually_source_polynomial_exp 2 0 J (by norm_num)] with L hL hdecay
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro X _ μ F U E A mass hA hAb hF hU hE
  apply (measure_mono (variation_two_term_bad_subset F U E hL hA hAb hF)).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add hU hE).trans
  calc
    _ = ENNReal.ofReal (2*Real.exp (-(J+1)*L))*mass := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

namespace SourceLabeledLattice

/-- The two separate tails control the full original masked synthesis,
using the previously proved exact main/error decomposition. -/
theorem eventually_physical_full_variation_tail (a q p J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^a →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t c : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
      (maskExponent y u H : ℝ),
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation
          alt hAlt t c b v g T L maskExponent y x|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(p+7) ≤ |P.physicalAngularError t c b v g (x,y+t*x)|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(max (2*q+8) (a+p+7)+1) ≤ |P.physicalMaskedVariation
          alt hAlt t b v g T L maskExponent y x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [eventually_variation_two_term_tail a (2*q+8) (p+7) J] with L hL
  intro N κ Label Item _ _ P horder hP alt hAlt t c b hb hb1 v hv g hg hg1 T
    maskExponent y u H hmain herror
  have hbound (x : ℝ) : |P.physicalMaskedVariation alt hAlt t b v g T L maskExponent y x| ≤
      |P.physicalCenteredMaskedVariation alt hAlt t c b v g T L maskExponent y x|+
        P.absoluteConstant*|P.physicalAngularError t c b v g (x,y+t*x)| := by
    rw [abs_of_nonneg (show 0 ≤ P.physicalMaskedVariation
      alt hAlt t b v g T L maskExponent y x from cubicVariation_nonneg _ _),
      abs_of_nonneg (show 0 ≤ P.physicalCenteredMaskedVariation
        alt hAlt t c b v g T L maskExponent y x from cubicVariation_nonneg _ _)]
    apply (P.physicalMaskedVariation_le_main_add_error
      alt hAlt t c b v g T L maskExponent y horder hb hb1 hv hg hg1 x).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) P.absoluteConstant_pos.le)
  have h := hL ℝ (volume.restrict (Ico u (u+H))) _ _ _ P.absoluteConstant
    (ENNReal.ofReal H) P.absoluteConstant_pos.le hP hbound hmain herror
  simpa only [show a+(p+7) = a+p+7 by ring] using h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the original error, narrow main square and narrow centered
variation tails into the physical bad-reference event. Polynomial powers
and exponential losses are fixed before the family is selected. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalAngularError_nonneg (P : SourceLabeledLattice N κ Label Item)
    (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    0 ≤ P.physicalAngularError t a b v g z := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro l _
  exact Finset.sum_nonneg (fun u _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _))

/-- The actual three-reference event has a uniform tail, provided the
three already proved component tails are supplied two rates stronger. -/
theorem eventually_physical_reference_good_tail (a q p J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^a →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t c : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A y u W : ℝ), 0 < W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t c b v g T L A y x|} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
          (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_physicalReferenceBad_tail J,
    eventually_physical_full_variation_tail a (q+1) p (J+1),
    eventually_ge_atTop (0:ℝ)] with L hbad hfull hL
  intro N κ Label Item _ _ P horder hP alt hAlt t c b hb hb1 v hv g hg hg1 T
    A y u W hW hE hS hV
  have hweaken : ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W ≤
      ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal W := by
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEabs : (volume.restrict (Ico u (u+W)))
      {x | L^(p+7) ≤ |P.physicalAngularError t c b v g (x,y+t*x)|} ≤
        ENNReal.ofReal (Real.exp (-((J+1)+1)*L))*ENNReal.ofReal W := by
    simpa only [abs_of_nonneg (P.physicalAngularError_nonneg t c b v g _),
      show J+1+1 = J+2 by ring] using hE
  have hfull' := hfull N κ Label Item P horder hP alt hAlt t c b hb hb1 v hv g hg hg1
    T A y u W (by simpa only [show 2*(q+1)+8 = 2*q+10 by ring,
      show J+1+1 = J+2 by ring] using hV) hEabs
  have hV' : (volume.restrict (Ico u (u+W)))
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal W := by
    apply (measure_mono (show
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ⊆
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ |P.physicalMaskedVariation alt hAlt t b v g T L A y x|}
      from by
        intro x hx
        change L^(max (2*q+10) (a+p+7)+1) ≤
          P.physicalMaskedVariation alt hAlt t b v g T L A y x at hx
        change L^(max (2*q+10) (a+p+7)+1) ≤
          |P.physicalMaskedVariation alt hAlt t b v g T L A y x|
        exact hx.trans (le_abs_self _))).trans
    simpa only [show 2*(q+1)+8 = 2*q+10 by ring] using hfull'
  exact hbad N κ Label Item P alt hAlt t c b v g T A (p+7) (2*q+9)
    (max (2*q+10) (a+p+7)+1) y u W hW (hE.trans hweaken) (hS.trans hweaken) hV'

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSpectralGoodTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original packet spectra and the fixed active-label count discharge
the main-square and masked-variation tails in the physical reference
event. The only remaining component premise is the independently
constructed positive angular-error tail. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_physical_reference_good_spectral_tail_oai (hVariation : LepingleInput)
    (B : ℕ) (a q p J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order →
      P.absoluteConstant ≤ L^a → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (c : ℝ), 0 ≤ c →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, P.length j ≤ R → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
          (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_active_narrow_main_square_spectral_tail hVariation B q (J+2) F
      cStar cEta CEta cb Cb hq (by linarith) hF hcStar hcEta hCEta hcb hCb hgap,
    physical_active_narrow_centered_masked_variation_spectral_tail hVariation B q (J+2) A F
      cStar cEta CEta cb Cb maskCone hq (by linarith) hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap,
    eventually_physical_reference_good_tail a q p J] with L hS hV hgood
  intro N κ Label Item _ _ P horder hPa hPq alt hAlt t R w hw hwide hfrequency c hc
    b hb hb1 v hv g hg hg1 hshort hcard hspectrum haltSpectrum hselector T hlength hangle
    y u H hH hRH hE
  have hbFrozen : ∀ j l k, ‖b j l k t‖ ≤ 1 := fun j l k => hb1 j l k t
  have hs := hS N κ Label Item P hPq t R w hw hwide hfrequency c hc b hbFrozen v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  have hvary := hV N κ Label Item P hPq alt hAlt t R w hw hwide hfrequency c hc b hbFrozen
    v hv g hg hg1 hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  have hs' : (volume.restrict (Ico u (u+H)))
      {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ≤
      ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H := by
    apply (measure_mono (show
      {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ⊆
      {x | L^(2*q+9) ≤ |P.physicalMainSquare t c b v g y x|} from ?_)).trans hs.2
    intro x hx
    change L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x at hx
    exact hx.trans (le_abs_self _)
  exact hgood N κ Label Item P horder hPa alt hAlt t c b hb hb1 v hv g hg hg1 T A y u H hH
    hE hs' hvary.2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail_oai := @OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail_oai
