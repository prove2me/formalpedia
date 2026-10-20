-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:25:44.1726+00:00
-- url     : https://prove2.me/submissions/c2d9b7fd-b1be-4333-8675-6c856d37f4eb

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH uIndex
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem h50c_grad_norm (f : Smooth H) (x : H) : ‖Smooth.grad x f‖ = ‖fderiv ℝ (f : H → ℝ) x‖ := by
  change ‖(InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (f : H → ℝ) x)‖ = _
  exact LinearIsometryEquiv.norm_map _ _

theorem h50c_grad_le_one (f : Smooth H) (hf : LipschitzWith 1 (f : H → ℝ)) (x : H) :
    ‖Smooth.grad x f‖ ≤ 1 := by
  rw [h50c_grad_norm]
  simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hf

theorem h50c_grad_cont (f : Smooth H) (p q : H) :
    Continuous (fun t : ℝ => Smooth.grad (edge p q t) f) := by
  change Continuous (fun t : ℝ => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (f : H → ℝ) (edge p q t)))
  have he : Continuous (fun t : ℝ => edge p q t) := by
    unfold edge; exact continuous_const.add (continuous_id.smul continuous_const)
  exact (InnerProductSpace.toDual ℝ H).symm.continuous.comp
    ((f.contDiff.continuous_fderiv (by simp)).comp he)

theorem h50c_edge_hasDeriv (p q : H) (t : ℝ) : HasDerivAt (fun s : ℝ => edge p q s) (p - q) t := by
  unfold edge
  simpa using ((hasDerivAt_id t).smul_const (p - q)).const_add q

theorem h50c_ftc (h : Smooth H) (p q : H) :
    h.val p - h.val q = ∫ t in (0:ℝ)..1, inner ℝ (Smooth.grad (edge p q t) h) (p - q) := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s => h.val (edge p q s))
      (inner ℝ (Smooth.grad (edge p q t) h) (p - q)) t := by
    intro t _
    have h1 := ((h.differentiable (edge p q t)).hasFDerivAt).comp_hasDerivAt t (h50c_edge_hasDeriv p q t)
    have key : inner ℝ (Smooth.grad (edge p q t) h) (p - q) = fderiv ℝ (h : H → ℝ) (edge p q t) (p - q) :=
      InnerProductSpace.toDual_symm_apply
    rw [key]; exact h1
  have hc : Continuous (fun t => inner ℝ (Smooth.grad (edge p q t) h) (p - q)) :=
    (h50c_grad_cont h p q).inner continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)]
  simp [edge]

theorem h50c_diff_le (h : Smooth H) (p q : H) :
    |h.val p - h.val q| ≤ dist p q * ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) h‖ := by
  rw [h50c_ftc]
  have hc : Continuous (fun t => inner ℝ (Smooth.grad (edge p q t) h) (p - q)) :=
    (h50c_grad_cont h p q).inner continuous_const
  have hc2 : Continuous (fun t => ‖Smooth.grad (edge p q t) h‖ * dist p q) :=
    (h50c_grad_cont h p q).norm.mul continuous_const
  calc _ ≤ ∫ t in (0:ℝ)..1, |inner ℝ (Smooth.grad (edge p q t) h) (p - q)| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) h‖ * dist p q :=
        intervalIntegral.integral_mono_on zero_le_one (hc.abs.intervalIntegrable 0 1)
          (hc2.intervalIntegrable 0 1) (fun t _ => by
            rw [dist_eq_norm]; exact abs_real_inner_le_norm _ _)
    _ = _ := by rw [intervalIntegral.integral_mul_const, mul_comm]


theorem h50c_aps {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i)-(∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i-b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have haj := ha j (Finset.mem_insert_self _ _)
    have hbj := hb j (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hpb : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    calc _ ≤ |a j * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| := abs_add_le _ _
      _ = |a j| * |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i ∈ s, |a i - b i|) + |a j - b j| * 1 := by
          gcongr
      _ = _ := by ring

theorem solution {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (f w : Smooth H)
    (hf : LipschitzWith 1 f.val) (a : MolecularData H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (herr : ∀ x ∈ Q, ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖ ≤ ε) :
    |smoothPair a w-smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by
  classical
  have hdamp : ∀ x, |damping s z x - 1| ≤ ∑ j ∈ s, ‖Smooth.grad x (z j)‖ := by
    intro x
    have := h50c_aps s (fun j => 1 - ‖Smooth.grad x (z j)‖) (fun _ => 1)
      (fun j hj => by
        have h1 := h50c_grad_le_one (z j) (hz j hj) x
        rw [abs_le]; constructor <;> linarith [norm_nonneg (Smooth.grad x (z j))])
      (fun j _ => by simp)
    simpa [damping] using this
  have hpt : ∀ x ∈ Q, ‖Smooth.grad x (w - f)‖ ≤ (∑ j ∈ s, ‖Smooth.grad x (z j)‖) + ε := by
    intro x hx
    have e : Smooth.grad x (w - f) = (Smooth.grad x w - damping s z x • Smooth.grad x f) +
        (damping s z x - 1) • Smooth.grad x f := by
      rw [map_sub, sub_smul, one_smul]; abel
    rw [e]
    calc _ ≤ ‖Smooth.grad x w - damping s z x • Smooth.grad x f‖ + ‖(damping s z x - 1) • Smooth.grad x f‖ :=
          norm_add_le _ _
      _ ≤ ε + (∑ j ∈ s, ‖Smooth.grad x (z j)‖) * 1 := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add (herr x hx) (mul_le_mul (hdamp x) (h50c_grad_le_one f hf x) (norm_nonneg _)
            (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
      _ = _ := by ring
  have hpair : smoothPair a w - smoothPair a f = ∑ i, a.coeff i * ((w - f).val (a.p i) - (w - f).val (a.q i)) := by
    rw [← map_sub]; rfl
  rw [hpair]
  have hterm : ∀ i, |a.coeff i * ((w - f).val (a.p i) - (w - f).val (a.q i))| ≤
      (∑ j ∈ s, (|a.coeff i| * dist (a.p i) (a.q i)) * ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖)
        + ε * (|a.coeff i| * dist (a.p i) (a.q i)) := by
    intro i
    set e := fun t => edge (a.p i) (a.q i) t
    have hcj : ∀ j, Continuous (fun t => ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖) :=
      fun j => (h50c_grad_cont (z j) _ _).norm
    have hsumc : Continuous (fun t => (∑ j ∈ s, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖) + ε) :=
      (continuous_finset_sum _ (fun j _ => hcj j)).add continuous_const
    have hI : ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (w - f)‖ ≤
        (∑ j ∈ s, ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖) + ε := by
      have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
        ((h50c_grad_cont (w - f) _ _).norm.intervalIntegrable 0 1) (hsumc.intervalIntegrable 0 1)
        (fun t ht => hpt _ (by
          unfold edge
          exact hQ.add_smul_sub_mem (ha i).2 (ha i).1 ht))
      have hs0 : Continuous (fun t => ∑ j ∈ s, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖) :=
        continuous_finset_sum _ (fun j _ => hcj j)
      rw [intervalIntegral.integral_add (hs0.intervalIntegrable 0 1)
        (intervalIntegrable_const (μ := MeasureTheory.volume)),
        intervalIntegral.integral_finset_sum (fun j _ => (hcj j).intervalIntegrable 0 1)] at hm
      simpa using hm
    have hd := h50c_diff_le (w - f) (a.p i) (a.q i)
    have hw0 : 0 ≤ |a.coeff i| * dist (a.p i) (a.q i) := by positivity
    rw [abs_mul]
    calc |a.coeff i| * |(w - f).val (a.p i) - (w - f).val (a.q i)|
        ≤ |a.coeff i| * (dist (a.p i) (a.q i) * ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (w - f)‖) :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = (|a.coeff i| * dist (a.p i) (a.q i)) * ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (w - f)‖ := by ring
      _ ≤ (|a.coeff i| * dist (a.p i) (a.q i)) * ((∑ j ∈ s, ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖) + ε) :=
          mul_le_mul_of_nonneg_left hI hw0
      _ = _ := by rw [mul_add, Finset.mul_sum, mul_comm ε]
  calc _ ≤ ∑ i, |a.coeff i * ((w - f).val (a.p i) - (w - f).val (a.q i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((∑ j ∈ s, (|a.coeff i| * dist (a.p i) (a.q i)) * ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) (z j)‖)
        + ε * (|a.coeff i| * dist (a.p i) (a.q i))) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
        simp only [gradMass, MolecularData.cost]

