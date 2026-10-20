-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:03:54.14544+00:00
-- url     : https://prove2.me/submissions/9cb7cab3-31e8-4c7d-8839-1b53518d520a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/PairingEstimates.lean:L69-L92
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_abs_prod_sub_prod_le

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothCalculus ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

namespace Smooth

theorem norm_grad (f : Smooth H) (p : H) : ‖grad p f‖ = ‖fderiv ℝ (f : H → ℝ) p‖ :=
  (InnerProductSpace.toDual ℝ H).symm.norm_map _

theorem grad_contDiff (f : Smooth H) : ContDiff ℝ ∞ (fun p => grad p f) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (f.contDiff.fderiv_right (by simp))

theorem grad_continuous (f : Smooth H) : Continuous (fun p => grad p f) :=
  f.grad_contDiff.continuous

theorem grad_norm_le {C : ℝ≥0} (f : Smooth H) (h : LipschitzWith C (f : H → ℝ)) (p : H) :
    ‖grad p f‖ ≤ C := by
  rw [norm_grad]
  exact norm_fderiv_le_of_lipschitz ℝ h

end Smooth

theorem edge_continuous {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) : Continuous (edge p q) := by
  unfold edge
  fun_prop

theorem edge_mem {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : Set H} (hK : Convex ℝ K) {p q : H} (hp : p ∈ K) (hq : q ∈ K)
    {t : ℝ} (ht : t ∈ Icc 0 1) : edge p q t ∈ K := by
  have he : edge p q t = (1-t) • q+t • p := by simp [edge,sub_smul,smul_sub]; module
  rw [he]
  exact hK hq hp (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem edge_hasDerivAt {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) (t : ℝ) : HasDerivAt (edge p q) (p-q) t := by
  unfold edge
  simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (p-q)).const_add q

theorem smooth_edge_integral (f : Smooth H) (p q : H) :
    (∫ t in (0:ℝ)..1, fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) = f.val p-f.val q := by
  have hint : IntervalIntegrable (fun t => fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) volume 0 1 :=
    ((f.contDiff.continuous_fderiv (by simp)).comp (edge_continuous p q)).clm_apply continuous_const
      |>.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) 1) => (f.differentiable _).hasFDerivAt.comp_hasDerivAt t (edge_hasDerivAt p q t)) hint
  simpa [edge] using h

open FreeSpace

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.EnergyEstimates ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem grad_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm).intervalIntegrable _ _

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothMultiplier ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem damping_nonneg {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) : 0 ≤ damping s z x := by
  apply Finset.prod_nonneg
  intro i hi
  have h := (z i).grad_norm_le (hz i hi) x
  norm_num only [NNReal.coe_one] at h
  linarith

theorem damping_le_one {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) : damping s z x ≤ 1 := by
  have hn (i : ι) (hi : i ∈ s) : 0 ≤ 1-‖Smooth.grad x (z i)‖ := by
    have h := (z i).grad_norm_le (hz i hi) x
    norm_num only [NNReal.coe_one] at h
    linarith
  have hp : (∏ i ∈ s, (1-‖Smooth.grad x (z i)‖)) ≤ ∏ _i ∈ s, (1:ℝ) :=
    Finset.prod_le_prod₀ hn (fun i _ => sub_le_self _ (norm_nonneg _))
  simpa only [damping,Finset.prod_const_one] using hp

theorem one_sub_damping_le {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) :
    1-damping s z x ≤ ∑ i ∈ s, ‖Smooth.grad x (z i)‖ := by
  have h := abs_prod_sub_prod_le s (fun _ => (1:ℝ)) (fun i => 1-‖Smooth.grad x (z i)‖)
    (fun _ _ => by norm_num) (fun i hi => by
      have h := (z i).grad_norm_le (hz i hi) x
      norm_num only [NNReal.coe_one] at h
      rw [abs_le]; constructor <;> linarith [norm_nonneg (Smooth.grad x (z i))])
  simp only [Finset.prod_const_one,sub_sub_cancel,abs_norm] at h
  exact (le_abs_self _).trans h

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.PairingEstimates ----
namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem smoothPair_le_majorant (a : MolecularData H) (f : Smooth H)
    {Q : Set H} (hQ : Convex ℝ Q) (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q)
    (b : H → ℝ) (hb : Continuous b) (hbound : ∀ x ∈ Q, ‖Smooth.grad x f‖ ≤ b x) :
    |smoothPair a f| ≤ ∑ i, (|a.coeff i| * dist (a.p i) (a.q i))*
      ∫ t in (0:ℝ)..1, b (edge (a.p i) (a.q i) t) := by
  have he (p q : H) (hp : p ∈ Q) (hq : q ∈ Q) :
      |f.val p-f.val q| ≤ dist p q * ∫ t in (0:ℝ)..1, b (edge p q t) := by
    rw [← smooth_edge_integral f p q]
    have hi : IntervalIntegrable (fun t => fderiv ℝ f.val (edge p q t) (p-q)) volume 0 1 :=
      (((f.contDiff.continuous_fderiv (by simp)).comp (edge_continuous p q)).clm_apply continuous_const).intervalIntegrable _ _
    calc
      _ ≤ ∫ t in (0:ℝ)..1, |fderiv ℝ f.val (edge p q t) (p-q)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, dist p q * b (edge p q t) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi.abs
          ((continuous_const.mul (hb.comp (edge_continuous p q))).intervalIntegrable _ _)
        intro t ht
        calc
          _ = ‖fderiv ℝ f.val (edge p q t) (p-q)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ f.val (edge p q t)‖ * ‖p-q‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ b (edge p q t)*‖p-q‖ := mul_le_mul_of_nonneg_right
            (by rw [← Smooth.norm_grad]; exact hbound _ (edge_mem hQ hp hq ht)) (norm_nonneg _)
          _ = _ := by simp only [Pi.mul_apply,Function.comp_apply,dist_eq_norm]; ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  calc
    |smoothPair a f| = |∑ i, a.coeff i*(f.val (a.p i)-f.val (a.q i))| := rfl
    _ ≤ ∑ i, |a.coeff i*(f.val (a.p i)-f.val (a.q i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (he _ _ (ha i).1 (ha i).2) (abs_nonneg _)

theorem smoothPair_le_masses {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (a : MolecularData H) (f : Smooth H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (hbound : ∀ x ∈ Q, ‖Smooth.grad x f‖ ≤ (∑ i ∈ s, ‖Smooth.grad x (z i)‖)+ε) :
    |smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by
  classical
  have hb : Continuous (fun x => (∑ i ∈ s, ‖Smooth.grad x (z i)‖)+ε) :=
    (continuous_finsetSum s (fun i _ => (z i).grad_continuous.norm)).add continuous_const
  refine (smoothPair_le_majorant a f hQ ha _ hb hbound).trans_eq ?_
  have he (p q : H) : (∫ t in (0:ℝ)..1, (∑ i ∈ s, ‖Smooth.grad (edge p q t) (z i)‖)+ε) =
      (∑ i ∈ s, ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) (z i)‖)+ε := by
    have hsum : IntervalIntegrable (fun t => ∑ i ∈ s, ‖Smooth.grad (edge p q t) (z i)‖) volume 0 1 := by
      exact (continuous_finsetSum s (fun i _ => ((z i).grad_continuous.comp (edge_continuous p q)).norm)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hsum intervalIntegrable_const,
      intervalIntegral.integral_finsetSum (fun i _ => grad_integrable (z i) p q)]
    simp
  simp only [he,mul_add,Finset.sum_add_distrib,Finset.mul_sum,gradMass,MolecularData.cost]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem correction_pairing_bound {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (f w : Smooth H)
    (hf : LipschitzWith 1 f.val) (a : MolecularData H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (herr : ∀ x ∈ Q, ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖ ≤ ε) :
    |smoothPair a w-smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by
  rw [← map_sub]
  apply smoothPair_le_masses s z a (w-f) hQ ha ε
  intro x hx
  have hf' : ‖Smooth.grad x f‖ ≤ 1 := by simpa using f.grad_norm_le hf x
  have hd0 := damping_nonneg s z hz x
  have hd1 := damping_le_one s z hz x
  have he : Smooth.grad x (w-f) = (Smooth.grad x w-damping s z x • Smooth.grad x f)+
      (damping s z x-1) • Smooth.grad x f := by rw [map_sub]; module
  rw [he]
  calc
    _ ≤ ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖+
        ‖(damping s z x-1) • Smooth.grad x f‖ := norm_add_le _ _
    _ ≤ ε+(1-damping s z x) := by
      apply add_le_add (herr x hx)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hd1)]
      have hmul := mul_le_mul_of_nonneg_left hf' (sub_nonneg.mpr hd1)
      nlinarith
    _ ≤ _ := by linarith [one_sub_damping_le s z hz x]

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace


theorem solution.{uH,uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound.{uH,uIndex} := @_root_.OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound.{uH,uIndex}
