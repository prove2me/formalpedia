-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_wuc_functions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:14:46.737959+00:00
-- url     : https://prove2.me/submissions/4340cfe1-e880-4417-aa33-621baa0469b0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WUCFunctions.lean:L89-L132
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_wuc_functions. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCFunctions
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_correction_pairing_bound
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_detecting_sequence

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

theorem grad_norm_le {C : ℝ≥0} (f : Smooth H) (h : LipschitzWith C (f : H → ℝ)) (p : H) :
    ‖grad p f‖ ≤ C := by
  rw [norm_grad]
  exact norm_fderiv_le_of_lipschitz ℝ h

end Smooth

open FreeSpace

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothMultiplier ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
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

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.WUCFunctions ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem halfWeight_pos (j : ℕ) : 0 < halfWeight j := by unfold halfWeight; positivity

theorem sum_halfWeight (n : ℕ) : ∑ j ∈ Finset.range n, halfWeight j = 1-(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [halfWeight,pow_succ]; ring

theorem sum_halfWeight_le (n : ℕ) : (∑ j ∈ Finset.range n, halfWeight j) ≤ 1 := by
  rw [sum_halfWeight]
  linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem halfWeight_le_one (j : ℕ) : halfWeight j ≤ 1 := by
  unfold halfWeight
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem damping_telescope (z : ℕ → Smooth H) (n : ℕ) (x : H) :
    (∑ j ∈ Finset.range n, damping (Finset.range j) z x * ‖Smooth.grad x (z j)‖) =
      1-damping (Finset.range n) z x := by
  induction n with
  | zero => simp [damping]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hd : damping (Finset.range (n+1)) z x = damping (Finset.range n) z x *
        (1-‖Smooth.grad x (z n)‖) := Finset.prod_range_succ _ n
    rw [hd]
    ring

theorem sum_grad_norm_le {Q : Set H} (z w : ℕ → Smooth H) (ε : ℕ → ℝ)
    (hz : ∀ i, LipschitzWith 1 (z i).val)
    (hεsum : ∀ n, (∑ i ∈ Finset.range n, ε i) ≤ 1)
    (herr : ∀ i x, x ∈ Q →
      ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i)
    (n : ℕ) {x : H} (hx : x ∈ Q) : (∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖) ≤ 2 := by
  have h (i : ℕ) : ‖Smooth.grad x (w i)‖ ≤
      damping (Finset.range i) z x * ‖Smooth.grad x (z i)‖+ε i := by
    have hd := damping_nonneg (Finset.range i) z (fun j _ => hz j) x
    calc
      _ ≤ ‖damping (Finset.range i) z x • Smooth.grad x (z i)‖+
          ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ := norm_le_insert' _ _
      _ ≤ _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]; exact add_le_add le_rfl (herr i x hx)
  calc
    _ ≤ ∑ i ∈ Finset.range n, (damping (Finset.range i) z x * ‖Smooth.grad x (z i)‖+ε i) :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = 1-damping (Finset.range n) z x+∑ i ∈ Finset.range n, ε i := by
      rw [Finset.sum_add_distrib,damping_telescope]
    _ ≤ 2 := by linarith [damping_nonneg (Finset.range n) z (fun j _ => hz j) x,hεsum n]

theorem signed_sum_lipschitz {Q : Set H} (hQ : Convex ℝ Q) (w : ℕ → Smooth H)
    (hgrad : ∀ n x, x ∈ Q → (∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖) ≤ 2)
    (n : ℕ) (c : ℕ → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    LipschitzOnWith 2 (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) Q := by
  let f : Smooth H := ∑ i ∈ Finset.range n, c i • w i
  have hef (x : H) : f.val x = ∑ i ∈ Finset.range n, c i*(w i).val x := by
    change Smooth.eval x f = _
    simp only [f,map_sum,map_smul,smul_eq_mul,Smooth.eval,LinearMap.coe_mk,AddHom.coe_mk]
  have hfn : LipschitzOnWith 2 f.val Q := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => f.differentiable x) _ hQ
    intro x hx
    rw [← NNReal.coe_le_coe]
    change ‖fderiv ℝ f.val x‖ ≤ (2:ℝ)
    rw [← Smooth.norm_grad]
    calc
      _ = ‖∑ i ∈ Finset.range n, c i • Smooth.grad x (w i)‖ := by simp only [f,map_sum,map_smul]
      _ ≤ ∑ i ∈ Finset.range n, ‖c i • Smooth.grad x (w i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, ‖Smooth.grad x (w i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc i)
      _ ≤ 2 := hgrad n x hx
  have he : f.val = (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) := funext hef
  rw [he] at hfn
  exact hfn

theorem exists_wuc_functions {K Q : Set H} (hQ : IsCompact Q) (hQc : Convex ℝ Q)
    (hKQ : K ⊆ Q) {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) :
    ∃ (w : ℕ → Smooth H) (a : ℕ → RowItem K C ρ μ),
      (∀ i, (w i).val 0 = 0) ∧
      (∀ i, α/2 ≤ smoothPair (a i).a (w i)) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) →
        LipschitzOnWith 2 (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) Q := by
  classical
  let β := min 1 (α/(8*(C+1)))
  have hβ : 0 < β := lt_min (by norm_num) (div_pos hα (by positivity))
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβC : β*C ≤ α/8 := by
    have hm : β*(8*(C+1)) ≤ α := (le_div_iff₀ (by positivity)).mp (min_le_right (1:ℝ) _)
    nlinarith
  let ε := fun i => β*halfWeight i
  let η := fun i => (α/8)*halfWeight i
  have hε (i) : 0 < ε i := mul_pos hβ (halfWeight_pos i)
  have hη (i) : 0 < η i := mul_pos (by positivity) (halfWeight_pos i)
  have hεsum (n) : (∑ i ∈ Finset.range n, ε i) ≤ 1 := by
    change (∑ i ∈ Finset.range n, β*halfWeight i) ≤ 1
    rw [← Finset.mul_sum]
    exact (mul_le_of_le_one_right hβ.le (sum_halfWeight_le n)).trans hβ1
  have hηsum (n) : (∑ i ∈ Finset.range n, η i) ≤ α/8 := by
    change (∑ i ∈ Finset.range n, (α/8)*halfWeight i) ≤ α/8
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right (by positivity) (sum_halfWeight_le n)
  have hεC (i) : ε i*C ≤ α/8 := by
    have hi : ε i ≤ β := mul_le_of_le_one_right hβ.le (halfWeight_le_one i)
    exact (mul_le_mul_of_nonneg_right hi hC).trans hβC
  obtain ⟨z,w,a,hz,hzero,hhigh,hmass,herr⟩ := exists_detecting_sequence hQ hC hα hRich ε η hε hη
  refine ⟨w,a,fun i => (hzero i).2,?_,?_⟩
  · intro i
    have hpair := correction_pairing_bound (Finset.range i) z (fun j _ => hz j) (z i) (w i)
      (hz i) (a i).a hQc (fun j => ⟨hKQ ((a i).support j).1,hKQ ((a i).support j).2⟩)
      (ε i) (herr i)
    have hm : (∑ j ∈ Finset.range i, gradMass (a i).a (z j)) ≤ α/8 :=
      (Finset.sum_le_sum (fun j hj => hmass i j (Finset.mem_range.mp hj))).trans (hηsum i)
    have hc : ε i*(a i).a.cost ≤ α/8 :=
      (mul_le_mul_of_nonneg_left (a i).cost_le (hε i).le).trans (hεC i)
    have hb := (abs_le.mp hpair).1
    linarith [hhigh i]
  · exact fun n c hc => signed_sum_lipschitz hQc w
      (fun n x hx => sum_grad_norm_le z w ε hz hεsum herr n hx) n c hc

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_wuc_functions.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_wuc_functions.{uH}
