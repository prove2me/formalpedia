-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_smooth_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:59:37.012626+00:00
-- url     : https://prove2.me/submissions/b8fab539-5dc2-4dcd-8567-541789739791

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothMultiplier.lean:L77-L116
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_smooth_multiplier. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothHilbert ----
namespace OAI

universe uH uX

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem regularNorm_nonneg {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℝ) (x : H) : 0 ≤ regularNorm ε x := Real.sqrt_nonneg _

theorem regularNorm_sq {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℝ) (x : H) : (regularNorm ε x)^2 = ‖x‖^2+ε^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_le_regularNorm (ε : ℝ) (x : H) : ‖x‖ ≤ regularNorm ε x := by
  have := regularNorm_sq ε x
  have := regularNorm_nonneg ε x
  nlinarith [norm_nonneg x, sq_nonneg ε]

theorem regularNorm_le (ε : ℝ) (hε : 0 ≤ ε) (x : H) : regularNorm ε x ≤ ‖x‖+ε := by
  have := regularNorm_sq ε x
  have := regularNorm_nonneg ε x
  nlinarith [norm_nonneg x, mul_nonneg (norm_nonneg x) hε]

theorem regularNorm_contDiff {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ ∞ (regularNorm (H := H) ε) := by
  apply ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
  intro x
  have : 0 < ‖x‖^2+ε^2 := by positivity
  exact this.ne'

end LipschitzCounterexample.CompactWSC
end

end OAI

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

theorem exists_smooth_multiplier {ι : Type uIndex} [Fintype ι] (z : ι → Smooth H)
    (hz : ∀ i, LipschitzWith 1 (z i).val) (Q : Set H) (hQ : IsCompact Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Smooth H, ∃ D : ℝ, 0 < D ∧
      (∀ x, |φ.val x-damping Finset.univ z x| ≤ ε) ∧
      ∀ x ∈ Q, ‖Smooth.grad x φ‖ ≤ D := by
  classical
  let δ : ℝ := min (1/2) (ε/((Fintype.card ι : ℝ)+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδe : (Fintype.card ι : ℝ)*δ ≤ ε := by
    have h := min_le_right (1/2:ℝ) (ε/((Fintype.card ι : ℝ)+1))
    have hd : 0 < (Fintype.card ι : ℝ)+1 := by positivity
    have hmul := (le_div_iff₀ hd).mp h
    change δ*((Fintype.card ι : ℝ)+1) ≤ ε at hmul
    nlinarith
  let φ : Smooth H := ⟨fun x => ∏ i, (1-regularNorm δ (Smooth.grad x (z i))), by
    change ContDiff ℝ ∞ (fun x => ∏ i, (1-regularNorm δ (Smooth.grad x (z i))))
    apply contDiff_prod
    intro i _
    exact contDiff_const.sub ((regularNorm_contDiff hδ.ne').comp (z i).grad_contDiff)⟩
  have happ (x : H) : |φ.val x-damping Finset.univ z x| ≤ ε := by
    have ha (i : ι) : |1-regularNorm δ (Smooth.grad x (z i))| ≤ 1 := by
      have hn := (z i).grad_norm_le (hz i) x
      norm_num only [NNReal.coe_one] at hn
      have hr := regularNorm_le δ hδ.le (Smooth.grad x (z i))
      have hr0 := regularNorm_nonneg δ (Smooth.grad x (z i))
      rw [abs_le]; constructor <;> linarith
    have hb (i : ι) : |1-‖Smooth.grad x (z i)‖| ≤ 1 := by
      have hn := (z i).grad_norm_le (hz i) x
      norm_num only [NNReal.coe_one] at hn
      rw [abs_le]; constructor <;> linarith [norm_nonneg (Smooth.grad x (z i))]
    have hd (i : ι) : |(1-regularNorm δ (Smooth.grad x (z i)))-(1-‖Smooth.grad x (z i)‖)| ≤ δ := by
      have h₁ := norm_le_regularNorm δ (Smooth.grad x (z i))
      have h₂ := regularNorm_le δ hδ.le (Smooth.grad x (z i))
      rw [abs_le]; constructor <;> linarith
    exact (abs_prod_sub_prod_le Finset.univ _ _ (fun i _ => ha i) (fun i _ => hb i)).trans
      ((Finset.sum_le_sum (fun i _ => hd i)).trans (by simpa using hδe))
  obtain ⟨D,hD⟩ := hQ.exists_bound_of_continuousOn φ.grad_continuous.continuousOn
  exact ⟨φ,max D 1,by positivity,happ,fun x hx => (hD x hx).trans (le_max_left _ _)⟩

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter


theorem solution.{uH,uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_multiplier.{uH,uIndex} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_multiplier.{uH,uIndex}
