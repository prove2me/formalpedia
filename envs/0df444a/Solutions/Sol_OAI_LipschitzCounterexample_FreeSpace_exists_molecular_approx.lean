-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.exists_molecular_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:34:21.64097+00:00
-- url     : https://prove2.me/submissions/c01e9edc-3969-4681-8990-8427bc92c119

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/MolecularApproximation.lean:L85-L139
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.exists_molecular_approx. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_linearize_unique
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_supported_pairing_le

-- ---- from OAI.Analysis.LipschitzEquivalence.SupportedDuality ----
namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem dual_as_test (T : Space M →L[ℝ] ℝ) :
    test (normalized (fun x => T (point x)) (dual_point_lipschitz T)) = T := by
  have hzero : T (point 0) = 0 := by simp
  exact (linearize_unique _ (dual_point_lipschitz T) hzero _ (by
    intro x
    change T (point x)-T (point 0) = T (point x)
    rw [hzero,sub_zero])).symm.trans
    (linearize_unique _ (dual_point_lipschitz T) hzero T (fun _ => rfl))

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.MolecularApproximation ----
namespace OAI

universe uM

noncomputable section
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology BigOperators
open Filter Set Metric LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem supported_unitBall_subset_closure_convexHull_molecules (K : Set M) (h0 : (0 : M) ∈ K)
    (μ : Space M) (hμ : μ ∈ supported K) (hμnorm : ‖μ‖ ≤ 1) :
    μ ∈ closure (convexHull ℝ (Set.range (fun pq : K×K => molecule (pq.1 : M) pq.2))) := by
  by_contra hnot
  let A : Set (Space M) := Set.range (fun pq : K×K => molecule (pq.1 : M) pq.2)
  obtain ⟨T,u,hA,hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ A).closure isClosed_closure hnot
  have hm (p : M) (hp : p ∈ K) (q : M) (hq : q ∈ K) : T (molecule p q) < u :=
    hA _ (subset_closure (subset_convexHull ℝ A ⟨(⟨p,hp⟩,⟨q,hq⟩),rfl⟩))
  have hupos : 0 < u := by simpa using hm 0 h0 0 h0
  have hdiff (p : M) (hp : p ∈ K) (q : M) (hq : q ∈ K) :
      T (point p)-T (point q) ≤ u*dist p q := by
    by_cases hpq : p = q
    · simp [hpq]
    · have hp' : 0 < dist p q := dist_pos.mpr hpq
      have h := hm p hp q hq
      simp only [molecule,map_smul,map_sub,smul_eq_mul] at h
      have hh := (mul_lt_mul_of_pos_right h hp').le
      have he : (dist p q)⁻¹*(T (point p)-T (point q))*dist p q = T (point p)-T (point q) := by
        rw [mul_right_comm,inv_mul_cancel₀ hp'.ne',one_mul]
      rwa [he] at hh
  have hLip : LipschitzOnWith ⟨u,hupos.le⟩ (fun p => T (point p)) K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    change |T (point p)-T (point q)| ≤ u*dist p q
    rw [abs_le]
    exact ⟨by have := hdiff q hq p hp; rw [dist_comm q p] at this; linarith,hdiff p hp q hq⟩
  have hbound := supported_pairing_le h0 (fun p => T (point p))
    (dual_point_lipschitz T) hLip μ hμ
  rw [dual_as_test T] at hbound
  change |T μ| ≤ u*‖μ‖ at hbound
  have hmul : u*‖μ‖ ≤ u := by nlinarith
  exact (not_lt_of_ge ((le_abs_self (T μ)).trans (hbound.trans hmul))) hu

namespace MolecularData

end MolecularData

theorem exists_molecular_approx {K : Set M} (h0 : (0 : M) ∈ K)
    (μ : Space M) (hμ : μ ∈ supported K) {C ε : ℝ} (hC : 0 < C)
    (hbound : ‖μ‖ ≤ C) (hε : 0 < ε) :
    ∃ a : MolecularData M, (∀ i, a.p i ∈ K ∧ a.q i ∈ K) ∧
      a.cost ≤ C ∧ ‖μ-a.vector‖ < ε := by
  classical
  let ν : Space M := C⁻¹ • μ
  have hν : ν ∈ supported K := Submodule.smul_mem _ _ hμ
  have hνnorm : ‖ν‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hC.le]
    exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hC.le)).trans_eq
      (inv_mul_cancel₀ hC.ne')
  obtain ⟨v,hv,hclose⟩ := Metric.mem_closure_iff.mp
    (supported_unitBall_subset_closure_convexHull_molecules K h0 ν hν hνnorm)
    (ε/C) (div_pos hε hC)
  obtain ⟨ι,hι,w,z,hw,hsum,hz,hv⟩ := mem_convexHull_iff_exists_fintype.mp hv
  let : Fintype ι := hι
  choose pq hpq using hz
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let a : MolecularData M := {
    n := Fintype.card ι
    coeff := fun i => C*w (e i)*(dist (pq (e i)).1.val (pq (e i)).2.val)⁻¹
    p := fun i => (pq (e i)).1.val
    q := fun i => (pq (e i)).2.val }
  have hvec : a.vector = C • v := by
    rw [← hv, Finset.smul_sum, ← e.sum_comp (fun i => C • (w i • z i))]
    apply Finset.sum_congr rfl
    intro i _
    change (C*w (e i)*(dist (pq (e i)).1.val (pq (e i)).2.val)⁻¹) •
      (point (pq (e i)).1.val-point (pq (e i)).2.val) = C • (w (e i) • z (e i))
    rw [← hpq (e i)]
    simp only [molecule,mul_smul]
  have hcost : a.cost ≤ C := by
    have hterm (i : Fin a.n) : |a.coeff i| * dist (a.p i) (a.q i) ≤ C*w (e i) := by
      have hc : 0 ≤ a.coeff i := by
        change 0 ≤ C*w (e i)*(dist _ _)⁻¹
        exact mul_nonneg (mul_nonneg hC.le (hw _)) (inv_nonneg.mpr dist_nonneg)
      rw [abs_of_nonneg hc]
      change (C*w (e i)*(dist _ _)⁻¹)*dist (a.p i) (a.q i) ≤ C*w (e i)
      by_cases hd : dist (a.p i) (a.q i) = 0
      · change (C*w (e i)*(dist (a.p i) (a.q i))⁻¹)*dist (a.p i) (a.q i) ≤ _
        rw [hd,mul_zero]
        exact mul_nonneg hC.le (hw _)
      · change (C*w (e i)*(dist (a.p i) (a.q i))⁻¹)*dist (a.p i) (a.q i) ≤ _
        rw [mul_assoc,inv_mul_cancel₀ hd,mul_one]
    calc
      a.cost ≤ ∑ i : Fin a.n, C*w (e i) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = C := by rw [← Finset.mul_sum, e.sum_comp, hsum,mul_one]
  refine ⟨a,fun i => ⟨(pq (e i)).1.property,(pq (e i)).2.property⟩,hcost,?_⟩
  have hμeq : μ = C • ν := by simp only [ν,smul_smul,mul_inv_cancel₀ hC.ne',one_smul]
  rw [hvec,hμeq,← smul_sub,norm_smul,Real.norm_of_nonneg hC.le]
  have hc : ‖ν-v‖ < ε/C := by simpa [dist_eq_norm] using hclose
  have := mul_lt_mul_of_pos_left hc hC
  rw [mul_div_cancel₀ ε hC.ne'] at this
  exact this

end LipschitzCounterexample.FreeSpace
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped NNReal Topology BigOperators
open Filter Set Metric LocalizedLinearization


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.exists_molecular_approx.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.exists_molecular_approx.{uM}
