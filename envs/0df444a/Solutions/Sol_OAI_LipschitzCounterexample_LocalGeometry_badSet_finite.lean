-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalGeometry.badSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:27:37.632305+00:00
-- url     : https://prove2.me/submissions/465aeaa3-28db-49bc-9384-6664f0c5eb4a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean:L158-L206
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalGeometry.badSet_finite. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_CoordinateSpaces_sum_projection_sq_le

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem norm_projection_le (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) : ‖projection S x‖ ≤ ‖x‖ :=
  (space S).norm_starProjection_apply_le x

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem head_add_tail (l : ℕ) (x : Hilbert (ι := ι)) : head l x + tail l x = x := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  change head l x n a + tail l x n a = x n a
  rw [head_coord,tail_coord]
  split_ifs <;> simp_all
  omega

theorem inner_head (l : ℕ) (x y : Hilbert (ι := ι)) : ⟪head l x,y⟫_ℝ = ⟪x,head l y⟫_ℝ :=
  (space (headSet l)).inner_starProjection_left_eq_right x y

theorem head_eq_sum (l : ℕ) (x : Hilbert (ι := ι)) :
    head l x = ∑ n ∈ Finset.range l, lp.single 2 n (x n) := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  change head l x n a = coord ⟨n,a⟩ (∑ m ∈ Finset.range l, lp.single 2 m (x m))
  rw [head_coord,map_sum]
  simp only [coord_apply]
  by_cases hn : n < l
  · rw [ite_eq_left hn,Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [lp.single_apply, Ne.symm hmn]
    · simp [hn]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := fun h => hn (h ▸ Finset.mem_range.mp hm)
    simp [lp.single_apply, Ne.symm hmn]

theorem head_tendsto_zero {b : ℕ → Hilbert (ι := ι)}
    (hb : ∀ a : Σ n, ι n, Tendsto (fun i => b i a.1 a.2) atTop (𝓝 0)) (l : ℕ) :
    Tendsto (fun i => head l (b i)) atTop (𝓝 0) := by
  have hn (n : ℕ) : Tendsto (fun i => b i n) atTop (𝓝 0) := by
    apply (PiLp.continuous_toLp 2 (fun _ : ι n => ℝ)).continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr (fun a => hb ⟨n,a⟩)
  have hs (n : ℕ) : Tendsto (fun i => (lp.single 2 n (b i n) : Hilbert (ι := ι))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, lp.singleContinuousLinearMap_apply, map_zero] using ((lp.singleContinuousLinearMap ℝ (fun n => EuclideanSpace ℝ (ι n)) 2 n).continuous.tendsto 0).comp (hn n)
  simpa only [head_eq_sum, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range l) (fun n _ => hs n)

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalLipschitz ----
namespace OAI

universe uM uN uB uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {N : Type uN} [MetricSpace M] [MetricSpace N]

theorem quotients_nonempty (f : M → N) (S : Set M) : (quotients f S).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem constant_le {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : constant f S ≤ L := by
  apply csSup_le (quotients_nonempty f S)
  rintro r (rfl | ⟨x,hx,y,hy,rfl⟩)
  · exact L.coe_nonneg
  · exact quotient_le hf hx hy

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} [MetricSpace M]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem scalar_local_lipschitz (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) {O : Set M} (l : ℕ) (S : Set (Σ n, ι n))
    (hS : ∀ x ∈ O, tail l (D x) ∈ space S) (b : Hilbert (ι := ι)) :
    LipschitzOnWith
      ⟨L * (‖projection S b‖ + ‖head l b‖), mul_nonneg L.coe_nonneg (by positivity)⟩
      (fun x => ⟪D x,b⟫_ℝ) O := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hv : tail l (D x-D y) ∈ space S := by
    rw [map_sub]
    exact Submodule.sub_mem _ (hS x hx) (hS y hy)
  have hid : ⟪D x,b⟫_ℝ-⟪D y,b⟫_ℝ =
      ⟪tail l (D x-D y),projection S b⟫_ℝ + ⟪D x-D y,head l b⟫_ℝ := by
    rw [inner_projection S hv, ← inner_head, ← inner_add_left,
      add_comm (tail l (D x-D y)), head_add_tail, inner_sub_left]
  rw [Real.dist_eq, hid]
  calc
    |⟪tail l (D x-D y),projection S b⟫_ℝ+⟪D x-D y,head l b⟫_ℝ| ≤
        |⟪tail l (D x-D y),projection S b⟫_ℝ|+|⟪D x-D y,head l b⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖tail l (D x-D y)‖*‖projection S b‖+‖D x-D y‖*‖head l b‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖D x-D y‖ * (‖projection S b‖+‖head l b‖) := by
      dsimp [tail]
      nlinarith [mul_le_mul_of_nonneg_right (norm_projection_le (tailSet l) (D x-D y))
        (norm_nonneg (projection S b))]
    _ ≤ (L * (‖projection S b‖+‖head l b‖)) * dist x y := by
      have ht := hD.dist_le_mul x y
      rw [dist_eq_norm] at ht
      nlinarith [mul_le_mul_of_nonneg_right ht (show 0 ≤ ‖projection S b‖+‖head l b‖ by positivity)]

end LipschitzCounterexample.LocalGeometry
namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem badSet_finite (D : M → Hilbert (ι := ι)) {L : ℝ≥0} (hL : 0 < L)
    (hD : LipschitzWith L D) (hloc : LocalOrthogonality D)
    (b : ℕ → Hilbert (ι := ι)) (hbn : ∀ i, ‖b i‖ ≤ 1)
    (hb : ∀ a : Σ n, ι n, Tendsto (fun i => b i a.1 a.2) atTop (𝓝 0))
    {B : Type uB} (O : B → Set M)
    (hbase : ∀ z : M, ∀ r : ℝ, 0 < r → ∃ j, z ∈ O j ∧ O j ⊆ Metric.ball z r)
    (a : B → ℝ)
    (ha : ∀ j, Tendsto (fun i => constant (fun x => ⟪D x,b i⟫_ℝ) (O j)) atTop (𝓝 (a j)))
    {η : ℝ} (hη : 0 < η) : (badSet O a η).Finite := by
  classical
  by_contra hn
  have hinf : (badSet O a η).Infinite := hn
  let e : ℕ ↪ badSet O a η := hinf.natEmbedding _
  let t : ℝ := η / (4 * (L : ℝ))
  have hL' : 0 < (L : ℝ) := hL
  have ht : 0 < t := div_pos hη (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_gt (1 / t^2)
  have hlarge : 1 < (N : ℝ) * t^2 := by
    exact (div_lt_iff₀ (sq_pos_of_pos ht)).mp hN
  let z : Fin N → M := fun j => (e j.val).val
  have hz : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    apply e.injective
    exact Subtype.ext hij
  obtain ⟨r,hr,l,S,hS,hDS⟩ := hloc z hz
  choose j hzj hj using fun k => hbase (z k) r hr
  have hja (k : Fin N) : η ≤ a (j k) := (e k.val).property (j k) (hzj k)
  have hhead : Tendsto (fun i => ‖head l (b i)‖) atTop (𝓝 0) := by
    simpa using (head_tendsto_zero hb l).norm
  have hbound (k : Fin N) : ∀ᶠ i in atTop, t ≤ ‖projection (S k) (b i)‖ := by
    have hsmall := hhead.eventually (eventually_lt_nhds ht)
    have hbig := (ha (j k)).eventually (eventually_gt_nhds (show η / 2 < a (j k) by linarith [hja k]))
    filter_upwards [hsmall,hbig] with i hi hgi
    have hconst := constant_le (scalar_local_lipschitz D hD l (S k)
      (fun x hx => hDS k x (hj k hx)) (b i))
    change constant (fun x => ⟪D x,b i⟫_ℝ) (O (j k)) ≤
      (L : ℝ) * (‖projection (S k) (b i)‖+‖head l (b i)‖) at hconst
    have htid : (L : ℝ) * t = η / 4 := by dsimp [t]; field_simp
    nlinarith
  obtain ⟨i,hi⟩ := (Filter.eventually_all.mpr hbound).exists
  have hbessel := sum_projection_sq_le S hS (b i)
  have hsum : ∑ k : Fin N, t^2 ≤ ∑ k : Fin N, ‖projection (S k) (b i)‖^2 := by
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ ht.le (hi k) 2
  have hsum' : (N : ℝ) * t^2 ≤ ‖b i‖^2 := by
    simpa using hsum.trans hbessel
  nlinarith [hbn i, norm_nonneg (b i)]

end LipschitzCounterexample.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalGeometry
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open CoordinateSpaces LocalLipschitz


theorem solution.{uM,uB,uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.LocalGeometry.badSet_finite.{uM,uB,uIndex} := @_root_.OAI.LipschitzCounterexample.LocalGeometry.badSet_finite.{uM,uB,uIndex}
