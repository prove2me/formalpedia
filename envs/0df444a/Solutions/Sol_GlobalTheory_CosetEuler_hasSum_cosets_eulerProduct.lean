-- Prove2me | solution 1 for GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:32.150695+00:00
-- url     : https://prove2.me/submissions/d6683f1b-a0b0-4925-a960-948c1f2efa11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_offSet_nonneg
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_offSet_summable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
namespace GlobalTheory.CosetEuler
theorem _root_.solution : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  intro G ι _ L _ e p K J H hJH hpe hpe' he _ hJ hfin Ψ Φ Z A z hΨ hΦ hΨΦ hZ hA hA1 hz
  classical
  have hΦ0 : ∀ g ∈ H, 0 ≤ Φ g := fun g hg => (norm_nonneg _).trans (hΨΦ g hg)
  have hphi := hasSum_offSet_nonneg hJH hpe hpe' he hJ Φ hΦ0 hΦ A hA
  have hsA : Summable (fun v => |A v - 1|) := hA1.abs
  have hφ : Summable fun y : H ⧸ J.subgroupOf H => Φ ((y.out : H) : G) := by
    refine summable_of_sum_le (c := Real.exp (∑' v, |A v - 1|) * Φ 1)
      (fun y => hΦ0 _ (y.out).2) fun u => ?_
    let T : Finset ι := u.biUnion fun y => (hfin _ (y.out).2).toFinset
    have hu : ∀ y ∈ u, y ∈ offSet p K J H T := fun y hy v hv => by
      by_contra h
      exact hv (Finset.mem_biUnion.2 ⟨y, hy, (Set.Finite.mem_toFinset _).2 h⟩)
    calc ∑ y ∈ u, Φ ((y.out : H) : G)
        = ∑ y ∈ u, (offSet p K J H T).indicator (fun y => Φ ((y.out : H) : G)) y :=
          Finset.sum_congr rfl fun y hy =>
            (Set.indicator_of_mem (hu y hy) (fun y => Φ ((y.out : H) : G))).symm
      _ ≤ (∏ v ∈ T, A v) * Φ 1 :=
          sum_le_hasSum u (fun y _ => Set.indicator_nonneg (fun y _ => hΦ0 _ (y.out).2) _) (hphi T)
      _ ≤ Real.exp (∑' v, |A v - 1|) * Φ 1 := by
        refine mul_le_mul_of_nonneg_right ?_ (hΦ0 1 H.one_mem)
        calc ∏ v ∈ T, A v ≤ ∏ v ∈ T, |A v| := (le_abs_self _).trans (Finset.abs_prod _ _).le
          _ ≤ ∏ v ∈ T, Real.exp |A v - 1| :=
              Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => by
                have h1 := Real.add_one_le_exp |A v - 1|
                have h2 := abs_sub_abs_le_abs_sub (A v) 1
                rw [abs_one] at h2
                linarith
          _ = Real.exp (∑ v ∈ T, |A v - 1|) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, |A v - 1|) :=
              Real.exp_le_exp.2 (hsA.sum_le_tsum T fun v _ => abs_nonneg _)
  have hψ : Summable fun y : H ⧸ J.subgroupOf H => Ψ ((y.out : H) : G) :=
    Summable.of_norm_bounded hφ fun y => hΨΦ _ (y.out).2
  have hpsi := hasSum_offSet_summable hJH hpe hpe' he hJ Ψ hΨ Z hZ hψ
  have hlim : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (∑' y : H ⧸ J.subgroupOf H, Ψ ((y.out : H) : G))) := by
    refine tendsto_tsum_of_dominated_convergence hφ (fun y => ?_)
      (Eventually.of_forall fun T y => ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (hfin _ (y.out).2).toFinset] with T hT
      refine (Set.indicator_of_mem (show y ∈ offSet p K J H T from fun v hv => ?_)
        (fun y => Ψ ((y.out : H) : G))).symm
      by_contra h
      exact hv (hT ((Set.Finite.mem_toFinset _).2 h))
    · exact (norm_indicator_le_norm_self _ _).trans (hΨΦ _ (y.out).2)
  have hlim2 : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (z * Ψ 1)) := by
    simp only [fun T => (hpsi T).tsum_eq]
    exact (hz : Tendsto (fun s : Finset ι => ∏ b ∈ s, Z b) atTop (𝓝 z)).mul_const _
  rw [← tendsto_nhds_unique hlim hlim2]
  exact hψ.hasSum
end GlobalTheory.CosetEuler
