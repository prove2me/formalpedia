-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.lottery_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:21:17.759757+00:00
-- url     : https://prove2.me/submissions/c72b5c07-004c-4f49-b91b-e136e55c6d1e

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false
set_option maxHeartbeats 800000
open MechanismDesign.IncentiveCompat
open scoped BigOperators

theorem solution {Ω : Type*} [Fintype Ω] (S : Set (Ω → ℝ)) (hS : Convex ℝ S)
    (hSne : S.Nonempty) (q : S → stdSimplex ℝ Ω) :
    Implementable (fun (p : stdSimplex ℝ Ω) (θ : S) => lotteryUtility p (θ : Ω → ℝ)) q ↔
      ∃ U : (Ω → ℝ) → ℝ, ConvexOn ℝ S U ∧
        ∀ θ : S, IsSubgradientOn S U (θ : Ω → ℝ) ((q θ : stdSimplex ℝ Ω) : Ω → ℝ) := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    let U : (Ω → ℝ) → ℝ := fun x =>
      if hx : x ∈ S then lotteryUtility (q ⟨x,hx⟩) x - t ⟨x,hx⟩ else 0
    have hu (θ : S) : U θ = lotteryUtility (q θ) θ - t θ := by
      simp [U,θ.property]
    have hgrad (θ : S) : IsSubgradientOn S U (θ : Ω → ℝ) ((q θ : stdSimplex ℝ Ω) : Ω → ℝ) := by
      intro y hy
      let η : S := ⟨y,hy⟩
      have hic := ht η θ
      change U θ + dotProduct (q θ : Ω → ℝ) ((η : Ω → ℝ) - θ) ≤ U η
      rw [hu θ,hu η,dotProduct_sub]
      dsimp [IsIC,lotteryUtility] at *
      linarith
    refine ⟨U,?_,hgrad⟩
    refine ⟨hS,?_⟩
    intro x hx y hy a b ha hb hab
    let z : Ω → ℝ := a • x + b • y
    have hz : z ∈ S := hS hx hy ha hb hab
    let v : Ω → ℝ := q ⟨z,hz⟩
    have hzx := hgrad ⟨z,hz⟩ x hx
    have hzy := hgrad ⟨z,hz⟩ y hy
    change U z + dotProduct v (x-z) ≤ U x at hzx
    change U z + dotProduct v (y-z) ≤ U y at hzy
    have hcancel : a * dotProduct v (x-z) + b * dotProduct v (y-z) = 0 := by
      simp only [dotProduct,Pi.sub_apply]
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      calc
        _ = ∑ i : Ω, v i * (a*x i+b*y i-(a+b)*z i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [hab]
          change v i * (a*x i+b*y i-1*(a*x i+b*y i)) = 0
          ring
    have hax := mul_le_mul_of_nonneg_left hzx ha
    have hby := mul_le_mul_of_nonneg_left hzy hb
    have htotal := congrArg (fun r : ℝ => r * U z) hab
    change U z ≤ a * U x + b * U y
    nlinarith [hax,hby,htotal,hcancel]
  · rintro ⟨U,hconv,hgrad⟩
    refine ⟨fun θ => lotteryUtility (q θ) θ - U θ,?_⟩
    intro θ θ'
    have h := hgrad θ' θ θ.property
    rw [dotProduct_sub] at h
    dsimp [IsIC,lotteryUtility] at *
    linarith
