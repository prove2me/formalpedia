-- Prove2me | solution 1 for NumberField.mixedEmbedding.sgn_eq_one_of_forall_pos_of_polarCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2d998974-67bc-54bb-8467-bafe9a020db2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
      (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (hP_cont : ∀ s, Continuous (P s))
    (hP_mul : ∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ'))
    (hP_norm : ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
      normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ)))
    (hP_inv : ∀ y : mixedSpace K, IsUnit y →
      P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) :
    ∀ y : mixedSpace K, IsUnit y → (∀ w : {w : InfinitePlace K // w.IsReal}, 0 < y.1 w) → sgn y = 1 := by
  classical
  intro y hy hpos

  have hne : ∀ (s : {w : InfinitePlace K // w.IsReal} → ℤˣ) (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ))
      (w : {w : InfinitePlace K // w.IsReal}), (P s p).1 w ≠ 0 := by
    intro s p w h0
    have h1 := hP_norm s p.1 p.2 w.1
    rw [normAtPlace_apply_of_isReal w.2] at h1
    have : ‖(P s (p.1, p.2)).1 w‖ = 0 := by
      have : (P s (p.1, p.2)).1 ⟨w.1, w.2⟩ = (P s p).1 w := rfl
      rw [this, h0, norm_zero]
    rw [this] at h1
    exact (Real.exp_pos _).ne' h1.symm

  have hconst : ∀ (s : {w : InfinitePlace K // w.IsReal} → ℤˣ) (w : {w : InfinitePlace K // w.IsReal})
      (p q : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ)), (0 < (P s p).1 w ↔ 0 < (P s q).1 w) := by
    intro s w
    have hg : Continuous fun p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) => (P s p).1 w :=
      ((continuous_apply w).comp (continuous_fst.comp (hP_cont s)))
    have hpc : IsPreconnected (Set.univ : Set ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ))) :=
      convex_univ.isPreconnected

    have key : ∀ p q : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ), (P s p).1 w < 0 → 0 < (P s q).1 w → False := by
      intro p q hp hq
      have hsub := hpc.intermediate_value (Set.mem_univ p) (Set.mem_univ q) hg.continuousOn
      obtain ⟨r, -, hr⟩ := hsub ⟨hp.le, hq.le⟩
      exact hne s r w hr
    intro p q
    constructor
    · intro hp
      rcases lt_or_gt_of_ne (hne s q w) with hq | hq
      · exact (key q p hq hp).elim
      · exact hq
    · intro hq
      rcases lt_or_gt_of_ne (hne s p w) with hp | hp
      · exact (key p q hp hq).elim
      · exact hp

  set τ : ({w : InfinitePlace K // w.IsReal} → ℤˣ) → ({w : InfinitePlace K // w.IsReal} → ℤˣ) :=
    fun s w => if 0 < (P s 0).1 w then 1 else -1 with hτ
  have hτ_spec : ∀ s w (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ)),
      τ s w = 1 ↔ 0 < (P s p).1 w := by
    intro s w p
    rw [hτ]
    simp only
    have hc := hconst s w 0 p
    by_cases h : 0 < (P s 0).1 w
    · rw [if_pos h]; exact ⟨fun _ => hc.mp h, fun _ => rfl⟩
    · rw [if_neg h]
      constructor
      · intro h1; exact absurd h1 (by decide)
      · intro h2; exact absurd (hc.mpr h2) h

  have hτ_mul : ∀ s s', τ (s * s') = τ s * τ s' := by
    intro s s'
    funext w
    have hm : (P (s * s') 0).1 w = (P s 0).1 w * (P s' 0).1 w := by
      have := hP_mul s s' 0 0 0 0
      simp only [add_zero] at this
      have h0 : ((0 : Fin (Fintype.card (InfinitePlace K)) → ℝ), (0 : Fin (nrComplexPlaces K) → ℝ)) = (0 : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ)) := rfl
      rw [h0] at this
      rw [this]
      rfl

    have h1 := hne s 0 w
    have h2 := hne s' 0 w
    show τ (s * s') w = τ s w * τ s' w
    rw [hτ]
    simp only
    rw [hm]
    rcases lt_or_gt_of_ne h1 with a | a <;> rcases lt_or_gt_of_ne h2 with b | b
    · rw [if_pos (mul_pos_of_neg_of_neg a b), if_neg (not_lt.mpr a.le), if_neg (not_lt.mpr b.le)]; norm_num
    · rw [if_neg (not_lt.mpr (mul_neg_of_neg_of_pos a b).le), if_neg (not_lt.mpr a.le), if_pos b]; norm_num
    · rw [if_neg (not_lt.mpr (mul_neg_of_pos_of_neg a b).le), if_pos a, if_neg (not_lt.mpr b.le)]; norm_num
    · rw [if_pos (mul_pos a b), if_pos a, if_pos b]; norm_num

  have hτ_surj : Function.Surjective τ := by
    intro ε
    let yε : mixedSpace K := (fun w => ((ε w : ℤ) : ℝ), fun _ => 1)
    have hyε : IsUnit yε := by
      rw [Prod.isUnit_iff]
      refine ⟨Pi.isUnit_iff.mpr fun w => ?_, Pi.isUnit_iff.mpr fun _ => isUnit_one⟩
      rw [isUnit_iff_ne_zero]
      show ((ε w : ℤ) : ℝ) ≠ 0
      exact_mod_cast (ε w).ne_zero
    refine ⟨sgn yε, funext fun w => ?_⟩
    have hx := hP_inv yε hyε

    rcases Int.units_eq_one_or (ε w) with h | h
    · rw [h]
      apply (hτ_spec _ _ _).mpr
      rw [hx]
      show (0 : ℝ) < ((ε w : ℤ) : ℝ)
      rw [h]; norm_num
    · rw [h]
      have : ¬ τ (sgn yε) w = 1 := by
        rw [hτ_spec _ _ (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) yε), arg yε)]
        rw [hx, not_lt]
        show ((ε w : ℤ) : ℝ) ≤ 0
        rw [h]; norm_num
      rcases Int.units_eq_one_or (τ (sgn yε) w) with h' | h'
      · exact absurd h' this
      · exact h'
  have hτ_inj : Function.Injective τ := Finite.injective_iff_surjective.mpr hτ_surj

  have hτ1 : τ 1 = 1 := by
    have := hτ_mul 1 1
    rw [one_mul] at this
    exact (mul_right_cancel (by rw [one_mul]; exact this) : (1 : {w : InfinitePlace K // w.IsReal} → ℤˣ) = τ 1).symm
  have hτy : τ (sgn y) = 1 := by
    funext w
    rw [Pi.one_apply]
    apply (hτ_spec _ _ (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y)).mpr
    rw [hP_inv y hy]
    exact hpos w
  exact hτ_inj (hτy.trans hτ1.symm)

end S_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord
end P2MW
export P2MW.S_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord (solution)
