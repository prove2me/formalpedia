-- Prove2me | solution 1 for KarimiPL.ProxCD.appH_expected_improvement_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:55:53.470174+00:00
-- url     : https://prove2.me/submissions/47370729-732a-460e-ad03-0adbc2288356

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_IsProxGradStep
import Definitions.Def_KarimiPL_ProxCD_Dg
import Definitions.Def_KarimiPL_ProxCD_coordModel
import Definitions.Def_KarimiPL_ProxCD_IsCoordMin

open scoped InnerProductSpace

open KarimiPL.ProxCD in
theorem solution {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L : ℝ} (hL : 0 < L)
    (x : EuclideanSpace ℝ (Fin d)) (t : Fin d → ℝ)
    (ht : ∀ i, IsCoordMin f gc Dc L i x (t i)) :
    IsProxGradStep f (sepG gc) (sepDom Dc) L x (x + ∑ i, EuclideanSpace.single i (t i)) ∧
      1 / (d : ℝ) * ∑ i, coordModel f gc L i x (t i) =
        -(1 / (2 * L * d)) * Dg f (sepG gc) (sepDom Dc) L x := by
  have hsep : ∀ y : EuclideanSpace ℝ (Fin d),
      ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 + sepG gc y - sepG gc x =
        ∑ i, coordModel f gc L i x (y i - x i) := by
    intro y
    unfold sepG coordModel
    rw [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial, add_sub_cancel]
    first | done | ring
  obtain ⟨p, hp⟩ : ∃ p, p = x + ∑ i, EuclideanSpace.single i (t i) := ⟨_, rfl⟩
  have hpi : ∀ i, p i = x i + t i := by
    intro i
    rw [hp]
    simp [PiLp.single_apply]
  have hpD : p ∈ sepDom Dc := fun i => by rw [hpi]; exact (ht i).1
  have hval : ⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + sepG gc p - sepG gc x =
      ∑ i, coordModel f gc L i x (t i) := by
    rw [hsep]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpi, add_sub_cancel_left]
  have hmin : ∀ y ∈ sepDom Dc,
      ⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + sepG gc p - sepG gc x ≤
        ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 + sepG gc y - sepG gc x := by
    intro y hy
    rw [hval, hsep]
    apply Finset.sum_le_sum
    intro i _
    apply (ht i).2
    rw [add_sub_cancel]
    exact hy i
  rw [← hp]
  refine ⟨⟨hpD, hmin⟩, ?_⟩
  have hinf : (⨅ y : sepDom Dc, (⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
      L / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + sepG gc y - sepG gc x)) =
      ∑ i, coordModel f gc L i x (t i) := by
    haveI : Nonempty (sepDom Dc) := ⟨⟨p, hpD⟩⟩
    have hbdd : BddBelow (Set.range fun y : sepDom Dc =>
        (⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
          L / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + sepG gc y - sepG gc x)) :=
      ⟨_, Set.forall_mem_range.mpr fun y => hmin y y.2⟩
    rw [← hval]
    exact le_antisymm (ciInf_le hbdd (⟨p, hpD⟩ : sepDom Dc)) (le_ciInf fun y => hmin y y.2)
  unfold Dg
  rw [hinf]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
