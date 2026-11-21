-- Prove2me | solution 2 for MasulloGRH.nuclearFrechet_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T23:59:27.318172+00:00
-- url     : https://prove2.me/submissions/b7054446-f4a5-44f4-9ae5-c938bfd48606

import Theorems.Thm_MasulloGRH_bounded_disk_scalar_expansion

set_option autoImplicit false
open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → E) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  obtain ⟨y, c, a, hy, hc0, hc, ha, hxSum⟩ :=
    bounded_disk_scalar_expansion E hE.2.1 hN (.inl hE) B hB
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  letI : Nonempty ι := hι
  letI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hp.continuousSMul
  have hyb := hy.isVonNBounded_range ℂ
  refine ⟨y, c, hyb, hc0, hc, ?_⟩
  intro f x hx
  let v : Submodule.span ℂ B := ⟨x, Submodule.subset_span hx⟩
  obtain ⟨M, hM⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).mp (hyb.image f)
  have hs : Summable (fun n => c n * ‖f (y n)‖) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hM (y n) ⟨n, rfl⟩) (hc0 n)) (hc.mul_right M)
  apply (f.hasSum (hxSum v)).norm_le_of_bounded hs.hasSum
  intro n
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (ha n v hx) (norm_nonneg _)
