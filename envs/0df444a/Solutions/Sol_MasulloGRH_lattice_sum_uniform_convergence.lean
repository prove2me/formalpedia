-- Prove2me | solution 1 for MasulloGRH.lattice_sum_uniform_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:58:21.656726+00:00
-- url     : https://prove2.me/submissions/601d5d1c-b518-46a8-944b-0d2949b5fcc1

import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter

theorem solution
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Γ : Submodule ℤ E) [DiscreteTopology Γ] [IsZLattice ℝ Γ] (K : Set E) (hK : IsCompact K) :
    (∀ σ : ℝ, (Module.finrank ℝ E : ℝ) < σ →
      ∃ S : E → ℝ, TendstoUniformlyOn
        (fun (s : Finset {ξ : Γ // (ξ : E) ∉ K}) (x : E) =>
          ∑ ξ ∈ s, ‖((ξ : Γ) : E) + x‖ ^ (-σ))
        S Filter.atTop K) ∧
    (∀ ε : ℝ, 0 < ε → ∃ S : ℝ × E → ℝ, TendstoUniformlyOn
      (fun (s : Finset {ξ : Γ // (ξ : E) ∉ K}) (p : ℝ × E) =>
        ∑ ξ ∈ s, ‖((ξ : Γ) : E) + p.2‖ ^ (-p.1))
      S Filter.atTop (Set.Ici ((Module.finrank ℝ E : ℝ) + ε) ×ˢ K)) := by
  classical
  let A := {ξ : Γ // (ξ : E) ∉ K}
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  have hclosed : IsClosed (Γ : Set E) := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    Γ.toAddSubgroup (inferInstanceAs (DiscreteTopology Γ))
  have hlargeΓ : Tendsto (fun z : Γ => ‖(z : E)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding hclosed.isClosedEmbedding_subtypeVal
  have hlarge : Tendsto (fun z : A => ‖((z : Γ) : E)‖) cofinite atTop :=
    hlargeΓ.comp (Function.Injective.tendsto_cofinite Subtype.val_injective)
  have hmain (b : ℝ) (hb : (Module.finrank ℝ E : ℝ) < b) :
      TendstoUniformlyOn
        (fun (s : Finset A) (p : ℝ × E) => ∑ z ∈ s, ‖((z : Γ) : E) + p.2‖ ^ (-p.1))
        (fun p => ∑' z : A, ‖((z : Γ) : E) + p.2‖ ^ (-p.1))
        atTop (Set.Ici b ×ˢ K) := by
    have hr : -b < -(Module.finrank ℤ Γ : ℝ) := by rw [ZLattice.rank ℝ Γ]; linarith
    have hpos : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
    have hsum : Summable (fun z : A => (1 / 2 : ℝ) ^ (-b) * ‖((z : Γ) : E)‖ ^ (-b)) :=
      (((ZLattice.summable_norm_rpow Γ (-b) hr).subtype (fun z : Γ => (z : E) ∉ K)).mul_left _)
    apply tendstoUniformlyOn_tsum_of_cofinite_eventually hsum
    filter_upwards [hlarge.eventually_ge_atTop (max (2*B) 2)] with z hz
    rintro ⟨σ, x⟩ ⟨hσ, hx⟩
    change b ≤ σ at hσ
    change ‖‖((z : Γ) : E) + x‖ ^ (-σ)‖ ≤ _
    have hzB := (le_max_left (2*B) 2).trans hz
    have hz2 := (le_max_right (2*B) 2).trans hz
    have htri := norm_add_le (((z : Γ) : E) + x) (-x)
    rw [add_neg_cancel_right, norm_neg] at htri
    have hhalf : (1/2 : ℝ) * ‖((z : Γ) : E)‖ ≤ ‖((z : Γ) : E) + x‖ := by linarith [hB x hx]
    have hone : 1 ≤ ‖((z : Γ) : E) + x‖ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      _ ≤ ‖((z : Γ) : E) + x‖ ^ (-b) := Real.rpow_le_rpow_of_exponent_le hone (neg_le_neg hσ)
      _ ≤ ((1/2 : ℝ) * ‖((z : Γ) : E)‖) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hhalf (by linarith)
      _ = _ := Real.mul_rpow (by norm_num) (norm_nonneg _)
  constructor
  · intro σ hσ
    refine ⟨_, ((hmain σ hσ).comp (fun x : E => (σ, x))).mono ?_⟩
    intro x hx
    exact ⟨show σ ≤ σ from le_rfl, hx⟩
  · intro ε hε
    exact ⟨_, hmain _ (by linarith)⟩
