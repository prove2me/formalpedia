-- Prove2me | solution 1 for GlobalTheory.rat_mem_span_of_real_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:20.594554+00:00
-- url     : https://prove2.me/submissions/20d9f995-4fb6-4178-a0cc-287e5db3a4db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ)
    (hv : (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ))) :
    v ∈ Submodule.span ℚ (Set.range w) := by
  by_contra hnot
  obtain ⟨f, hfv, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  classical
  set a : Fin r → ℚ := fun j => f (fun k => if j = k then 1 else 0) with ha
  have hf : ∀ x : Fin r → ℚ, f x = ∑ j, x j * a j := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hw : ∀ i, f (w i) = 0 := by
    intro i
    have : f (w i) ∈ (Submodule.span ℚ (Set.range w)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    rw [hfp] at this
    exact (Submodule.mem_bot ℚ).mp this
  let L : (Fin r → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j, x j * (a j : ℝ)
      map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    show ∑ j, ((w i j : ℚ) : ℝ) * (a j : ℝ) = 0
    have h := hw i
    rw [hf] at h
    have h' : ((∑ j, w i j * a j : ℚ) : ℝ) = 0 := by rw [h]; simp
    push_cast at h'
    exact h'
  have h0 : L (fun j => ((v j : ℚ) : ℝ)) = 0 := LinearMap.mem_ker.mp (hle hv)
  have h1 : ((f v : ℚ) : ℝ) = 0 := by
    rw [hf]
    push_cast
    exact h0
  exact hfv (by exact_mod_cast h1)
end GlobalTheory
