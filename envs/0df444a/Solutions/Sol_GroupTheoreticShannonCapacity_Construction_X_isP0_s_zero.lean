-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.X_isP0_s_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:21.513666+00:00
-- url     : https://prove2.me/submissions/dc558a94-bd49-4a22-9097-cc5642825568

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixX_real_eq_map
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixX_real_continuous_s
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixX_real_isP0_s_pos
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_closed


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r 0).map (↑· : ℚ → ℝ)) := by
  -- Strategy: X(0) is the limit of X(s) as s → 0⁺, where X(s) is P₀ for s > 0.
  -- Since P₀ is closed (isP0_closed), the limit is P₀.
  -- The key fact: matrixX is continuous in s (as a real matrix)
  have hcont : Continuous (fun s : ℝ => matrixX_real n k b r s) :=
    matrixX_real_continuous_s n k b r
  -- X(0) = matrixX_real n k b r 0
  have heq : (matrixX n (k:ℤ) (b:ℤ) (r:ℤ) 0).map (↑· : ℚ → ℝ) = matrixX_real n k b r 0 := by
    have h := matrixX_real_eq_map n k b r 0
    simp only [Nat.cast_zero] at h
    exact h.symm
  rw [heq]
  -- Use that P₀ is a closed set and X(s) → X(0) as s → 0
  have hP0_closed : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | P0Matrix.IsP0Matrix n M} :=
    P0Matrix.isP0_closed n
  -- Use the sequence s_m = 1/(m+1) for m ≥ 0
  have htendsto : Filter.Tendsto (fun m : ℕ => matrixX_real n k b r (1 / (m + 1 : ℝ)))
      Filter.atTop (nhds (matrixX_real n k b r 0)) := by
    have h1 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1 : ℝ)) Filter.atTop (nhds 0) := by
      simp only [one_div]
      have h2 : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds
      exact h2.inv_tendsto_atTop
    exact hcont.tendsto 0 |>.comp h1
  -- Each X(1/(m+1)) is P₀ since 1/(m+1) > 0
  have hseq_P0 : ∀ m : ℕ, P0Matrix.IsP0Matrix n (matrixX_real n k b r (1 / (m + 1 : ℝ))) := by
    intro m
    have hs_pos : 0 < 1 / (m + 1 : ℝ) := by positivity
    exact matrixX_real_isP0_s_pos n k b r _ hn hk hb hrb hs_pos
  -- The limit of a sequence in a closed set is in the set
  have hlimit :
      matrixX_real n k b r 0 ∈ {M : Matrix (Fin n) (Fin n) ℝ | P0Matrix.IsP0Matrix n M} := by
    apply hP0_closed.mem_of_tendsto htendsto
    exact Filter.Eventually.of_forall hseq_P0
  exact hlimit
end GroupTheoreticShannonCapacity.Construction
