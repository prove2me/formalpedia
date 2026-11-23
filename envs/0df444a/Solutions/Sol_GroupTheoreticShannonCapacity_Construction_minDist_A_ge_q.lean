-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.minDist_A_ge_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:36.030468+00:00
-- url     : https://prove2.me/submissions/ccb251b5-83ac-472f-93f3-0dbc4a9463d2

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_q_pos
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixA_eq_X_add_qI
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_min_distance_bound


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) [NeZero n] (k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    Lattice.minDistance n (Lattice.latticeOfMatrix n
      ((matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ))) ≥
      (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  -- Define the key values with explicit types to help elaboration
  let X : Matrix (Fin n) (Fin n) ℝ := (matrixX n k b r s).map (↑· : ℚ → ℝ)
  let qval : ℝ := (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)
  have hq_pos : (0 : ℝ) < qval := q_pos n k b r s hk hb
  have hX_P0 : P0Matrix.IsP0Matrix n X := X_isP0 n k b r s hn hk hb hrb
  have hA_eq : ((matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ)) = X + qval • 1 :=
    matrixA_eq_X_add_qI n k b r s
  calc Lattice.minDistance n (Lattice.latticeOfMatrix n
         ((matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ)))
      = Lattice.minDistance n (Lattice.latticeOfMatrix n (X + qval • 1)) := by rw [hA_eq]
    _ ≥ qval := P0Matrix.p0_min_distance_bound n X hX_P0 qval hq_pos
end GroupTheoreticShannonCapacity.Construction
