-- Prove2me | solution 1 for OAI.SharpPlanar.piece_density_bound_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:27:17.27422+00:00
-- url     : https://prove2.me/submissions/54480da9-a31e-4970-bb85-495c7eb8aa63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G365
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basis_density_bounds_g
import Theorems.Thm_OAI_SharpPlanar_X_norm_g
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_piece_summand_bound_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma piece_density_bound_g_oai (p : CardinalData) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖density p j.val t‖ ≤ densityCap j*(|p.c₀|+|p.d₀|+‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n,false):ℂ)*u n.val j.val t+
      (p.x (n,true):ℂ)*v n.val j.val t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => piece_summand_bound_g p.x n j ht)
      ((X_summable_pairs_g p.x).mul_left (densityCap j))
  have hsum : ‖∑' n : Node, ((p.x (n,false):ℂ)*u n.val j.val t+
      (p.x (n,true):ℂ)*v n.val j.val t)‖ ≤ densityCap j*‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n,false):ℂ)*u n.val j.val t+
        (p.x (n,true):ℂ)*v n.val j.val t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityCap j*(|p.x (n,false)|+|p.x (n,true)|) :=
        hnorm.tsum_le_tsum (fun n => piece_summand_bound_g p.x n j ht)
          ((X_summable_pairs_g p.x).mul_left (densityCap j))
      _ = _ := by rw [tsum_mul_left,← X_norm_g]
  obtain ⟨hu,hv⟩ := basis_density_bounds_g 0 (by simp [residues]) j ht
  unfold density
  calc
    _ ≤ ‖(p.c₀:ℂ)*u 0 j.val t‖+‖(p.d₀:ℂ)*v 0 j.val t‖+
        ‖∑' n : Node, ((p.x (n,false):ℂ)*u n.val j.val t+
          (p.x (n,true):ℂ)*v n.val j.val t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| *densityCap j+|p.d₀| *densityCap j+densityCap j*‖p.x‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      gcongr
    _ = _ := by ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_density_bound_g_oai := @OAI.SharpPlanar.piece_density_bound_g_oai
