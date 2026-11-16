-- Prove2me | solution 1 for InfoLossLAR.WorstCase.smith_modular_rank_nullity
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:33:57.864206+00:00
-- url     : https://prove2.me/submissions/ffa6a8bd-6a4e-4237-9b3b-dec128e4b31a

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
open InfoLossLAR.WorstCase
set_option autoImplicit false

 theorem rank_child (q r d : ℕ) [Fact q.Prime] (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) : (matModq q T).rank = r := by
  let f : ℤ →+* ZMod q := Int.castRingHom _
  have hu : IsUnit (matModq q S.U).det := by
    change IsUnit (f.mapMatrix S.U).det
    rw [← f.map_det]
    exact S.U_unimod.map f
  have hv : IsUnit (matModq q S.V).det := by
    change IsUnit (f.mapMatrix S.V).det
    rw [← f.map_det]
    exact S.V_unimod.map f
  have hs : matModq q S.U * matModq q T * matModq q S.V = matModq q (smithDiag q r d) := by
    change S.U.map f * T.map f * S.V.map f = (smithDiag q r d).map f
    rw [← Matrix.map_mul, ← Matrix.map_mul, S.smith]
  have hr := congrArg Matrix.rank hs
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hv,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu] at hr
  rw [hr]
  have he : matModq q (smithDiag q r d) = Matrix.diagonal (fun i : Fin d => if (i : ℕ) < r then (1 : ZMod q) else 0) := by
    ext i j
    simp [matModq, smithDiag, Matrix.diagonal_apply]
  rw [he, Matrix.rank_diagonal]
  classical
  have hc : Fintype.card { i : Fin d // (if (i : ℕ) < r then (1 : ZMod q) else 0) ≠ 0 } = r := by
    rw [Fintype.card_subtype]
    simp only [ite_ne_left_iff, one_ne_zero, not_false_eq_true, ite_ne_right_iff, ne_eq, and_true]
    rw [Fin.card_filter_val_lt, Nat.min_eq_right S.r_le]
  exact hc

theorem solution (q r d : ℕ) [Fact q.Prime] (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) :
    (matModq q T).rank = r ∧
    Module.finrank (ZMod q) (LinearMap.ker (Matrix.mulVecLin (matModq q T))) = d - r := by
  constructor
  · exact rank_child q r d T S
  · have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (matModq q T))
    have hr := rank_child q r d T S
    change Module.finrank (ZMod q) (LinearMap.range (Matrix.mulVecLin (matModq q T))) = r at hr
    rw [hr] at h
    simp only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_fin] at h
    omega
