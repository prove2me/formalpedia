-- Prove2me | solution 1 for HodgeComputer.RankOneBiquartic.F_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:45:47.784399+00:00
-- url     : https://prove2.me/submissions/d2666f41-941d-4782-808b-aac28d09bb80

import Definitions.Def_HodgeComputerRankOneBiquartic

set_option autoImplicit false
open HodgeComputer HodgeComputer.RankOneBiquartic
theorem _root_.solution : F ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ)) h
  unfold HodgeComputer.RankOneBiquartic.F at this
  simp only [map_add, map_mul, map_pow, map_zero, map_one, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C] at this
  have e0 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 0 = 1 := rfl
  have e1 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 1 = 0 := rfl
  have e2 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 2 = 0 := rfl
  have e3 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 3 = 0 := rfl
  have e4 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 4 = 0 := rfl
  have e5 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) 5 = 0 := rfl
  simp only [e0, e1, e2, e3, e4, e5, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at this
  exact one_ne_zero (this.trans (map_zero _))

