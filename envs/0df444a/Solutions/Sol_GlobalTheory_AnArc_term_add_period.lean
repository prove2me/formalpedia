-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:30.58914+00:00
-- url     : https://prove2.me/submissions/eec966dc-2fcc-4150-8d97-45e304c7be11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Theorems.Thm_GlobalTheory_AnArc_La_eq_add_parts
import Theorems.Thm_GlobalTheory_AnArc_ah_add
import Theorems.Thm_GlobalTheory_AnArc_degeneratingTori_periodMap_eq_base_of_y_eq_zero
import Theorems.Thm_GlobalTheory_AnArc_e_neg_div
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0_l
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0_n
import Theorems.Thm_GlobalTheory_AnArc_term_add_Pw_y


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
open AlgebraicGeometry CategoryTheory Limits
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O)
open _root_.GlobalTheory.AnArc.La
namespace GlobalTheory.AnArc
namespace _root_.GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (μ : A.X) (v : A.V) :
    A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ) =
      A.perFactor w la v ^ j *
        (A.term j α th (μ + la.y) v *
          _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α (μ + la.y))) := by
  set y := la.y with hy
  set n := la.n with hn
  set l := la.l with hl
  set L : A.La := _root_.GlobalTheory.AnArc.La.mk 0 0 l
  set M : A.La := _root_.GlobalTheory.AnArc.La.mk 0 n 0
  set Y : A.La := _root_.GlobalTheory.AnArc.La.mk y 0 0
  have hPw : A.Pw w la = A.Pw w Y + A.P0 M + A.P0 L := by
    conv_lhs => rw [eq_add_parts la]
    rw [map_add, map_add, _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _),
      _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _)]
  set v' : A.V := v + A.P0 L + A.P0 M
  have hv : v + A.Pw w la = v' + A.Pw w Y := by
    rw [hPw]
    simp only [v']
    abel
  have key := A.term_add_Pw_y j α th w μ y v'
  rw [← hv] at key
  have hterm : A.term j α th (μ + y) v' =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j *
        A.term j α th (μ + y) v := by
    rw [_root_.GlobalTheory.AnArc.term_add_P0_n,
      _root_.GlobalTheory.AnArc.term_add_P0_l A h]
  have hv1 : v'.1 y = v.1 y + (n y : ℂ) + -(A.H (A.ct y) l / (2 * Complex.I)) := by
    simp [v', L, M, Prod.fst_add, _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_fst_apply, mk_y, mk_n, mk_l]
    ring
  set X : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  set X' : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v'.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  have hX' : X' = X * Complex.exp (-(Real.pi * A.H (A.ct y) l)) := by
    simp only [X', X, hv1, _root_.GlobalTheory.AnArc.e_add, _root_.GlobalTheory.AnArc.e_intCast, _root_.GlobalTheory.AnArc.e_neg_div]
    ring
  have hX'0 : X' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (_root_.GlobalTheory.AnArc.e_ne_zero _)) (_root_.GlobalTheory.AnArc.e_ne_zero _)
  have hfac : A.perFactor w la v =
      A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l) * X'⁻¹ := by
    rw [_root_.GlobalTheory.AnArc.perFactor, ← hy, ← hl, _root_.GlobalTheory.AnArc.ah_add, hX']
    simp only [mul_inv, ← Complex.exp_neg, neg_neg, _root_.GlobalTheory.AnArc.ah, X]
    ring
  calc A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)
      = (X' ^ j)⁻¹ *
          (X' ^ j * (A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ))) := by
        rw [inv_mul_cancel_left₀ (pow_ne_zero _ hX'0)]
    _ = _ := by
        rw [key, hterm, hfac]
        ring
end _root_.GlobalTheory.AnArc
end GlobalTheory.AnArc
