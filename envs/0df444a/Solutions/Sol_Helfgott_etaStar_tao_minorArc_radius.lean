-- Prove2me | solution 1 for Helfgott.etaStar_tao_minorArc_radius
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T16:52:19.177881+00:00
-- url     : https://prove2.me/submissions/1a6c4147-0bc8-4c23-a7ae-157bba70aef6

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic
import Theorems.Thm_Helfgott_etaStar_tao_gaussian_bound

open scoped Classical

namespace Helfgott

theorem rational_mem_majorArcs (δ x : ℝ) (r : ℕ) (α : AddCircle (1:ℝ))
    (p : ℚ) (hδ : 0 ≤ δ) (hx : 0 < x) (hp : p.den ≤ r)
    (hd : dist α ((p:ℝ) : AddCircle (1:ℝ)) < δ*r/(2*p.den*x)) :
    α ∈ majorArcs δ r x := by
  let u := Int.fract p
  have hu : 0 ≤ u.num := Rat.num_nonneg.mpr (Int.fract_nonneg p)
  have hden : u.den = p.den := Rat.den_intFract p
  have hnum : (u.num.natAbs:ℝ) = (u.num:ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natAbs_of_nonneg hu)
  have hrep : (u.num.natAbs:ℝ)/(u.den:ℝ) = (u:ℝ) := by
    rw [hnum]
    exact (Rat.cast_def u).symm
  have hlt : u.num.natAbs < u.den := by
    have hv : (u:ℝ) < 1 := by exact_mod_cast Int.fract_lt_one p
    rw [← hrep] at hv
    have hd0 : (0:ℝ) < u.den := by exact_mod_cast u.pos
    have := (div_lt_iff₀ hd0).mp hv
    exact_mod_cast (by simpa using this : (u.num.natAbs:ℝ) < u.den)
  have hcop : u.num.natAbs.Coprime u.den := u.reduced
  have hcircle : (((u.num.natAbs:ℝ)/(u.den:ℝ):ℝ) : AddCircle (1:ℝ)) = (p:ℝ) := by
    rw [hrep]
    change (((Int.fract p:ℚ):ℝ) : AddCircle (1:ℝ)) = _
    rw [Rat.cast_fract, AddCircle.coe_fract]
  refine ⟨u.den, u.num.natAbs, u.pos, hlt, hcop, ?_⟩
  rcases Nat.even_or_odd u.den with he | ho
  · right
    refine ⟨he, by omega, ?_⟩
    rw [hcircle, hden]
    apply hd.trans_le
    have hd0 : (0:ℝ) < p.den := by exact_mod_cast p.pos
    have hn : 0 ≤ δ*(r:ℝ) := mul_nonneg hδ (Nat.cast_nonneg r)
    apply div_le_div_of_nonneg_left hn (by positivity)
    nlinarith
  · refine Or.inl ⟨ho, by omega, ?_⟩
    rw [hcircle, hden]
    exact hd

theorem minorArc_dirichlet (δ x α : ℝ) (r N : ℕ)
    (hδ : 0 ≤ δ) (hx : 0 < x) (hN : 0 < N)
    (hscale : 2*x < δ*r*((N:ℝ)+1))
    (hminor : (α : AddCircle (1:ℝ)) ∉ majorArcs δ r x) :
    ∃ a : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ r < 4*q ∧
      a.natAbs.Coprime q ∧
      |4*α-(a:ℝ)/q| ≤ 1/(((N:ℝ)+1)*q) ∧
      |4*α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
  obtain ⟨p, herr, hpN⟩ := Real.exists_rat_abs_sub_le_and_den_le (4*α) hN
  have hp0 : (0:ℝ) < p.den := by exact_mod_cast p.pos
  have hN0 : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hden4 : (p/4).den ≤ 4*p.den := by
    have h := Rat.mul_den_dvd p (1/4)
    norm_num at h
    simpa [div_eq_mul_inv, mul_comm] using Nat.le_of_dvd (by positivity : 0 < p.den*4) h
  have hrq : r < 4*p.den := by
    by_contra h
    have hpr : (p/4).den ≤ r := hden4.trans (by omega)
    apply hminor
    apply rational_mem_majorArcs δ x r (α : AddCircle (1:ℝ)) (p/4) hδ hx hpr
    have hdist : dist (α : AddCircle (1:ℝ)) (((p/4:ℚ):ℝ) : AddCircle (1:ℝ)) ≤
        |4*α-(p:ℝ)|/4 := by
      calc
        _ = ‖((α-((p/4:ℚ):ℝ):ℝ) : AddCircle (1:ℝ))‖ := by
          rw [dist_eq_norm, QuotientAddGroup.mk_sub]
        _ ≤ ‖α-((p/4:ℚ):ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
        _ = |4*α-(p:ℝ)|/4 := by
          rw [Real.norm_eq_abs, Rat.cast_div, Rat.cast_ofNat]
          rw [show α-(p:ℝ)/4 = (4*α-(p:ℝ))/4 by ring, abs_div]
          norm_num
    have hd40 : (0:ℝ) < (p/4).den := by exact_mod_cast (p/4).pos
    have hd4 : ((p/4).den:ℝ) ≤ 4*p.den := by exact_mod_cast hden4
    have hn : 0 ≤ δ*(r:ℝ) := mul_nonneg hδ (Nat.cast_nonneg r)
    calc
      _ ≤ |4*α-(p:ℝ)|/4 := hdist
      _ ≤ (1/(((N:ℝ)+1)*p.den))/4 := div_le_div_of_nonneg_right herr (by norm_num)
      _ < δ*r/(2*(4*p.den)*x) := by
        rw [div_div]
        apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_lt_mul_of_pos_right hscale (by positivity : (0:ℝ) < 4*p.den)]
      _ ≤ δ*r/(2*(p/4).den*x) := by
        apply div_le_div_of_nonneg_left hn (by positivity)
        nlinarith
  refine ⟨p.num,p.den,p.pos,hpN,hrq,p.reduced,?_,?_⟩
  · simpa only [← Rat.cast_def] using herr
  · rw [← Rat.cast_def]
    apply herr.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hpN' : (p.den:ℝ) ≤ N := by exact_mod_cast hpN
    nlinarith

end Helfgott


open Helfgott
set_option maxHeartbeats 800000

namespace Helfgott

theorem etaStar_tao_minorArc_envelope (δ x t α : ℝ) (r N : ℕ)
    (hδ : 0 ≤ δ) (hx : 49 ≤ x) (ht : 0 < t)
    (hmin : (10:ℝ)^20 ≤ x*t/49) (hr : 400 ≤ r) (hN : 0 < N)
    (hscale : 2*x < δ*r*((N:ℝ)+1))
    (hNt : (N:ℝ) ≤ (x*t/49)/100)
    (hminor : (α : AddCircle (1:ℝ)) ∉ majorArcs δ r x) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt ((r:ℝ)/4)
    let B := (16/25:ℝ)/Real.sqrt (X/N)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by
  obtain ⟨a,q,hq0,hqN,hrq,haq,herr,herr2⟩ :=
    minorArc_dirichlet δ x α r N hδ (by linarith) hN hscale hminor
  have hq100 : 100 ≤ q := by omega
  have hqN' : (q:ℝ) ≤ N := by exact_mod_cast hqN
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq0
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hrpos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hXpos : 0 < x/49 := by positivity
  have hrq' : (r:ℝ)/4 ≤ q := by
    have : (r:ℝ) < 4*q := by exact_mod_cast hrq
    linarith
  have hA : (7/50:ℝ)/Real.sqrt q ≤ (7/50:ℝ)/Real.sqrt ((r:ℝ)/4) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt hrq')
  have hB : (16/25:ℝ)/Real.sqrt ((x/49)/q) ≤
      (16/25:ℝ)/Real.sqrt ((x/49)/N) := by
    apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by positivity))
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hXpos.le hqpos hqN')
  have hL : 0 ≤ Real.log (x/49) := Real.log_nonneg (by linarith)
  have hH : 0 ≤ Real.log (x/49)*(Real.log (x/49)+113/10) := by positivity
  have hJ : 0 ≤ 2*Real.log (x/49)+113/10 := by positivity
  have hP : 0 ≤ (Real.log (x/49)*(Real.log (x/49)+113/10)+3)*Real.sqrt (Real.pi/2)+
      2*(2*Real.log (x/49)+113/10) := by positivity
  have hQ : 0 ≤ (2*Real.log (x/49)+113/10)*Real.sqrt (Real.pi/2)+
      Real.log (x/49)*(Real.log (x/49)+113/10)+2 := by positivity
  have hmain := etaStar_tao_gaussian_bound x t α (4*α-(a:ℝ)/q) a q hx ht hmin
    hq100 (hqN'.trans hNt) haq (by ring) herr2
  dsimp only at hmain ⊢
  apply hmain.trans
  apply mul_le_mul_of_nonneg_left _ hXpos.le
  have hD0 : (7/50:ℝ)/Real.sqrt q+(16/25:ℝ)/Real.sqrt ((x/49)/q)/2+
      4*((3/20:ℝ)*(x/49)^(-(1/5:ℝ)))/5 ≤
      (7/50:ℝ)/Real.sqrt ((r:ℝ)/4)+(16/25:ℝ)/Real.sqrt ((x/49)/N)/2+
      4*((3/20:ℝ)*(x/49)^(-(1/5:ℝ)))/5 := by linarith
  have hDm : (16/25:ℝ)/Real.sqrt ((x/49)/q)/2+(3/20:ℝ)*(x/49)^(-(1/5:ℝ))/5 ≤
      (16/25:ℝ)/Real.sqrt ((x/49)/N)/2+(3/20:ℝ)*(x/49)^(-(1/5:ℝ))/5 := by linarith
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hD0 hP)
    (mul_le_mul_of_nonneg_right hDm hQ)) le_rfl

end Helfgott


open Helfgott
set_option maxHeartbeats 800000

namespace Helfgott

theorem etaStar_tao_minorArc_radius (x t α : ℝ) (r : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hr : 400 ≤ r) (hrx : 28*(r:ℝ) ≤ x) (hrt : 1400 ≤ (r:ℝ)*t)
    (hminor : (α : AddCircle (1:ℝ)) ∉ majorArcs 8 r x) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt ((r:ℝ)/4)
    let B := (16/25:ℝ)/Real.sqrt ((r:ℝ)/14)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by
  let N := ⌈x/(4*(r:ℝ))⌉₊
  have hrpos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hxpos : 0 < x := by linarith
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNlo : x/(4*(r:ℝ)) ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < x/(4*(r:ℝ))+1 := Nat.ceil_lt_add_one (by positivity)
  have hNr : (N:ℝ) ≤ 2*x/(7*(r:ℝ)) := by
    have he : x/(4*(r:ℝ))+1 ≤ 2*x/(7*(r:ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < 7*r)).mpr
      field_simp
      nlinarith
    exact hNhi.le.trans he
  have hscale : 2*x < 8*(r:ℝ)*((N:ℝ)+1) := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 4*r)).mp hNlo
    nlinarith
  have hNt : (N:ℝ) ≤ (x*t/49)/100 := by
    apply hNr.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 7*r)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrt hxpos.le]
  have hmain := etaStar_tao_minorArc_envelope 8 x t α r N (by norm_num) hx ht hmin hr hN
    hscale hNt hminor
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hB : (16/25:ℝ)/Real.sqrt ((x/49)/N) ≤ (16/25:ℝ)/Real.sqrt ((r:ℝ)/14) := by
    apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by positivity))
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hNpos).mpr
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 7*r)).mp hNr
    nlinarith
  have hL : 0 ≤ Real.log (x/49) := Real.log_nonneg (by linarith)
  have hH : 0 ≤ Real.log (x/49)*(Real.log (x/49)+113/10) := by positivity
  have hJ : 0 ≤ 2*Real.log (x/49)+113/10 := by positivity
  dsimp only at hmain ⊢
  apply hmain.trans
  gcongr

end Helfgott

open Helfgott
theorem solution (x t α : ℝ) (r : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hr : 400 ≤ r) (hrx : 28*(r:ℝ) ≤ x) (hrt : 1400 ≤ (r:ℝ)*t)
    (hminor : (α : AddCircle (1:ℝ)) ∉ majorArcs 8 r x) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt ((r:ℝ)/4)
    let B := (16/25:ℝ)/Real.sqrt ((r:ℝ)/14)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by
  exact Helfgott.etaStar_tao_minorArc_radius x t α r hx ht hmin hr hrx hrt hminor
