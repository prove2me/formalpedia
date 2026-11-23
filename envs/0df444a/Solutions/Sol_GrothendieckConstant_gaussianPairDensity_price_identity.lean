-- Prove2me | solution 1 for GrothendieckConstant.gaussianPairDensity_price_identity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:02:31.238151+00:00
-- url     : https://prove2.me/submissions/eda33001-e2cc-43fd-8f25-f99600509f8c

import Definitions.Def_KrivineSchemeDefs

open GrothendieckConstant
namespace GaussianPrice

private noncomputable def D (t : ℝ) := 1-t^2
private noncomputable def Q (t x y : ℝ) := x^2-2*t*x*y+y^2
private noncomputable def A (t : ℝ) := 1/(2*Real.pi*Real.sqrt (D t))
private noncomputable def B (t x y : ℝ) := -Q t x y/(2*D t)
private noncomputable def g (t x y : ℝ) := A t * Real.exp (B t x y)

private lemma dD (t : ℝ) : HasDerivAt D (-2*t) t := by
  apply ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).congr_deriv
  dsimp <;> ring
private lemma dA {t : ℝ} (ht : 0 < D t) : HasDerivAt A (A t*t/D t) t := by
  have hp : 2*Real.pi*Real.sqrt (D t) ≠ 0 := by positivity
  have h := (hasDerivAt_const t (1 : ℝ)).div (((dD t).sqrt ht.ne').const_mul (2*Real.pi)) hp
  apply h.congr_deriv
  dsimp only [A]
  set s := Real.sqrt (D t) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsq : s^2=D t := Real.sq_sqrt ht.le
  rw [← hsq]
  field_simp [hs0,Real.pi_ne_zero] <;> ring

private lemma dxB (t x y : ℝ) (ht : D t ≠ 0) :
    HasDerivAt (fun X => B t X y) ((t*y-x)/D t) x := by
  have hQ := (((hasDerivAt_id x).pow 2).sub (((hasDerivAt_id x).const_mul (2*t)).mul_const y)).add_const (y^2)
  apply (hQ.neg.div_const (2*D t)).congr_deriv
  dsimp
  field_simp [ht] <;> ring
private lemma dyB (t x y : ℝ) (ht : D t ≠ 0) :
    HasDerivAt (fun Y => B t x Y) ((t*x-y)/D t) y := by
  have hQ := ((hasDerivAt_const y (x^2)).sub ((hasDerivAt_id y).const_mul (2*t*x))).add ((hasDerivAt_id y).pow 2)
  apply (hQ.neg.div_const (2*D t)).congr_deriv
  dsimp
  field_simp [ht] <;> ring

private lemma dtB (t x y : ℝ) (ht : D t ≠ 0) :
    HasDerivAt (fun s => B s x y) (((t*y-x)*(t*x-y))/(D t)^2) t := by
  have hQ := ((hasDerivAt_const t (x^2)).sub ((((hasDerivAt_id t).const_mul 2).mul_const x).mul_const y)).add_const (y^2)
  apply (hQ.neg.div ((dD t).const_mul 2) (mul_ne_zero (by norm_num) ht)).congr_deriv
  dsimp
  unfold D at *
  field_simp [ht] <;> ring

private lemma dxg (t x y : ℝ) (ht : D t ≠ 0) :
    HasDerivAt (fun X => g t X y) (g t x y * ((t*y-x)/D t)) x := by
  apply ((dxB t x y ht).exp.const_mul (A t)).congr_deriv
  dsimp [g]; ring
private lemma dyg (t x y : ℝ) (ht : D t ≠ 0) :
    HasDerivAt (fun Y => g t x Y) (g t x y * ((t*x-y)/D t)) y := by
  apply ((dyB t x y ht).exp.const_mul (A t)).congr_deriv
  dsimp [g]; ring

private lemma mixed (t x y : ℝ) (ht : 0 < D t) :
    deriv (fun s => g s x y) t = deriv (fun X => deriv (fun Y => g t X Y) y) x := by
  have ht' := ht.ne'
  have H := (dA ht).mul (dtB t x y ht').exp
  have hY : (fun X => deriv (fun Y => g t X Y) y) = (fun X => g t X y*((t*X-y)/D t)) :=
    funext fun X => (dyg t X y ht').deriv
  have hlin := (((hasDerivAt_id x).const_mul t).sub_const y).div_const (D t)
  rw [hY, (show deriv (fun s => g s x y) t = _ from H.deriv), (show deriv (fun X => g t X y*((t*X-y)/D t)) x = _ from ((dxg t x y ht').mul hlin).deriv)]
  dsimp [g]
  field_simp [ht'] <;> ring
end GaussianPrice

open GaussianPrice
theorem solution (t x y : ℝ) (ht : |t| < 1) :
    deriv (fun s : ℝ => gaussianPairDensity 1 s ![x] ![y]) t =
      deriv (fun u : ℝ => deriv (fun v : ℝ => gaussianPairDensity 1 t ![u] ![v]) y) x := by
  have hD : 0 < D t := by
    obtain ⟨h₁,h₂⟩ := abs_lt.mp ht
    unfold D
    nlinarith only [mul_pos (sub_pos.mpr h₂) (show 0 < 1+t by linarith)]
  simpa only [gaussianPairDensity,Fin.prod_univ_one,Matrix.cons_val_zero,g,A,B,D,Q] using mixed t x y hD
