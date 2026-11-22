-- Prove2me | solution 1 for NoHair.Weyl.ernst_deviation_subharmonic
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:12:19.257818+00:00
-- url     : https://prove2.me/submissions/078df97f-8668-4036-b283-a035eaa41f21

import Definitions.Def_NoHair_vacuumErnst
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open NoHair.Weyl

noncomputable section

private def direction (i : OrbitPoint) (f : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ :=
  fderiv ℝ f p i

private theorem diff_direction (i : OrbitPoint) {f : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (direction i f) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
    (show ContDiff ℝ 1 (fun _ : OrbitPoint => i) from contDiff_const)).differentiable_one

private theorem dir_add (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q + g q) = fun q => direction i f q + direction i g q := by
  funext q
  simp [direction, fderiv_fun_add (hf q) (hg q)]

private theorem dir_sub (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q - g q) = fun q => direction i f q - direction i g q := by
  funext q
  simp [direction, fderiv_fun_sub (hf q) (hg q)]

private theorem dir_mul (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q * g q) = fun q => direction i f q * g q + f q * direction i g q := by
  funext q
  simp only [direction, fderiv_fun_mul (hf q) (hg q), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private def weight (p : OrbitPoint) := Real.exp (2 * p.1)

/-- A value, its two first partials, and its scaled Laplacian at one point. -/
@[ext] private structure Jet where
  value : ℝ
  s : ℝ
  z : ℝ
  lap : ℝ

private def jetAt (p : OrbitPoint) (f : OrbitPoint → ℝ) : Jet :=
  ⟨f p, direction (1,0) f p, direction (0,1) f p,
    direction (1,0) (direction (1,0) f) p + weight p * direction (0,1) (direction (0,1) f) p⟩

private def addJ (a b : Jet) : Jet := ⟨a.value+b.value, a.s+b.s, a.z+b.z, a.lap+b.lap⟩

private def subJ (a b : Jet) : Jet := ⟨a.value-b.value, a.s-b.s, a.z-b.z, a.lap-b.lap⟩

private def mulJ (w : ℝ) (a b : Jet) : Jet :=
  ⟨a.value*b.value, a.s*b.value+a.value*b.s, a.z*b.value+a.value*b.z,
    a.lap*b.value+a.value*b.lap+2*(a.s*b.s+w*a.z*b.z)⟩

private def divJ (w : ℝ) (a b : Jet) : Jet :=
  let v := a.value/b.value
  let s := (a.s-v*b.s)/b.value
  let z := (a.z-v*b.z)/b.value
  ⟨v,s,z,(a.lap-v*b.lap-2*(s*b.s+w*z*b.z))/b.value⟩

private theorem jet_add {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q + g q) = addJ (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q + g q)) p =
      direction i (direction i f) p + direction i (direction i g) p := by
    rw [dir_add i fd gd, dir_add i (diff_direction i hf) (diff_direction i hg)]
  apply Jet.ext
  · rfl
  · exact congrFun (dir_add _ fd gd) p
  · exact congrFun (dir_add _ fd gd) p
  · dsimp only [jetAt, addJ]
    simp only [twice]
    ring

private theorem jet_sub {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q - g q) = subJ (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q - g q)) p =
      direction i (direction i f) p - direction i (direction i g) p := by
    rw [dir_sub i fd gd, dir_sub i (diff_direction i hf) (diff_direction i hg)]
  apply Jet.ext
  · rfl
  · exact congrFun (dir_sub _ fd gd) p
  · exact congrFun (dir_sub _ fd gd) p
  · dsimp only [jetAt, subJ]
    simp only [twice]
    ring

private theorem jet_mul {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q * g q) = mulJ (weight p) (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q * g q)) p =
      direction i (direction i f) p * g p + f p * direction i (direction i g) p +
      2 * direction i f p * direction i g p := by
    rw [dir_mul i fd gd, dir_add i ((diff_direction i hf).fun_mul gd) (fd.fun_mul (diff_direction i hg)),
      dir_mul i (diff_direction i hf) gd, dir_mul i fd (diff_direction i hg)]
    ring
  apply Jet.ext
  · rfl
  · exact congrFun (dir_mul _ fd gd) p
  · exact congrFun (dir_mul _ fd gd) p
  · dsimp only [jetAt, mulJ]
    simp only [twice]
    ring

private theorem quotient_of_product {w : ℝ} {a b q : Jet} (hb : b.value ≠ 0)
    (hm : mulJ w q b = a) : q = divJ w a b := by
  subst a
  cases q
  cases b
  dsimp at hb
  apply Jet.ext <;> dsimp [divJ, mulJ] <;> field_simp [hb] <;> ring

private theorem jet_div {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hn : ∀ q, g q ≠ 0) (p : OrbitPoint) :
    jetAt p (fun q => f q / g q) = divJ (weight p) (jetAt p f) (jetAt p g) := by
  have he : (fun q => f q / g q * g q) = f := funext fun q => div_mul_cancel₀ _ (hn q)
  apply quotient_of_product (hn p)
  exact (jet_mul (hf.div hg hn) hg p).symm.trans (congrArg (jetAt p) he)

private def comparisonJet (w : ℝ) (a b c d : Jet) : Jet :=
  let x := subJ a c
  let y := subJ b d
  divJ w (addJ (mulJ w x x) (mulJ w y y)) (mulJ w a c)

private theorem jet_deviation {u v : ErnstPotentials} (hu : u.IsSolution) (hv : v.IsSolution)
    (p : OrbitPoint) : jetAt p (deviation u v) = comparisonJet (weight p)
      (jetAt p u.normSq) (jetAt p u.twist) (jetAt p v.normSq) (jetAt p v.twist) := by
  have hx := hu.1.sub hv.1
  have hy := hu.2.1.sub hv.2.1
  have hxx := hx.mul hx
  have hyy := hy.mul hy
  have hn (q : OrbitPoint) := mul_ne_zero (hu.2.2 q).1.ne' (hv.2.2 q).1.ne'
  change jetAt p (fun q => ((u.normSq q-v.normSq q)^2+(u.twist q-v.twist q)^2) /
    (u.normSq q*v.normSq q)) = _
  simp only [pow_two, comparisonJet]
  rw [jet_div (hxx.add hyy) (hu.1.mul hv.1) hn p, jet_add hxx hyy p,
    jet_mul hx hx p, jet_mul hy hy p, jet_mul hu.1 hv.1 p,
    jet_sub hu.1 hv.1 p, jet_sub hu.2.1 hv.2.1 p]

private def normJet (w x xs xz ys yz : ℝ) : Jet :=
  ⟨x, xs, xz, ((xs*xs+w*xz*xz) - (ys*ys+w*yz*yz))/x⟩

private def twistJet (w x y xs xz ys yz : ℝ) : Jet :=
  ⟨y, ys, yz, 2*(xs*ys+w*xz*yz)/x⟩

private theorem field_equations {u : ErnstPotentials} (hu : u.IsSolution) (p : OrbitPoint) :
    jetAt p u.normSq = normJet (weight p) (u.normSq p)
      (ds u.normSq p) (dz u.normSq p) (ds u.twist p) (dz u.twist p) ∧
    jetAt p u.twist = twistJet (weight p) (u.normSq p) (u.twist p)
      (ds u.normSq p) (dz u.normSq p) (ds u.twist p) (dz u.twist p) := by
  obtain ⟨hpos, hn, ht⟩ := hu.2.2 p
  constructor
  · apply Jet.ext <;> try rfl
    apply (eq_div_iff hpos.ne').2
    rw [mul_comm]
    exact hn
  · apply Jet.ext <;> try rfl
    apply (eq_div_iff hpos.ne').2
    rw [mul_comm]
    exact ht

/-- The squared entries of the difference of the two matrix currents in orthonormal frames. -/
private def currentSquares (a c t u v x y : ℝ) : ℝ :=
  (a*(u-x)+t*v)^2 + (a*v-c*y-t*(u+x))^2 + (c*v-a*y)^2 + (c*(x-u)-t*y)^2

set_option maxHeartbeats 4000000 in
private theorem mazur_nonneg (w a b c d as₁ az bs bz cs cz ds₁ dz₁ : ℝ)
    (hw : 0 ≤ w) (ha : 0 < a) (hc : 0 < c) :
    0 ≤ (comparisonJet w (normJet w a as₁ az bs bz) (twistJet w a b as₁ az bs bz)
      (normJet w c cs cz ds₁ dz₁) (twistJet w c d cs cz ds₁ dz₁)).lap := by
  have identity :
      (comparisonJet w (normJet w a as₁ az bs bz) (twistJet w a b as₁ az bs bz)
        (normJet w c cs cz ds₁ dz₁) (twistJet w c d cs cz ds₁ dz₁)).lap =
      (currentSquares a c (b-d) (as₁/a) (bs/a) (cs/c) (ds₁/c) +
        w * currentSquares a c (b-d) (az/a) (bz/a) (cz/c) (dz₁/c)) / (a*c) := by
    dsimp [comparisonJet, addJ, subJ, mulJ, divJ, normJet, twistJet, currentSquares]
    field_simp [ha.ne', hc.ne']
    ring
  rw [identity]
  unfold currentSquares
  positivity

theorem solution (u v : ErnstPotentials) (hu : u.IsSolution) (hv : v.IsSolution) :
    ContDiff ℝ 2 (deviation u v) ∧ ∀ p, 0 ≤ scaledLaplacian (deviation u v) p := by
  constructor
  · exact (((hu.1.sub hv.1).pow 2).add ((hu.2.1.sub hv.2.1).pow 2)).div
      (hu.1.mul hv.1) (fun q => mul_ne_zero (hu.2.2 q).1.ne' (hv.2.2 q).1.ne')
  · intro p
    change 0 ≤ (jetAt p (deviation u v)).lap
    obtain ⟨huX, huY⟩ := field_equations hu p
    obtain ⟨hvX, hvY⟩ := field_equations hv p
    rw [jet_deviation hu hv, huX, huY, hvX, hvY]
    exact mazur_nonneg (weight p) (u.normSq p) (u.twist p) (v.normSq p) (v.twist p)
      (ds u.normSq p) (dz u.normSq p) (ds u.twist p) (dz u.twist p)
      (ds v.normSq p) (dz v.normSq p) (ds v.twist p) (dz v.twist p)
      (Real.exp_pos _).le (hu.2.2 p).1 (hv.2.2 p).1
