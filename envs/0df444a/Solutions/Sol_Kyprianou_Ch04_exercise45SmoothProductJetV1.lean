-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45SmoothProductJetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:44:58.737839+00:00
-- url     : https://prove2.me/submissions/0521f71e-be72-462a-8bf1-e8165b9b10b8

import Mathlib
open Set
open scoped ContDiff
set_option autoImplicit false
theorem solution :
  ∀ (f fTime fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun
  u : Real => f u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x)
  (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x
  : Real, ContDiff Real 1 (fun s => f s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x =>
  f s x)) (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ
  Set.univ) ∧ ContinuousOn (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)
  ∧ ContinuousOn (fun z : Real × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
  ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (b : ℝ →
  ℝ) (hb : ContDiff ℝ (↑(⊤ : ℕ∞)) b),
    let g (s x : ℝ) := b s * (b x * f s x)
    let gt (s x : ℝ) := deriv b s * (b x * f s x) + b s * (b x * fTime s x)
    let gx (s x : ℝ) := b s * (deriv b x * f s x + b x * fSpace s x)
    let gxx (s x : ℝ) := b s * (deriv (deriv b) x * f s x + deriv b x * fSpace s x +
      (deriv b x * fSpace s x + b x * fSpace2 s x))
    (∀ s x, gt s x = deriv (fun u : ℝ => g u x) s) ∧
    (∀ s x, gx s x = deriv (fun u : ℝ => g s u) x) ∧
    (∀ s x, gxx s x = deriv (fun u : ℝ => gx s u) x) ∧
    (∀ x, ContDiff ℝ 1 (fun s => g s x)) ∧
    (∀ s, ContDiff ℝ 2 (fun x => g s x)) ∧
    (ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gt z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
     ContinuousOn (fun z : ℝ × ℝ => gxx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) := by
  intro f ft fx fxx hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint b hb g gt gx gxx
  have hbd := (contDiff_infty_iff_deriv.mp hb).2
  have hbdd := (contDiff_infty_iff_deriv.mp hbd).2
  have hbdAt (x : ℝ) : HasDerivAt b (deriv b x) x :=
    ((contDiff_infty_iff_deriv.mp hb).1 x).hasDerivAt
  have hbddAt (x : ℝ) : HasDerivAt (deriv b) (deriv (deriv b) x) x :=
    ((contDiff_infty_iff_deriv.mp hbd).1 x).hasDerivAt
  have hfT (s x : ℝ) : HasDerivAt (fun u => f u x) (ft s x) s := by
    rw [hTime]
    exact ((hSmoothTime x).differentiable (by norm_num) s).hasDerivAt
  have hfX (s x : ℝ) : HasDerivAt (f s) (fx s x) x := by
    rw [hSpace]
    exact ((hSmoothSpace s).differentiable (by norm_num) x).hasDerivAt
  have hfXX (s x : ℝ) : HasDerivAt (fx s) (fxx s x) x := by
    rw [hSpace2]
    have he : fx s = deriv (f s) := funext (hSpace s)
    rw [he]
    exact ((hSmoothSpace s).differentiable_deriv_two x).hasDerivAt
  have hgT (s x : ℝ) : gt s x = deriv (fun u => g u x) s :=
    ((hbdAt s).mul ((hfT s x).const_mul (b x))).deriv.symm
  have hgX (s x : ℝ) : gx s x = deriv (g s) x :=
    (((hbdAt x).mul (hfX s x)).const_mul (b s)).deriv.symm
  have hgXX (s x : ℝ) : gxx s x = deriv (gx s) x :=
    ((((hbddAt x).mul (hfX s x)).add ((hbdAt x).mul (hfXX s x))).const_mul
      (b s)).deriv.symm
  have hST (x : ℝ) : ContDiff ℝ 1 (fun s => g s x) :=
    (hb.of_le (by exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul (contDiff_const.mul (hSmoothTime x))
  have hSX (s : ℝ) : ContDiff ℝ 2 (g s) :=
    contDiff_const.mul ((hb.of_le (by
      change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).mul (hSmoothSpace s))
  let A : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ univ
  have cb1 : ContinuousOn (fun z : ℝ × ℝ => b z.1) A :=
    (hb.continuous.comp continuous_fst).continuousOn
  have cb2 : ContinuousOn (fun z : ℝ × ℝ => b z.2) A :=
    (hb.continuous.comp continuous_snd).continuousOn
  have cd1 : ContinuousOn (fun z : ℝ × ℝ => deriv b z.1) A :=
    (hbd.continuous.comp continuous_fst).continuousOn
  have cd2 : ContinuousOn (fun z : ℝ × ℝ => deriv b z.2) A :=
    (hbd.continuous.comp continuous_snd).continuousOn
  have cdd2 : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv b) z.2) A :=
    (hbdd.continuous.comp continuous_snd).continuousOn
  have cg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) A :=
    cb1.mul (cb2.mul hJoint.1)
  have cgt : ContinuousOn (fun z : ℝ × ℝ => gt z.1 z.2) A :=
    (cd1.mul (cb2.mul hJoint.1)).add (cb1.mul (cb2.mul hJoint.2.1))
  have cgx : ContinuousOn (fun z : ℝ × ℝ => gx z.1 z.2) A :=
    cb1.mul ((cd2.mul hJoint.1).add (cb2.mul hJoint.2.2.1))
  have cgxx : ContinuousOn (fun z : ℝ × ℝ => gxx z.1 z.2) A :=
    cb1.mul (((cdd2.mul hJoint.1).add (cd2.mul hJoint.2.2.1)).add
      ((cd2.mul hJoint.2.2.1).add (cb2.mul hJoint.2.2.2)))
  exact ⟨hgT,hgX,hgXX,hST,hSX,cg,cgt,cgx,cgxx⟩
