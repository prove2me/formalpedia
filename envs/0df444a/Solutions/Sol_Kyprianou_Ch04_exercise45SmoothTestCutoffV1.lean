-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45SmoothTestCutoffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:44:31.030784+00:00
-- url     : https://prove2.me/submissions/4c8f2a64-3dc9-4179-9d6c-a0a49bcc6f29

import Theorems.Thm_Kyprianou_Ch04_exercise45SmoothProductJetV1
import Theorems.Thm_Kyprianou_Ch04_exercise45SmoothPlateauJetV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CompactHalfplaneBoundV1
import Mathlib
open Set Kyprianou.Ch04
open scoped ContDiff
set_option autoImplicit false
theorem solution :
∀
    (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real,
      fTime s x = deriv (fun u : Real => f u x) s)
    (hSpace : ∀ s x : Real,
      fSpace s x = deriv (fun u : Real => f s u) x)
    (hSpace2 : ∀ s x : Real,
      fSpace2 s x = deriv (fun u : Real => fSpace s u) x)
    (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x))
    (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fTime z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ))
    (n : ℕ),
    ∃ (g gt gx gxx : ℝ → ℝ → ℝ) (K : ℝ),
      0 < K ∧
      (∀ s x, gt s x = deriv (fun u : ℝ => g u x) s) ∧
      (∀ s x, gx s x = deriv (fun u : ℝ => g s u) x) ∧
      (∀ s x, gxx s x = deriv (fun u : ℝ => gx s u) x) ∧
      (∀ x, ContDiff ℝ 1 (fun s => g s x)) ∧
      (∀ s, ContDiff ℝ 2 (fun x => g s x)) ∧
      (ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gt z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
       ContinuousOn (fun z : ℝ × ℝ => gxx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) ∧
      (∀ s x, 0 ≤ s → |g s x| ≤ K ∧ |gt s x| ≤ K ∧ |gx s x| ≤ K ∧ |gxx s x| ≤ K) ∧
      (∀ s x, 0 ≤ s → s ≤ (n : ℝ) → |x| ≤ (n : ℝ) →
        g s x = f s x ∧ gt s x = fTime s x ∧ gx s x = fSpace s x ∧ gxx s x = fSpace2 s x)
 := by
  intro f ft fx fxx hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint n
  obtain ⟨b,hb,hInner,hOuter⟩ := exercise45SmoothPlateauJetV1 (n : ℝ) (by positivity)
  let g (s x : ℝ) := b s * (b x * f s x)
  let gt (s x : ℝ) := deriv b s * (b x * f s x) + b s * (b x * ft s x)
  let gx (s x : ℝ) := b s * (deriv b x * f s x + b x * fx s x)
  let gxx (s x : ℝ) := b s * (deriv (deriv b) x * f s x + deriv b x * fx s x +
    (deriv b x * fx s x + b x * fxx s x))
  obtain ⟨hgT,hgX,hgXX,hST,hSX,cg,cgt,cgx,cgxx⟩ :=
    exercise45SmoothProductJetV1 f ft fx fxx hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint b hb
  let q (s x : ℝ) := |g s x| + |gt s x| + |gx s x| + |gxx s x|
  have cq : ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) :=
    ((cg.abs.add cgt.abs).add cgx.abs).add cgxx.abs
  have hz (s x : ℝ) (hs : 0 ≤ s) (ho : (n : ℝ)+3 < s ∨ (n : ℝ)+3 < |x|) :
      q s x = 0 := by
    rcases ho with ho|ho
    · obtain ⟨h1,h2,h3⟩ := hOuter s (by rwa [abs_of_nonneg hs])
      simp [q,g,gt,gx,gxx,h1,h2]
    · obtain ⟨h1,h2,h3⟩ := hOuter x ho
      simp [q,g,gt,gx,gxx,h1,h2,h3]
  obtain ⟨K,hK,hbound⟩ := exercise45CompactHalfplaneBoundV1 q ((n : ℝ)+3)
    (by positivity) cq hz
  refine ⟨g,gt,gx,gxx,K,hK,hgT,hgX,hgXX,hST,hSX,⟨cg,cgt,cgx,cgxx⟩,?_,?_⟩
  · intro s x hs
    have h := hbound s x hs
    dsimp only [q] at h
    have h' := le_trans (le_abs_self (|g s x| + |gt s x| + |gx s x| + |gxx s x|)) h
    exact ⟨by linarith [abs_nonneg (gt s x),abs_nonneg (gx s x),abs_nonneg (gxx s x)],
      by linarith [abs_nonneg (g s x),abs_nonneg (gx s x),abs_nonneg (gxx s x)],
      by linarith [abs_nonneg (g s x),abs_nonneg (gt s x),abs_nonneg (gxx s x)],
      by linarith [abs_nonneg (g s x),abs_nonneg (gt s x),abs_nonneg (gx s x)]⟩
  · intro s x hs hsn hx
    obtain ⟨h1,h2,h3⟩ := hInner s (by rwa [abs_of_nonneg hs])
    obtain ⟨h4,h5,h6⟩ := hInner x hx
    simp [g,gt,gx,gxx,h1,h2,h4,h5,h6]
