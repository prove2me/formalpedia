-- Prove2me | solution 1 for HunterPDE.Shared.integral_evenReflection_mul_testFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T18:23:09.669787+00:00
-- url     : https://prove2.me/submissions/6d54e96a-1a43-41ef-886b-62c9983ec7ee

import Theorems.Thm_MeasureTheory_integral_signed_coordinate_fold
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_boundaryCompatible
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Shared
open scoped ENNReal NNReal ContDiff
set_option autoImplicit false

namespace EvenReflectionTest

lemma list_single {n : ℕ} (i : Fin n) (l : List (Fin n)) (hl : l.Nodup) :
    l.flatMap (fun j => List.replicate ((Pi.single i 1 : Fin n → ℕ) j) j) =
      if i ∈ l then [i] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := (List.nodup_cons.mp hl).1
    have hh := ih (List.nodup_cons.mp hl).2
    by_cases h : a = i
    · subst a
      simp [List.flatMap_cons, hh, ha]
    · simp [List.flatMap_cons, hh, h, Ne.symm h]

lemma multi_single {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    multiDeriv φ (Pi.single i 1) = partialDeriv φ i := by
  unfold multiDeriv multiIndexList
  rw [list_single i (List.finRange n) (List.nodup_finRange n)]
  simp [iteratedPartial]

end EvenReflectionTest

theorem solution (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (i : Fin (m + 1)) (f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : MemLp f p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hg : MemLp g p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hd : HunterPDE.Shared.HasWeakDeriv (HunterPDE.Compactness.upperHalfSpace m)
      (Pi.single i 1) f g)
    (φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hφ : HunterPDE.Shared.IsTestFunction Set.univ φ) :
    (∫ x : EuclideanSpace ℝ (Fin (m + 1)),
      (if i = Fin.last m ∧ x (Fin.last m) < 0 then
        -g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))
       else g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))) * φ x) =
    -(∫ x : EuclideanSpace ℝ (Fin (m + 1)),
      f (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j)) *
        HunterPDE.Shared.multiDeriv φ (Pi.single i 1) x) := by
  classical
  let S : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
      if j = Fin.last m then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)
  have hS (x : EuclideanSpace ℝ (Fin (m + 1))) (j : Fin (m + 1)) :
      S x j = if j = Fin.last m then -x j else x j := by
    by_cases hj : j = Fin.last m <;>
      simp [S, LinearIsometryEquiv.piLpCongrRight_apply, hj]
  have hs (x : EuclideanSpace ℝ (Fin (m + 1))) :
      S x = WithLp.toLp 2 (fun j => if j = Fin.last m then -x j else x j) := by
    ext j; exact hS x j
  let c : ℝ := if i = Fin.last m then -1 else 1
  have hc : c * c = 1 := by unfold c; split <;> norm_num
  let ψ := fun x => φ x + c * φ (S x)
  have hψ : IsTestFunction Set.univ ψ :=
    ⟨hφ.1.add (contDiff_const.mul (hφ.1.comp S.contDiff)),
      hφ.2.1.add ((hφ.2.1.comp_homeomorph S.toHomeomorph).mul_left),
      Set.subset_univ _⟩
  have hb : i = Fin.last m → ∀ x, x (Fin.last m) = 0 → ψ x = 0 := by
    intro hi x hx
    have hfix : S x = x := by
      ext j
      by_cases hj : j = Fin.last m <;> simp [hS, hj, hx]
    simp [ψ, c, hi, hfix]
  have hSi : S (EuclideanSpace.single i (1 : ℝ)) =
      c • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i
    · subst j
      by_cases hi : i = Fin.last m <;> simp [hS, c, hi]
    · simp [hS, hj]
  have hdψ (x : EuclideanSpace ℝ (Fin (m + 1))) :
      multiDeriv ψ (Pi.single i 1) x =
        multiDeriv φ (Pi.single i 1) x + multiDeriv φ (Pi.single i 1) (S x) := by
    simp only [EvenReflectionTest.multi_single, partialDeriv]
    have hdiff := hφ.1.differentiable (by simp)
    have hchain := (hdiff (S x)).hasFDerivAt.comp x S.toContinuousLinearEquiv.hasFDerivAt
    have hsum := (hdiff x).hasFDerivAt.add (hchain.const_mul c)
    change (fderiv ℝ (φ + fun y => c * (φ ∘ S) y) x) _ = _
    rw [hsum.fderiv]
    change (fderiv ℝ φ x) (EuclideanSpace.single i 1) +
      c * (fderiv ℝ φ (S x)) (S (EuclideanSpace.single i 1)) = _
    rw [hSi, map_smul]
    simp only [smul_eq_mul, ← mul_assoc, hc, one_mul]
  have hfL := hf.locallyIntegrable hp
  have hgL := hg.locallyIntegrable hp
  have hboundary := HasWeakDeriv.integral_mul_boundaryCompatible m i f g ψ hfL hgL hd hψ hb
  have hleft := MeasureTheory.integral_signed_coordinate_fold (m + 1) (Fin.last m)
    c g φ hgL hφ.1.continuous hφ.2.1
  have hdcont : ContDiff ℝ ∞ (multiDeriv φ (Pi.single i 1)) := by
    rw [EvenReflectionTest.multi_single]
    exact (hφ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  have hdcompact : HasCompactSupport (multiDeriv φ (Pi.single i 1)) := by
    rw [EvenReflectionTest.multi_single]
    exact HasCompactSupport.fderiv_apply ℝ hφ.2.1 (EuclideanSpace.single i 1)
  have hright := MeasureTheory.integral_signed_coordinate_fold (m + 1) (Fin.last m)
    1 f (multiDeriv φ (Pi.single i 1)) hfL hdcont.continuous hdcompact
  have hleft' : (∫ x : EuclideanSpace ℝ (Fin (m + 1)),
      (if i = Fin.last m ∧ x (Fin.last m) < 0 then
        -g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))
       else g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))) * φ x) =
      ∫ x in HunterPDE.Compactness.upperHalfSpace m, g x * ψ x := by
    convert hleft using 1
    · congr 1; funext x
      by_cases hi : i = Fin.last m <;> by_cases hx : x (Fin.last m) < 0 <;>
        simp [c, hi, hx]
    · apply integral_congr_ae
      filter_upwards [] with x
      simp [ψ, hs]
  rw [hleft', hboundary]
  congr 1
  calc
    (∫ x in HunterPDE.Compactness.upperHalfSpace m, f x * multiDeriv ψ (Pi.single i 1) x) =
        ∫ x in HunterPDE.Compactness.upperHalfSpace m,
          f x * (multiDeriv φ (Pi.single i 1) x + multiDeriv φ (Pi.single i 1) (S x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hdψ]
    _ = _ := by simpa only [one_mul, hs, HunterPDE.Compactness.upperHalfSpace,
      ite_self] using hright.symm


