-- Prove2me | solution 1 for NewtonCartan.exists_potential_of_closed_hessian_Sp
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:00:02.777542+00:00
-- url     : https://prove2.me/submissions/cbc5fb45-6b01-48b7-999a-f17286aa2a23


import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Theorems.Thm_NewtonCartan_contDiff_primitive_of_closed_oneForm

open scoped ContDiff BigOperators Topology
open Classical
open NewtonCartan

abbrev Sp := Fin 3 → ℝ

noncomputable def eProj (j : Fin 3) : Sp →L[ℝ] ℝ := ContinuousLinearMap.proj j

noncomputable def rowForm (H : Sp → Fin 3 → Fin 3 → ℝ) (i : Fin 3) : Sp → Sp →L[ℝ] ℝ :=
  fun y => ∑ j : Fin 3, H y i j • eProj j

private lemma contDiff_Hij (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun y : Sp => H y i j) :=
  (contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 3) j).comp
    ((contDiff_apply (𝕜 := ℝ) (E := Fin 3 → ℝ) (ι := Fin 3) i).comp hH)

lemma fderiv_rowForm_apply (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin 3) (a x y : Sp) :
    (fderiv ℝ (rowForm H i) a x) y =
      ∑ j : Fin 3, fderiv ℝ (fun z => H z i j) a x * y j := by
  have hdiff (j : Fin 3) : DifferentiableAt ℝ (fun z : Sp => H z i j) a :=
    (contDiff_Hij H hH i j).differentiable (by simp) |>.differentiableAt
  have hterm (j : Fin 3) :
      fderiv ℝ (fun z : Sp => (H z i j) • eProj j) a =
        (fderiv ℝ (fun z => H z i j) a).smulRight (eProj j) :=
    fderiv_smul_const (hdiff j) (eProj j)
  have hsum :
      (fderiv ℝ (rowForm H i) a x) y =
        ∑ j : Fin 3, (fderiv ℝ (fun z : Sp => (H z i j) • eProj j) a x) y := by
    unfold rowForm
    have hs := fderiv_fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (fun j _ => (hdiff j).smul_const (eProj j))
    rw [hs]
    simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hterm j]
  simp [ContinuousLinearMap.smulRight_apply, eProj, ContinuousLinearMap.proj_apply, smul_eq_mul]

lemma closed_rowForm (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (hclosed : ∀ y i j k,
      fderiv ℝ (fun z => H z i j) y (Pi.single k 1) =
        fderiv ℝ (fun z => H z i k) y (Pi.single j 1))
    (i : Fin 3) (a x y : Sp) :
    (fderiv ℝ (rowForm H i) a x) y = (fderiv ℝ (rowForm H i) a y) x := by
  rw [fderiv_rowForm_apply H hH i, fderiv_rowForm_apply H hH i]
  let G (j : Fin 3) : Sp →L[ℝ] ℝ := fderiv ℝ (fun z => H z i j) a
  -- Freeze components
  let cx k : ℝ := x k
  let cy m : ℝ := y m
  have hcx : ∀ k, cx k = x k := fun _ => rfl
  have hcy : ∀ m, cy m = y m := fun _ => rfl
  have hx : x = ∑ k : Fin 3, cx k • Pi.single k (1 : ℝ) := by
    ext m; simp [cx, Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ m : Fin 3, cy m • Pi.single m (1 : ℝ) := by
    ext m; simp [cy, Finset.sum_apply, Pi.single_apply]
  have Gx (j : Fin 3) : G j x = ∑ k : Fin 3, cx k * G j (Pi.single k 1) := by
    calc G j x
        = G j (∑ k : Fin 3, cx k • Pi.single k (1 : ℝ)) := by rw [hx]
      _ = ∑ k : Fin 3, G j (cx k • Pi.single k (1 : ℝ)) := by rw [map_sum]
      _ = ∑ k : Fin 3, cx k * G j (Pi.single k 1) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul, smul_eq_mul]
  have Gy (j : Fin 3) : G j y = ∑ m : Fin 3, cy m * G j (Pi.single m 1) := by
    calc G j y
        = G j (∑ m : Fin 3, cy m • Pi.single m (1 : ℝ)) := by rw [hy]
      _ = ∑ m : Fin 3, G j (cy m • Pi.single m (1 : ℝ)) := by rw [map_sum]
      _ = ∑ m : Fin 3, cy m * G j (Pi.single m 1) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, smul_eq_mul]
  -- Goal: ∑ j, G j x * y j = ∑ j, G j y * x j
  have key : ∑ j : Fin 3, G j x * cy j = ∑ j : Fin 3, G j y * cx j := by
    calc ∑ j : Fin 3, G j x * cy j
        = ∑ j : Fin 3, (∑ k : Fin 3, cx k * G j (Pi.single k 1)) * cy j := by
            exact Finset.sum_congr rfl fun j _ => by rw [Gx j]
      _ = ∑ j : Fin 3, ∑ k : Fin 3, (cx k * G j (Pi.single k 1)) * cy j := by
            exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
      _ = ∑ j : Fin 3, ∑ k : Fin 3, cx k * cy j * G j (Pi.single k 1) := by
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ j : Fin 3, ∑ k : Fin 3, cx k * cy j * G k (Pi.single j 1) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            dsimp [G]; rw [hclosed a i j k]
      _ = ∑ k : Fin 3, ∑ j : Fin 3, cy j * cx k * G k (Pi.single j 1) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k : Fin 3, ∑ j : Fin 3, (cy j * G k (Pi.single j 1)) * cx k := by
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k : Fin 3, (∑ j : Fin 3, cy j * G k (Pi.single j 1)) * cx k := by
            exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ k : Fin 3, G k y * cx k := by
            exact Finset.sum_congr rfl fun k _ => by rw [← Gy k]
      _ = ∑ j : Fin 3, G j y * cx j := rfl
  -- cy/cx are definitionally y/x via let
  simpa [cx, cy] using key

private lemma contDiff_rowForm (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin 3) : ContDiff ℝ ∞ (rowForm H i) :=
  ContDiff.sum fun j _ => (contDiff_Hij H hH i j).smul_const (eProj j)

theorem solution (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (hsym : ∀ y i j, H y i j = H y j i)
    (hclosed : ∀ y i j k,
      fderiv ℝ (fun z => H z i j) y (Pi.single k 1) =
        fderiv ℝ (fun z => H z i k) y (Pi.single j 1)) :
    ∃ φ : Sp → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ y i j, fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single i 1)) y (Pi.single j 1) =
        H y i j := by
  have hA (i : Fin 3) :=
    contDiff_primitive_of_closed_oneForm (rowForm H i)
      (contDiff_rowForm H hH i)
      (fun a x y => closed_rowForm H hH hclosed i a x y)
  choose A hAcont hAder using hA
  -- alpha(y) = ∑ i, A i y • eProj i
  let alpha : Sp → Sp →L[ℝ] ℝ := fun y => ∑ i : Fin 3, A i y • eProj i
  have hαCont : ContDiff ℝ ∞ alpha :=
    ContDiff.sum fun i _ => (hAcont i).smul_const (eProj i)
  have hαClosed : ∀ a x y, (fderiv ℝ alpha a x) y = (fderiv ℝ alpha a y) x := by
    intro a x y
    -- Mimic fderiv_rowForm_apply for alpha, then use symmetry of H
    have hAdiff (i : Fin 3) : DifferentiableAt ℝ (A i) a := (hAder i a).differentiableAt
    have hterm (i : Fin 3) :
        fderiv ℝ (fun z : Sp => A i z • eProj i) a =
          (fderiv ℝ (A i) a).smulRight (eProj i) :=
      fderiv_smul_const (hAdiff i) (eProj i)
    have hsumx :
        (fderiv ℝ alpha a x) y =
          ∑ i : Fin 3, (fderiv ℝ (fun z : Sp => A i z • eProj i) a x) y := by
      dsimp [alpha]
      have hs := fderiv_fun_sum (u := (Finset.univ : Finset (Fin 3)))
        (fun i _ => (hAdiff i).smul_const (eProj i))
      rw [hs]; simp only [FunLike.coe_sum, Finset.sum_apply]
    have hsumy :
        (fderiv ℝ alpha a y) x =
          ∑ i : Fin 3, (fderiv ℝ (fun z : Sp => A i z • eProj i) a y) x := by
      dsimp [alpha]
      have hs := fderiv_fun_sum (u := (Finset.univ : Finset (Fin 3)))
        (fun i _ => (hAdiff i).smul_const (eProj i))
      rw [hs]; simp only [FunLike.coe_sum, Finset.sum_apply]
    rw [hsumx, hsumy]
    -- Apply hterm pointwise
    have hterm' (i : Fin 3) (v w : Sp) :
        (fderiv ℝ (fun z : Sp => A i z • eProj i) a v) w =
          fderiv ℝ (A i) a v * w i := by
      rw [hterm i]; simp [ContinuousLinearMap.smulRight_apply, eProj,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp only [hterm']
    have hAi (i : Fin 3) : fderiv ℝ (A i) a = rowForm H i a := (hAder i a).fderiv
    simp_rw [hAi]
    have hexpand (v w : Sp) :
        ∑ i : Fin 3, rowForm H i a v * w i =
          ∑ i : Fin 3, ∑ j : Fin 3, H a i j * v j * w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rowForm
      simp only [FunLike.coe_sum, Finset.sum_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [eProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hexpand x y, hexpand y x]
    calc ∑ i : Fin 3, ∑ j : Fin 3, H a i j * x j * y i
        = ∑ j : Fin 3, ∑ i : Fin 3, H a i j * x j * y i := by rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, H a j i * x i * y j := by
            -- rename i↔j
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin 3, ∑ j : Fin 3, H a i j * y j * x i := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hsym a j i]; ring
  obtain ⟨φ, hφcont, hφder⟩ :=
    contDiff_primitive_of_closed_oneForm alpha hαCont
      (fun a x y => hαClosed a x y)
  refine ⟨φ, hφcont, fun y i j => ?_⟩
  have hfun : (fun z => fderiv ℝ φ z (Pi.single i 1)) = A i := by
    funext z
    have h := congrArg (fun L : Sp →L[ℝ] ℝ => L (Pi.single i 1)) (hφder z).fderiv
    dsimp [alpha] at h
    simp only [FunLike.coe_sum, Finset.sum_apply] at h
    -- ∑ c, (A c z • eProj c) (Pi.single i 1)
    simp only [eProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h
    exact h
  rw [hfun]
  have h := congrArg (fun L : Sp →L[ℝ] ℝ => L (Pi.single j 1)) (hAder i y).fderiv
  dsimp [rowForm] at h
  simp only [FunLike.coe_sum, Finset.sum_apply] at h
  simp only [eProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at h
  exact h
