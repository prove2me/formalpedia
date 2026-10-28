-- Prove2me | solution 1 for NewtonCartan.exists_potential_of_spatial_F
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:31:09.878899+00:00
-- url     : https://prove2.me/submissions/6da525b9-1f1c-42bb-8c82-38b330258a01

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_radPot_hessian_eq
import Theorems.Thm_NewtonCartan_contDiff_integral_I01
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped ContDiff BigOperators Topology Interval
open Classical MeasureTheory Set Filter ContinuousLinearMap
open NewtonCartan

noncomputable def spatIdx (i : Fin 3) : Fin 4 := i.succ

lemma spatIdx_ne_zero (i : Fin 3) : spatIdx i ≠ 0 := by simp [spatIdx]

noncomputable def embed (t : ℝ) (y : Sp) : E :=
  fun a => match a with
    | ⟨0, _⟩ => t
    | ⟨1, _⟩ => y 0
    | ⟨2, _⟩ => y 1
    | ⟨3, _⟩ => y 2

lemma contDiff_embed : ContDiff ℝ ∞ (fun p : ℝ × Sp => embed p.1 p.2) := by
  refine contDiff_pi.2 fun a => ?_
  fin_cases a <;> simp only [embed] <;> fun_prop

noncomputable def sliceH (F : E → Fin 4 → Fin 4 → ℝ) (t : ℝ) (y : Sp) (i j : Fin 3) : ℝ :=
  F (embed t y) (spatIdx i) (spatIdx j)

lemma contDiff_sliceH (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × Sp => sliceH F p.1 p.2 i j) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Sp => F (embed p.1 p.2)) := hF.comp contDiff_embed
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Sp => F (embed p.1 p.2) (spatIdx i)) :=
    (contDiff_apply (𝕜 := ℝ) (E := Fin 4 → ℝ) (ι := Fin 4) (spatIdx i)).comp h1
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × Sp => F (embed p.1 p.2) (spatIdx i) (spatIdx j)) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 4) (spatIdx j)).comp h2
  simpa [sliceH] using h3

lemma contDiff_sliceH_Sp (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (sliceH F t) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact (contDiff_sliceH F hF i j).comp <| ContDiff.prodMk contDiff_const contDiff_id

noncomputable def radPot' (H : Sp → Fin 3 → Fin 3 → ℝ) (y : Sp) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j

noncomputable def spatOf (x : E) : Sp := fun k => x k.succ

noncomputable def spacePot (F : E → Fin 4 → Fin 4 → ℝ) (x : E) : ℝ :=
  radPot' (sliceH F (x 0)) (spatOf x)

lemma contDiff_radIntegrand (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : (ℝ × Sp) × ℝ =>
      (1 - p.2) * sliceH F p.1.1 (p.2 • p.1.2) i j * p.1.2 i * p.1.2 j) := by
  have hslice := contDiff_sliceH F hF i j
  have hmap : ContDiff ℝ ∞ (fun p : (ℝ × Sp) × ℝ => (p.1.1, p.2 • p.1.2)) := by fun_prop
  have hH := hslice.comp hmap
  exact ((((by fun_prop : ContDiff ℝ ∞ fun p : (ℝ × Sp) × ℝ => (1 - p.2 : ℝ)).mul hH).mul
    (by fun_prop)).mul (by fun_prop))

lemma contDiff_radTerm (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × Sp =>
      ∫ s in (0 : ℝ)..1, (1 - s) * sliceH F p.1 (s • p.2) i j * p.2 i * p.2 j) := by
  simpa using contDiff_integral_I01 (E := ℝ × Sp) (⊤ : ℕ∞)
    (fun p s => (1 - s) * sliceH F p.1 (s • p.2) i j * p.2 i * p.2 j)
    (contDiff_radIntegrand F hF i j)

lemma contDiff_radPot_slice (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × Sp => radPot' (sliceH F p.1) p.2) := by
  simp only [radPot']
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_radTerm F hF i j

lemma contDiff_spacePot (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spacePot F) := by
  have h := contDiff_radPot_slice F hF
  have hmap : ContDiff ℝ ∞ (fun x : E => ((x 0 : ℝ), spatOf x)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 4) (0 : Fin 4)
    · refine contDiff_pi.2 fun k =>
        contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 4) k.succ
  convert h.comp hmap using 1
  ext x; rfl

lemma gradUp_eq_pd (φ : E → ℝ) (x : E) (i : Fin 4) (hi : i ≠ 0) :
    gradUp φ x i = pd φ i x := by
  simp [gradUp, hh, hi, pd]

/-- Spatial indices: every nonzero Fin 4 is succ of a Fin 3. -/
lemma exists_spatIdx (i : Fin 4) (hi : i ≠ 0) : ∃ k : Fin 3, i = spatIdx k := by
  match i with
  | ⟨0, _⟩ => exact absurd rfl hi
  | ⟨1, _⟩ => exact ⟨0, rfl⟩
  | ⟨2, _⟩ => exact ⟨1, rfl⟩
  | ⟨3, _⟩ => exact ⟨2, rfl⟩

lemma embed_spatOf (x : E) : embed (x 0) (spatOf x) = x := by
  ext a; fin_cases a <;> rfl

lemma spatOf_embed (t : ℝ) (y : Sp) : spatOf (embed t y) = y := by
  ext k; fin_cases k <;> rfl

lemma add_single_time (x : E) (k : Fin 3) (ε : ℝ) :
    (x + ε • (Pi.single (spatIdx k) (1 : ℝ) : E)) 0 = x 0 := by
  simp [Pi.add_apply, Pi.smul_apply, spatIdx]

lemma add_single_spatOf (x : E) (k : Fin 3) (ε : ℝ) :
    spatOf (x + ε • (Pi.single (spatIdx k) (1 : ℝ) : E)) =
      spatOf x + ε • Pi.single k (1 : ℝ) := by
  ext m
  simp only [spatOf, Pi.add_apply, Pi.smul_apply, spatIdx, Pi.single_apply]
  by_cases hm : m = k
  · subst hm; simp [smul_eq_mul]
  · have hsucc : (m.succ : Fin 4) ≠ k.succ := mt Fin.succ_inj.mp hm
    simp [hm, hsucc, smul_eq_mul]

lemma spacePot_spatial_line (F : E → Fin 4 → Fin 4 → ℝ) (x : E) (k : Fin 3) (ε : ℝ) :
    spacePot F (x + ε • (Pi.single (spatIdx k) (1 : ℝ) : E)) =
      radPot' (sliceH F (x 0)) (spatOf x + ε • Pi.single k (1 : ℝ)) := by
  simp only [spacePot, add_single_time, add_single_spatOf]




/-- Spatial inclusion `Sp ↪ E`: `(y₀,y₁,y₂) ↦ (0,y₀,y₁,y₂)`. -/
noncomputable def spatIncl : Sp →L[ℝ] E :=
  ContinuousLinearMap.pi fun a : Fin 4 =>
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3)
    | ⟨2, _⟩ => ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)
    | ⟨3, _⟩ => ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)

lemma spatIncl_apply (y : Sp) (a : Fin 4) :
    spatIncl y a =
      match a with
      | ⟨0, _⟩ => (0 : ℝ)
      | ⟨1, _⟩ => y 0
      | ⟨2, _⟩ => y 1
      | ⟨3, _⟩ => y 2 := by
  fin_cases a <;> rfl

lemma spatIncl_single (k : Fin 3) :
    spatIncl (Pi.single k (1 : ℝ)) = (Pi.single (spatIdx k) (1 : ℝ) : E) := by
  ext a
  fin_cases k <;> fin_cases a <;> simp [spatIncl_apply, spatIdx]

lemma embed_eq_const_add (t : ℝ) (y : Sp) :
    embed t y = (Pi.single (0 : Fin 4) t : E) + spatIncl y := by
  ext a
  fin_cases a <;> simp [embed, spatIncl_apply, Pi.add_apply]

lemma hasFDerivAt_embed (t : ℝ) (y : Sp) :
    HasFDerivAt (embed t) spatIncl y := by
  have h : embed t = fun z => (Pi.single (0 : Fin 4) t : E) + spatIncl z := by
    funext z; exact embed_eq_const_add t z
  rw [h]
  exact (spatIncl.hasFDerivAt).const_add _

lemma fderiv_embed (t : ℝ) (y : Sp) : fderiv ℝ (embed t) y = spatIncl :=
  (hasFDerivAt_embed t y).fderiv

lemma hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x v : F) : HasDerivAt (fun ε : ℝ => x + ε • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

lemma hasDerivAt_comp_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ ∞ f) (x v : F) :
    HasDerivAt (fun ε : ℝ => f (x + ε • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiable (by decide)).differentiableAt.hasFDerivAt
  exact hl.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hasDerivAt_line x v)
    (by simp : x = x + (0 : ℝ) • v)

lemma hasDerivAt_fderiv_apply_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ ∞ f) (x v w : F) :
    HasDerivAt (fun ε : ℝ => fderiv ℝ f (x + ε • w) v)
      (fderiv ℝ (fun z => fderiv ℝ f z v) x w) 0 := by
  have hle : (1 : ℕ∞ω) + 1 ≤ ∞ := by decide
  have hD : DifferentiableAt ℝ (fun z => fderiv ℝ f z v) x :=
    ((hf.fderiv_right (m := 1) hle).differentiable (by decide)).differentiableAt.clm_apply
      (differentiableAt_const _)
  exact hD.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hasDerivAt_line x w)
    (by simp : x = x + (0 : ℝ) • w)

lemma spacePot_embed (F : E → Fin 4 → Fin 4 → ℝ) (t : ℝ) (y : Sp) :
    spacePot F (embed t y) = radPot' (sliceH F t) y := by
  simp only [spacePot, spatOf_embed]
  have ht : embed t y 0 = t := by simp [embed]
  simp only [ht]

lemma contDiff_embed_t (t : ℝ) : ContDiff ℝ ∞ (embed t) := by
  have h : embed t = fun z => (Pi.single (0 : Fin 4) t : E) + spatIncl z := by
    funext z; exact embed_eq_const_add t z
  rw [h]
  exact contDiff_const.add spatIncl.contDiff

lemma contDiff_radPot'_of_slice (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Sp => radPot' (sliceH F t) y) := by
  have h : (fun y : Sp => radPot' (sliceH F t) y) =
      fun y => spacePot F (embed t y) := by
    funext y; exact (spacePot_embed F t y).symm
  rw [h]
  exact (contDiff_spacePot F hF).comp (contDiff_embed_t t)

lemma slice_closed (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F)
    (hclosed : ∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 →
      pd (fun y => F y i j) k x = pd (fun y => F y i k) j x)
    (t : ℝ) (z : Sp) (u v w : Fin 3) :
    fderiv ℝ (fun q => sliceH F t q u v) z (Pi.single w 1) =
      fderiv ℝ (fun q => sliceH F t q u w) z (Pi.single v 1) := by
  have hi := spatIdx_ne_zero u
  have hj := spatIdx_ne_zero v
  have hk := spatIdx_ne_zero w
  have hGuv : ContDiff ℝ ∞ (fun p : E => F p (spatIdx u) (spatIdx v)) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 4) (spatIdx v)).comp
      ((contDiff_apply (𝕜 := ℝ) (E := Fin 4 → ℝ) (ι := Fin 4) (spatIdx u)).comp hF)
  have hGuw : ContDiff ℝ ∞ (fun p : E => F p (spatIdx u) (spatIdx w)) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 4) (spatIdx w)).comp
      ((contDiff_apply (𝕜 := ℝ) (E := Fin 4 → ℝ) (ι := Fin 4) (spatIdx u)).comp hF)
  have hcomp_uv :
      HasFDerivAt ((fun p : E => F p (spatIdx u) (spatIdx v)) ∘ embed t)
        (fderiv ℝ (fun p : E => F p (spatIdx u) (spatIdx v)) (embed t z) ∘L spatIncl) z :=
    (hGuv.differentiable (by decide)).differentiableAt (x := embed t z) |>.hasFDerivAt.comp z
      (hasFDerivAt_embed t z)
  have hcomp_uw :
      HasFDerivAt ((fun p : E => F p (spatIdx u) (spatIdx w)) ∘ embed t)
        (fderiv ℝ (fun p : E => F p (spatIdx u) (spatIdx w)) (embed t z) ∘L spatIncl) z :=
    (hGuw.differentiable (by decide)).differentiableAt (x := embed t z) |>.hasFDerivAt.comp z
      (hasFDerivAt_embed t z)
  have huv :
      fderiv ℝ (fun q => F (embed t q) (spatIdx u) (spatIdx v)) z (Pi.single w 1) =
        fderiv ℝ (fun p => F p (spatIdx u) (spatIdx v)) (embed t z)
          (spatIncl (Pi.single w 1)) := by
    have hfeq :
        (fun q => F (embed t q) (spatIdx u) (spatIdx v)) =
          (fun p : E => F p (spatIdx u) (spatIdx v)) ∘ embed t := rfl
    rw [hfeq, hcomp_uv.fderiv, ContinuousLinearMap.comp_apply]
  have huw :
      fderiv ℝ (fun q => F (embed t q) (spatIdx u) (spatIdx w)) z (Pi.single v 1) =
        fderiv ℝ (fun p => F p (spatIdx u) (spatIdx w)) (embed t z)
          (spatIncl (Pi.single v 1)) := by
    have hfeq :
        (fun q => F (embed t q) (spatIdx u) (spatIdx w)) =
          (fun p : E => F p (spatIdx u) (spatIdx w)) ∘ embed t := rfl
    rw [hfeq, hcomp_uw.fderiv, ContinuousLinearMap.comp_apply]
  simp only [sliceH]
  rw [huv, huw, spatIncl_single, spatIncl_single]
  simpa [pd] using hclosed (embed t z) (spatIdx u) (spatIdx v) (spatIdx w) hi hj hk

/-- Spatial first derivative of `spacePot` equals Sp-derivative of the slice potential. -/
lemma pd_spacePot_spatial (F : E → Fin 4 → Fin 4 → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : E) (a : Fin 3) :
    pd (spacePot F) (spatIdx a) x =
      fderiv ℝ (radPot' (sliceH F (x 0))) (spatOf x) (Pi.single a 1) := by
  let H := sliceH F (x 0)
  let y := spatOf x
  let vE : E := Pi.single (spatIdx a) (1 : ℝ)
  let vS : Sp := Pi.single a (1 : ℝ)
  have hline (ε : ℝ) :
      spacePot F (x + ε • vE) = radPot' H (y + ε • vS) :=
    spacePot_spatial_line F x a ε
  have hSp : ContDiff ℝ ∞ (fun y : Sp => radPot' H y) := contDiff_radPot'_of_slice F hF (x 0)
  have hderiv_right : HasDerivAt (fun ε : ℝ => radPot' H (y + ε • vS))
      (fderiv ℝ (radPot' H) y vS) 0 :=
    hasDerivAt_comp_line (radPot' H) hSp y vS
  have hderiv_left : HasDerivAt (fun ε : ℝ => spacePot F (x + ε • vE))
      (fderiv ℝ (spacePot F) x vE) 0 :=
    hasDerivAt_comp_line (spacePot F) (contDiff_spacePot F hF) x vE
  have heq : (fun ε => spacePot F (x + ε • vE)) =
      fun ε => radPot' H (y + ε • vS) := funext hline
  have : fderiv ℝ (spacePot F) x vE = fderiv ℝ (radPot' H) y vS :=
    hderiv_left.unique (heq ▸ hderiv_right)
  simpa [pd, H, y, vE, vS] using this

theorem solution (F : E → Fin 4 → Fin 4 → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (_hrow : ∀ x d, F x 0 d = 0) (_hcol : ∀ x a, F x a 0 = 0)
    (hsym : ∀ x i j, F x i j = F x j i)
    (hclosed : ∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 →
      pd (fun y => F y i j) k x = pd (fun y => F y i k) j x) :
    ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ x i j, i ≠ 0 → j ≠ 0 →
        pd (fun y => gradUp φ y i) j x = F x i j := by
  refine ⟨spacePot F, contDiff_spacePot F hF, ?_⟩
  intro x i j hi hj
  obtain ⟨a, rfl⟩ := exists_spatIdx i hi
  obtain ⟨b, rfl⟩ := exists_spatIdx j hj
  have hgu : (fun y => gradUp (spacePot F) y (spatIdx a)) =
      fun y => pd (spacePot F) (spatIdx a) y := by
    funext y; exact gradUp_eq_pd _ _ _ (spatIdx_ne_zero a)
  rw [hgu]
  let t := x 0
  let y := spatOf x
  let H := sliceH F t
  have hH : ContDiff ℝ ∞ H := contDiff_sliceH_Sp F hF t
  have hsymH : ∀ z u v, H z u v = H z v u := fun z u v => hsym _ _ _
  have hclosedH := fun z u v w => slice_closed F hF hclosed t z u v w
  obtain ⟨_, hhessSp⟩ := radPot_hessian_eq H hH hsymH hclosedH
  have hx : embed t y = x := embed_spatOf x
  have hHab : H y a b = F x (spatIdx a) (spatIdx b) := by
    simp only [H, sliceH, t, y, hx]
  have h1 (z : E) : pd (spacePot F) (spatIdx a) z =
      fderiv ℝ (radPot' (sliceH F (z 0))) (spatOf z) (Pi.single a 1) :=
    pd_spacePot_spatial F hF z a
  let vE : E := Pi.single (spatIdx b) (1 : ℝ)
  let vS : Sp := Pi.single b (1 : ℝ)
  have hline (ε : ℝ) :
      pd (spacePot F) (spatIdx a) (x + ε • vE) =
        fderiv ℝ (radPot' H) (y + ε • vS) (Pi.single a 1) := by
    rw [h1]
    simp only [add_single_time, add_single_spatOf, H, t, y, vE, vS]
  have hSpCont : ContDiff ℝ ∞ (fun y : Sp => radPot' H y) := contDiff_radPot'_of_slice F hF t
  have hrhs : HasDerivAt
      (fun ε : ℝ => fderiv ℝ (radPot' H) (y + ε • vS) (Pi.single a 1))
      (fderiv ℝ (fun w => fderiv ℝ (radPot' H) w (Pi.single a 1)) y vS) 0 :=
    hasDerivAt_fderiv_apply_line (radPot' H) hSpCont y (Pi.single a 1) vS
  have hlhs : HasDerivAt
      (fun ε : ℝ => pd (spacePot F) (spatIdx a) (x + ε • vE))
      (pd (fun z => pd (spacePot F) (spatIdx a) z) (spatIdx b) x) 0 := by
    simpa [pd, vE] using
      hasDerivAt_fderiv_apply_line (spacePot F) (contDiff_spacePot F hF) x
        (Pi.single (spatIdx a) (1 : ℝ)) vE
  have hEqDeriv : pd (fun z => pd (spacePot F) (spatIdx a) z) (spatIdx b) x =
      fderiv ℝ (fun w => fderiv ℝ (radPot' H) w (Pi.single a 1)) y (Pi.single b 1) := by
    have heq := funext hline
    have := (heq ▸ hlhs).unique hrhs
    simpa [vS] using this
  have hhess' :
      fderiv ℝ (fun w => fderiv ℝ (radPot' H) w (Pi.single a 1)) y (Pi.single b 1) =
        H y a b := by
    change fderiv ℝ (fun w =>
        fderiv ℝ (fun y : Sp =>
          ∑ i : Fin 3, ∑ j : Fin 3,
            ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j) w (Pi.single a 1))
        y (Pi.single b 1) = H y a b
    exact hhessSp y a b
  rw [hEqDeriv, hhess', hHab]

