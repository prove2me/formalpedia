-- Prove2me | solution 1 for HunterPDE.Elliptic.weak_solution_existence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:19:51.406252+00:00
-- url     : https://prove2.me/submissions/0cb33345-e61a-4b71-9188-bf20d912e587

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

set_option autoImplicit false

open MeasureTheory

namespace HunterPDE.Elliptic.WSE71

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Pointwise integrand of `form`. -/
noncomputable def Gf (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q : Jet n) : ℝ :=
  ((∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j)
    - (∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i))
    + P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1

lemma form_eq (P : Coeffs n) (u v : H10 n Ω) :
    form P u v = ∫ x in Ω, Gf P x ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) := rfl

lemma Gf_add_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p p' q : Jet n) :
    Gf P x (p + p') q = Gf P x p q + Gf P x p' q := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [mul_add, Finset.sum_add_distrib, add_mul]
  ring

lemma Gf_add_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q q' : Jet n) :
    Gf P x p (q + q') = Gf P x p q + Gf P x p q' := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

lemma Gf_smul_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x (c • p) q = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma Gf_smul_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x p (c • q) = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma memLp_fst (U : JetL2 n Ω) :
    MemLp (fun x => (WithLp.ofLp (U x)).1) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))) U

lemma memLp_snd (U : JetL2 n Ω) (i : Fin n) :
    MemLp (fun x => (WithLp.ofLp (U x)).2 i) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp
    ((EuclideanSpace.proj i).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))) U

lemma int3 {f g h : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f ⊤ (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (hh : MemLp h 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x * h x) (volume.restrict Ω) := by
  have h1 : Integrable (g * h) (volume.restrict Ω) := hg.integrable_mul hh
  have h2 := h1.mul_of_top_right hf
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp [mul_assoc]

lemma Gf_integrable (P : Coeffs n) (hP : P.Admissible Ω) (U V : JetL2 n Ω) :
    Integrable (fun x => Gf P x (U x) (V x)) (volume.restrict Ω) := by
  unfold Gf
  refine Integrable.add (Integrable.sub ?_ ?_) ?_
  · refine integrable_finsetSum _ fun i _ => ?_
    refine integrable_finsetSum _ fun j _ => ?_
    exact int3 (hP.1 i j) (memLp_snd U i) (memLp_snd V j)
  · refine integrable_finsetSum _ fun i _ => ?_
    exact int3 (hP.2.1 i) (memLp_fst U) (memLp_snd V i)
  · exact int3 hP.2.2.1 (memLp_fst U) (memLp_fst V)

lemma form_add_left (P : Coeffs n) (hP : P.Admissible Ω) (u u' v : H10 n Ω) :
    form P (u + u') v = form P u v + form P u' v := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (u : JetL2 n Ω) (u' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_left]

lemma form_add_right (P : Coeffs n) (hP : P.Admissible Ω) (u v v' : H10 n Ω) :
    form P u (v + v') = form P u v + form P u v' := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (v : JetL2 n Ω) (v' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_right]

lemma form_smul_left (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P (c • u) v = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (u : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_left]

lemma form_smul_right (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P u (c • v) = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (v : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_right]

/-- The inclusion into `L²(Ω)` as a continuous linear map. -/
noncomputable def T (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)).comp
    (H10 n Ω).subtypeL

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (T n Ω u) (T n Ω v) := by
  rw [L2.inner_def]
  unfold l2inner
  refine integral_congr_ae ?_
  have hu := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (u : JetL2 n Ω)
  have hv := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (v : JetL2 n Ω)
  filter_upwards [hu, hv] with x hx hy
  change val u x * val v x = inner ℝ
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (u : JetL2 n Ω) x)
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (v : JetL2 n Ω) x)
  rw [hx, hy]
  simp [val, mul_comm]

lemma core {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (a : V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ a u u)
    (f : StrongDual ℝ V) : ∃! u : V, ∀ φ, a u φ = f φ := by
  have coercive : IsCoercive a := ⟨C, hC, fun u => by
    have := hcoer u; nlinarith [this]⟩
  set E := coercive.continuousLinearEquivOfBilin with hE
  set w0 := (InnerProductSpace.toDual ℝ V).symm f with hw0
  have key : ∀ y : V, (∀ φ, a y φ = f φ) ↔ E y = w0 := by
    intro y
    constructor
    · intro h
      refine ext_inner_right ℝ fun φ => ?_
      rw [hE, IsCoercive.continuousLinearEquivOfBilin_apply, h, hw0,
        InnerProductSpace.toDual_symm_apply]
    · intro h φ
      rw [← IsCoercive.continuousLinearEquivOfBilin_apply coercive, ← hE, h, hw0,
        InnerProductSpace.toDual_symm_apply]
  refine ⟨E.symm w0, (key _).2 (E.apply_symm_apply w0), fun y hy => ?_⟩
  have := (key y).1 hy
  rw [← this, E.symm_apply_apply]

end HunterPDE.Elliptic.WSE71

open HunterPDE.Elliptic in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (γ : ℝ)
    (hγ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u) ∧
      ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (f : StrongDual ℝ (H10 n Ω)) (μ : ℝ) (hμ : γ ≤ μ) :
    ∃! u : H10 n Ω, IsWeakSolution (form P) μ (fun φ => f φ) u := by
  obtain ⟨C₁, hC₁, C₂, hC₂, hcoer, hbd⟩ := hγ
  have : CompleteSpace (H10 n Ω) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let Bl : H10 n Ω →ₗ[ℝ] H10 n Ω →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => form P u v + μ * l2inner u v)
      (fun u u' v => by
        simp only [WSE71.form_add_left P hP, WSE71.l2inner_eq, map_add, inner_add_left]; ring)
      (fun c u v => by
        simp only [WSE71.form_smul_left P, WSE71.l2inner_eq, map_smul, real_inner_smul_left, smul_eq_mul]
        ring)
      (fun u v v' => by
        simp only [WSE71.form_add_right P hP, WSE71.l2inner_eq, map_add, inner_add_right]; ring)
      (fun c u v => by
        simp only [WSE71.form_smul_right P, WSE71.l2inner_eq, map_smul, real_inner_smul_right, smul_eq_mul]
        ring)
  let B : H10 n Ω →L[ℝ] H10 n Ω →L[ℝ] ℝ :=
    Bl.mkContinuous₂ (C₂ + |μ| * ‖WSE71.T n Ω‖ * ‖WSE71.T n Ω‖) (fun u v => by
      simp only [Bl, LinearMap.mk₂_apply, Real.norm_eq_abs]
      have h1 := hbd u v
      have h2 : |l2inner u v| ≤ ‖WSE71.T n Ω‖ * ‖u‖ * (‖WSE71.T n Ω‖ * ‖v‖) := by
        rw [WSE71.l2inner_eq]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul ((WSE71.T n Ω).le_opNorm u) ((WSE71.T n Ω).le_opNorm v) (norm_nonneg _)
          (by positivity)
      calc |form P u v + μ * l2inner u v| ≤ |form P u v| + |μ| * |l2inner u v| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ C₂ * ‖u‖ * ‖v‖ + |μ| * (‖WSE71.T n Ω‖ * ‖u‖ * (‖WSE71.T n Ω‖ * ‖v‖)) := by
            gcongr
        _ = (C₂ + |μ| * ‖WSE71.T n Ω‖ * ‖WSE71.T n Ω‖) * ‖u‖ * ‖v‖ := by ring)
  have hB : ∀ u v, B u v = form P u v + μ * l2inner u v := fun u v => rfl
  have hcoerB : ∀ u, C₁ * ‖u‖ ^ 2 ≤ B u u := by
    intro u
    rw [hB]
    have h0 : 0 ≤ l2inner u u := by rw [WSE71.l2inner_eq]; exact real_inner_self_nonneg
    have := hcoer u
    nlinarith
  obtain ⟨u, hu, huniq⟩ := WSE71.core B C₁ hC₁ hcoerB f
  refine ⟨u, fun φ => by rw [← hB]; exact hu φ, fun y hy => huniq y fun φ => ?_⟩
  rw [hB]; exact hy φ
