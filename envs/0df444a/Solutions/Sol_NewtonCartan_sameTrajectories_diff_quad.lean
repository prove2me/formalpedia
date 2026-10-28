-- Prove2me | solution 1 for NewtonCartan.sameTrajectories_diff_quad
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:08:00.672647+00:00
-- url     : https://prove2.me/submissions/e891badf-04ff-45f5-969d-18add83eb33a

import Definitions.Def_NewtonCartan_defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators Topology
open Classical Set Filter
open NewtonCartan

/-! SameTrajectories ⇒ spray agreement on the unit-timelike cone (Malament / Trautman). -/

private lemma contDiff_pd (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (b : Fin 4) :
    ContDiff ℝ ∞ (fun x => pd φ b x) := by
  have hf := (contDiff_infty_iff_fderiv.1 hφ).2
  simpa [pd] using ContDiff.clm_apply hf contDiff_const

private lemma contDiff_gradUp_apply (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (a : Fin 4) :
    ContDiff ℝ ∞ (fun x => gradUp φ x a) := by
  simpa [gradUp] using
    ContDiff.sum (s := Finset.univ) (f := fun n : Fin 4 => fun x => hh a n * pd φ n x)
      (fun n _ => contDiff_const.mul (contDiff_pd φ hφ n))

private lemma contDiff_geomΓ (Γ : Conn) (φ : E → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (geomΓ Γ φ) := by
  refine contDiff_pi.2 fun a => ?_
  refine contDiff_pi.2 fun b => ?_
  refine contDiff_pi.2 fun c => ?_
  have hΓabc : ContDiff ℝ ∞ (fun x => Γ x a b c) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c
  simpa [geomΓ] using hΓabc.add (contDiff_const.mul (contDiff_gradUp_apply φ hφ a))

private lemma compatible_Gamma0 (Γ : Conn) (hC : Compatible Γ) (x : E) (b c : Fin 4) :
    Γ x 0 b c = 0 := by
  simpa [tt, Finset.sum_ite_eq'] using hC.1 x b c

noncomputable def geodesicSpray (Γ : Conn) : (E × E) → (E × E) :=
  fun p => (p.2, fun a => -∑ b : Fin 4, ∑ c : Fin 4, Γ p.1 a b c * p.2 b * p.2 c)

private lemma contDiff_geodesicSpray (Γ : Conn) (hΓ : ContDiff ℝ ∞ Γ) :
    ContDiff ℝ ∞ (geodesicSpray Γ) := by
  refine ContDiff.prodMk contDiff_snd ?_
  refine contDiff_pi.2 fun a => ContDiff.neg ?_
  refine ContDiff.sum (s := Finset.univ)
    (f := fun b : Fin 4 => fun p : E × E =>
      ∑ c : Fin 4, Γ p.1 a b c * p.2 b * p.2 c) fun b _ => ?_
  refine ContDiff.sum (s := Finset.univ)
    (f := fun c : Fin 4 => fun p : E × E => Γ p.1 a b c * p.2 b * p.2 c) fun c _ => ?_
  have hΓabc : ContDiff ℝ ∞ (fun p : E × E => Γ p.1 a b c) :=
    (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c).comp contDiff_fst
  have hvb : ContDiff ℝ ∞ (fun p : E × E => p.2 b) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) b).comp contDiff_snd
  have hvc : ContDiff ℝ ∞ (fun p : E × E => p.2 c) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) c).comp contDiff_snd
  exact (hΓabc.mul hvb).mul hvc

private lemma contDiffOn_of_hasDerivAt_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : F → F} (hV : ContDiff ℝ ∞ V) {s : Set ℝ} (hs : IsOpen s)
    {α : ℝ → F} (hder : ∀ t ∈ s, HasDerivAt α (V (α t)) t) :
    ContDiffOn ℝ ∞ α s := by
  have hdiff : DifferentiableOn ℝ α s := fun t ht =>
    (hder t ht).differentiableAt.differentiableWithinAt
  have hderiv_eq : ∀ t ∈ s, deriv α t = V (α t) := fun t ht => (hder t ht).deriv
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n α s := by
    intro n
    induction n with
    | zero =>
      exact (contDiffOn_zero (𝕜 := ℝ) (f := α) (s := s)).2 hdiff.continuousOn
    | succ n ih =>
      refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : ℕ∞ω)) hs).2 ⟨hdiff, by simp, ?_⟩
      have hVα : ContDiffOn ℝ n (fun t => V (α t)) s :=
        (hV.of_le (by exact_mod_cast le_top)).comp_contDiffOn ih
      exact hVα.congr fun t ht => hderiv_eq t ht
  exact contDiffOn_infty.2 hnat

private lemma accel_diff (Γ₁ Γ₂ : Conn) (γ : ℝ → E) (s : ℝ) (a : Fin 4) :
    accel Γ₁ γ s a - accel Γ₂ γ s a =
      ∑ b : Fin 4, ∑ c : Fin 4, (Γ₁ (γ s) a b c - Γ₂ (γ s) a b c) *
        deriv γ s b * deriv γ s c := by
  simp only [accel]
  -- γ'' cancels: LHS = ∑∑ Γ₁ ξξ - ∑∑ Γ₂ ξξ
  have hcancel :
      deriv (deriv γ) s a + ∑ b, ∑ c, Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c -
        (deriv (deriv γ) s a + ∑ b, ∑ c, Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c) =
      (∑ b, ∑ c, Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c) -
        ∑ b, ∑ c, Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c := by ring
  -- But simp only [accel] already left us with that difference of full accels.
  -- Re-state from scratch via unfolding:
  change
    (deriv (deriv γ) s a + ∑ b, ∑ c, Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c) -
      (deriv (deriv γ) s a + ∑ b, ∑ c, Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c) =
    ∑ b, ∑ c, (Γ₁ (γ s) a b c - Γ₂ (γ s) a b c) * deriv γ s b * deriv γ s c
  have hterm (b c : Fin 4) :
      Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c -
        Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c =
      (Γ₁ (γ s) a b c - Γ₂ (γ s) a b c) * deriv γ s b * deriv γ s c := by ring
  calc
    (deriv (deriv γ) s a + ∑ b, ∑ c, Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c) -
        (deriv (deriv γ) s a + ∑ b, ∑ c, Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c)
        = (∑ b, ∑ c, Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c) -
            ∑ b, ∑ c, Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c := by ring
    _ = ∑ b, ∑ c,
          (Γ₁ (γ s) a b c * deriv γ s b * deriv γ s c -
            Γ₂ (γ s) a b c * deriv γ s b * deriv γ s c) := by
          simp [Finset.sum_sub_distrib]
    _ = ∑ b, ∑ c,
          (Γ₁ (γ s) a b c - Γ₂ (γ s) a b c) * deriv γ s b * deriv γ s c := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hterm b c

private lemma accel_geomΓ (Γ : Conn) (φ : E → ℝ) (γ : ℝ → E) (s : ℝ) (a : Fin 4) :
    accel (geomΓ Γ φ) γ s a =
      accel Γ γ s a + gradUp φ (γ s) a * (deriv γ s 0) ^ 2 := by
  simp only [accel, geomΓ, add_mul, Finset.sum_add_distrib]
  have hproj : (∑ b : Fin 4, tt b * deriv γ s b) = deriv γ s 0 := by
    simp [tt, Finset.sum_ite_eq']
  have hfactor :
      (∑ b : Fin 4, ∑ c : Fin 4,
          ((tt b * tt c * gradUp φ (γ s) a) * deriv γ s b * deriv γ s c)) =
        gradUp φ (γ s) a * (deriv γ s 0) ^ 2 := by
    have h1 :
        (∑ b : Fin 4, ∑ c : Fin 4,
            ((tt b * tt c * gradUp φ (γ s) a) * deriv γ s b * deriv γ s c)) =
          gradUp φ (γ s) a *
            (∑ b : Fin 4, tt b * deriv γ s b) *
            (∑ c : Fin 4, tt c * deriv γ s c) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    rw [h1, hproj]; ring
  rw [hfactor, add_assoc]

private lemma sameTrajectories_geomΓ (Γ : Conn) (φ : E → ℝ) :
    SameTrajectories Γ φ (geomΓ Γ φ) := by
  intro γ s₀ s₁ hγ
  constructor
  · intro hgeo s hs a
    have ht : deriv γ s 0 = 1 := hγ.2.2 s hs
    have hA := hgeo s hs a
    rw [accel_geomΓ, ht, one_pow] at hA
    linarith
  · intro hNew s hs a
    have ht : deriv γ s 0 = 1 := hγ.2.2 s hs
    rw [accel_geomΓ, ht, one_pow, hNew s hs a]; ring

private lemma compatible_geomΓ (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    Compatible (geomΓ Γ φ) := by
  constructor
  · intro x b c
    have h0 := hNG.1.2.1 x b c
    simp only [geomΓ, add_mul, Finset.sum_add_distrib]
    have hcorr :
        (∑ n : Fin 4, (tt b * tt c * gradUp φ x n) * tt n) =
          tt b * tt c * (∑ n : Fin 4, tt n * gradUp φ x n) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have htg : (∑ n : Fin 4, tt n * gradUp φ x n) = 0 := by
      simp [tt, Finset.sum_ite_eq', gradUp, hh]
    rw [h0, zero_add, hcorr, htg, mul_zero]
  · intro x a b c
    have h0 := hNG.1.2.2 x a b c
    have hgoal :
        (∑ n : Fin 4,
          ((Γ x b a n + tt a * tt n * gradUp φ x b) * hh n c +
            (Γ x c a n + tt a * tt n * gradUp φ x c) * hh b n)) =
          (∑ n : Fin 4, (Γ x b a n * hh n c + Γ x c a n * hh b n)) +
            (∑ n : Fin 4, (tt a * tt n * gradUp φ x b) * hh n c) +
            (∑ n : Fin 4, (tt a * tt n * gradUp φ x c) * hh b n) := by
      simp [add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    have hc1 :
        (∑ n : Fin 4, (tt a * tt n * gradUp φ x b) * hh n c) =
          tt a * gradUp φ x b * (∑ n : Fin 4, tt n * hh n c) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have hc2 :
        (∑ n : Fin 4, (tt a * tt n * gradUp φ x c) * hh b n) =
          tt a * gradUp φ x c * (∑ n : Fin 4, tt n * hh b n) := by
      simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    have htc : (∑ n : Fin 4, tt n * hh n c) = 0 := by
      apply Finset.sum_eq_zero; intro n _; simp only [tt, hh]; split_ifs <;> simp_all
    have htb : (∑ n : Fin 4, tt n * hh b n) = 0 := by
      apply Finset.sum_eq_zero; intro n _; simp only [tt, hh]; split_ifs <;> simp_all
    change (∑ n : Fin 4,
        (geomΓ Γ φ x b a n * hh n c + geomΓ Γ φ x c a n * hh b n)) = 0
    simp only [geomΓ]
    rw [hgoal, h0, zero_add, hc1, hc2, htc, htb, mul_zero, mul_zero, add_zero]

private lemma mem_Ioo_zero {ε : ℝ} (hε : 0 < ε) : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by
  simp only [mem_Ioo, sub_lt_iff_lt_add, lt_add_iff_pos_right]
  exact ⟨hε, hε⟩

/-- Local ContDiff ∞ unit-timelike geodesic of `geomΓ` with given initial data. -/
private lemma exists_geomΓ_geodesic (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (ξ : Fin 4 → ℝ) (hξ : ξ 0 = 1) :
    ∃ (γ : ℝ → E) (ε : ℝ), 0 < ε ∧
      IsTimelikeOn γ (0 - ε) (0 + ε) ∧
      IsGeodesicOn (geomΓ Γ φ) γ (0 - ε) (0 + ε) ∧
      γ 0 = x ∧ deriv γ 0 = ξ := by
  let Gg := geomΓ Γ φ
  have hGg : ContDiff ℝ ∞ Gg := contDiff_geomΓ Γ φ hNG.1.1.1 hNG.2.2
  have hC : Compatible Gg := compatible_geomΓ Γ φ hNG
  have hV : ContDiff ℝ ∞ (geodesicSpray Gg) := contDiff_geodesicSpray Gg hGg
  have hV1 : ContDiffAt ℝ 1 (geodesicSpray Gg) (x, ξ) :=
    (hV.of_le (by decide : (1 : ℕ∞ω) ≤ ∞)).contDiffAt
  obtain ⟨α, hα0, ε, hε, hder⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ hV1 0
  let s : Set ℝ := Ioo (0 - ε) (0 + ε)
  have hs : IsOpen s := isOpen_Ioo
  have hαInf : ContDiffOn ℝ ∞ α s := contDiffOn_of_hasDerivAt_comp hV hs hder
  let γ : ℝ → E := fun t => (α t).1
  have hγInf : ContDiffOn ℝ ∞ γ s := contDiff_fst.comp_contDiffOn hαInf
  have hvel (t : ℝ) (ht : t ∈ s) : deriv γ t = (α t).2 := by
    have hf : HasDerivAt (Prod.fst ∘ α) (geodesicSpray Gg (α t)).1 t :=
      ((ContinuousLinearMap.fst ℝ E E).hasFDerivAt).comp_hasDerivAt t (hder t ht)
    have hf' : HasDerivAt γ (geodesicSpray Gg (α t)).1 t := by
      simpa [γ, Function.comp_def] using hf
    simpa [geodesicSpray] using hf'.deriv
  have htime (t : ℝ) (ht : t ∈ s) : (α t).2 0 = 1 := by
    let w : ℝ → ℝ := fun t => (α t).2 0
    have hw' (t : ℝ) (ht : t ∈ s) : HasDerivAt w 0 t := by
      have hsnd : HasDerivAt (Prod.snd ∘ α) (geodesicSpray Gg (α t)).2 t :=
        ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt).comp_hasDerivAt t (hder t ht)
      have hsnd' : HasDerivAt (fun t => (α t).2) (geodesicSpray Gg (α t)).2 t := by
        simpa [Function.comp_def] using hsnd
      have happly : HasDerivAt (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4) ∘ fun t => (α t).2)
          ((geodesicSpray Gg (α t)).2 0) t :=
        ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4)).hasFDerivAt).comp_hasDerivAt t hsnd'
      have happly' : HasDerivAt w ((geodesicSpray Gg (α t)).2 0) t := by
        simpa [w, Function.comp_def] using happly
      have hzero : (geodesicSpray Gg (α t)).2 0 = 0 := by
        simp only [geodesicSpray, neg_eq_zero]
        apply Finset.sum_eq_zero; intro b _
        apply Finset.sum_eq_zero; intro c _
        simp [compatible_Gamma0 Gg hC]
      simpa [hzero] using happly'
    have hdiff_w : DifferentiableOn ℝ w s := fun t ht =>
      (hw' t ht).differentiableAt.differentiableWithinAt
    have hw0 : w 0 = 1 := by simpa [w, hα0] using hξ
    have h0mem := mem_Ioo_zero hε
    have hconst :=
      hs.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff_w
        (fun t ht => (hw' t ht).deriv) h0mem ht
    exact hconst.symm.trans hw0
  refine ⟨γ, ε, hε, ?_, ?_, ?_, ?_⟩
  · -- IsTimelikeOn
    refine ⟨by linarith, hγInf, ?_⟩
    intro t ht
    calc deriv γ t 0 = (α t).2 0 := by rw [hvel t ht]
      _ = 1 := htime t ht
  · -- IsGeodesicOn
    intro t ht a
    have hsnd : HasDerivAt (fun u => (α u).2) (geodesicSpray Gg (α t)).2 t := by
      simpa [Function.comp_def] using
        (((ContinuousLinearMap.snd ℝ E E).hasFDerivAt).comp_hasDerivAt t (hder t ht))
    have hγ'' : HasDerivAt (deriv γ) (geodesicSpray Gg (α t)).2 t := by
      have heq : deriv γ =ᶠ[nhds t] (fun u => (α u).2) := by
        filter_upwards [hs.mem_nhds ht] with u hu
        exact hvel u hu
      exact hsnd.congr_of_eventuallyEq heq
    have hacc1 : deriv (deriv γ) t = (geodesicSpray Gg (α t)).2 := hγ''.deriv
    simp only [accel, hacc1, hvel t ht, geodesicSpray, Gg]
    ring
  · -- γ 0 = x
    simpa [γ] using congrArg Prod.fst hα0
  · -- deriv γ 0 = ξ
    have h0mem := mem_Ioo_zero hε
    rw [hvel 0 h0mem]
    simpa using congrArg Prod.snd hα0

theorem solution (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (Γ' : Conn) (_hD : IsDerivOp Γ') (hS : SameTrajectories Γ φ Γ')
    (x : E) (a : Fin 4) (ξ : Fin 4 → ℝ) (hξ : ξ 0 = 1) :
    (∑ b : Fin 4, ∑ c : Fin 4,
        (Γ' x a b c - geomΓ Γ φ x a b c) * ξ b * ξ c) = 0 := by
  obtain ⟨γ, ε, hε, hTL, hGeo, hγ0, hγ'0⟩ := exists_geomΓ_geodesic Γ φ hNG x ξ hξ
  have hSG := sameTrajectories_geomΓ Γ φ
  have hGeo' : IsGeodesicOn Γ' γ (0 - ε) (0 + ε) := by
    have := (hS γ (0 - ε) (0 + ε) hTL).2
    have hNew : IsNewtonianOn Γ φ γ (0 - ε) (0 + ε) :=
      (hSG γ (0 - ε) (0 + ε) hTL).1 hGeo
    exact this hNew
  have h0mem := mem_Ioo_zero hε
  have hA' : accel Γ' γ 0 a = 0 := hGeo' 0 h0mem a
  have hAg : accel (geomΓ Γ φ) γ 0 a = 0 := hGeo 0 h0mem a
  have hdiff := accel_diff Γ' (geomΓ Γ φ) γ 0 a
  rw [hγ0, hγ'0, hA', hAg, zero_sub] at hdiff
  linarith
