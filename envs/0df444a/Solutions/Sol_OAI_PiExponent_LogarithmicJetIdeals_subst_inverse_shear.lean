-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_inverse_shear
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:45:28.02509+00:00
-- url     : https://prove2.me/submissions/dc490600-a719-4346-95cf-75d52c34c6e9

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators Topology MvPowerSeries.WithPiTopology
open MvPowerSeries.WithPiTopology
open Filter

-- A variable with constant coefficient one prevents the polynomial evaluation
-- map from having a limit at any formal power series.
private theorem polynomial_evaluation_no_limit
    {R : Type*} [CommRing R] [Nontrivial R]
    [UniformSpace R] [DiscreteUniformity R]
    (a : Fin 2 → MvPowerSeries (Fin 2) R)
    (ha : MvPowerSeries.constantCoeff (a 1) = 1)
    (f : MvPowerSeries (Fin 2) R) :
    ¬ ∃ z : MvPowerSeries (Fin 2) R,
      Tendsto (MvPolynomial.eval₂ (algebraMap R (MvPowerSeries (Fin 2) R)) a)
        (comap MvPolynomial.toMvPowerSeries (𝓝 f)) (𝓝 z) := by
  classical
  rintro ⟨z, hz⟩
  let p : ℕ → MvPolynomial (Fin 2) R := fun n => MvPowerSeries.truncTotal n f
  let q : ℕ → MvPolynomial (Fin 2) R := fun n => p n + MvPolynomial.X 1 ^ n
  let ε : MvPolynomial (Fin 2) R →+* MvPowerSeries (Fin 2) R :=
    MvPolynomial.eval₂Hom (algebraMap R (MvPowerSeries (Fin 2) R)) a
  have hp : Tendsto (fun n => (p n : MvPowerSeries (Fin 2) R)) atTop (𝓝 f) := by
    apply (tendsto_iff_coeff_tendsto _ _ _).mpr
    intro d
    apply tendsto_atTop_of_eventually_const (i₀ := d.degree + 1)
    intro n hn
    exact (MvPolynomial.coeff_coe (p n) d).trans
      (MvPowerSeries.coeff_truncTotal f (lt_of_lt_of_le (Nat.lt_succ_self _) hn))
  have hx : Tendsto
      (fun n : ℕ => ((MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) :
        MvPowerSeries (Fin 2) R)) atTop (𝓝 0) := by
    apply (tendsto_iff_coeff_tendsto _ _ _).mpr
    intro d
    apply tendsto_atTop_of_eventually_const (i₀ := d 1 + 1)
    intro n hn
    have hdn : d ≠ Finsupp.single 1 n := by
      intro he
      have hv : d 1 = n := by
        simpa using congrArg (fun t : Fin 2 →₀ ℕ => t 1) he
      exact (Nat.ne_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hn)) hv
    simp [MvPolynomial.coe_pow, MvPolynomial.coe_X,
      MvPowerSeries.coeff_X_pow, hdn]
  have hq : Tendsto (fun n => (q n : MvPowerSeries (Fin 2) R)) atTop (𝓝 f) := by
    simpa only [q, MvPolynomial.coe_add, add_zero] using hp.add hx
  have hzp : Tendsto (fun n => ε (p n)) atTop (𝓝 z) :=
    hz.comp (tendsto_comap_iff.mpr hp)
  have hzq : Tendsto (fun n => ε (q n)) atTop (𝓝 z) :=
    hz.comp (tendsto_comap_iff.mpr hq)
  have heq (n : ℕ) :
      MvPowerSeries.constantCoeff (ε (q n) - ε (p n)) = 1 := by
    dsimp only [q]
    rw [map_add, add_sub_cancel_left, map_pow]
    simp only [ε, MvPolynomial.eval₂Hom_X', map_pow, ha, one_pow]
  have ht : Tendsto
      (fun n => MvPowerSeries.constantCoeff (ε (q n) - ε (p n)))
      atTop (𝓝 (MvPowerSeries.constantCoeff (z - z))) :=
    (continuous_constantCoeff R).continuousAt.tendsto.comp (hzq.sub hzp)
  have ht' : Tendsto (fun _ : ℕ => (1 : R)) atTop (𝓝 (0 : R)) := by
    simpa only [heq, sub_self, map_zero] using ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht')

-- Outside the polynomial case the failed-limit branch is the same fixed
-- Classical.choice, independently of the input series.
private theorem bad_substitution_default
    (a : Fin 2 → MvPowerSeries (Fin 2) ℂ)
    (ha : MvPowerSeries.constantCoeff (a 1) = 1)
    (f : MvPowerSeries (Fin 2) ℂ)
    (hf : ¬ ∃ p : MvPolynomial (Fin 2) ℂ, (p : MvPowerSeries (Fin 2) ℂ) = f) :
    MvPowerSeries.subst a f =
      Classical.choice (inferInstance : Nonempty (MvPowerSeries (Fin 2) ℂ)) := by
  classical
  letI : UniformSpace ℂ := ⊥
  change MvPowerSeries.eval₂ (algebraMap ℂ (MvPowerSeries (Fin 2) ℂ)) a f = _
  rw [MvPowerSeries.eval₂, dif_neg hf]
  exact limUnder_of_not_tendsto (polynomial_evaluation_no_limit a ha f)

private noncomputable def badLog : PowerSeries ℂ :=
  PowerSeries.mk (fun _ => (-1 : ℂ))

private noncomputable def badLift : MvPowerSeries (Fin 2) ℂ :=
  liftLogSeries 1 badLog

private theorem badLift_coeff (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n) badLift = -1 := by
  have h := MvPowerSeries.coeff_coeff_finSuccEquiv badLift
    (k := n) (x := (0 : Fin 1 →₀ ℕ))
  simpa [badLift, liftLogSeries, badLog, RingHom.comp_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_mk,
    Finsupp.cons_zero_eq_single_zero] using h.symm

private theorem badLift_constant : MvPowerSeries.constantCoeff badLift = -1 := by
  simpa only [Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    using badLift_coeff 0

private theorem badLift_not_polynomial (c : ℂ) :
    ¬ ∃ p : MvPolynomial (Fin 2) ℂ,
      (p : MvPowerSeries (Fin 2) ℂ) =
        MvPowerSeries.X 1 + badLift + MvPowerSeries.C c := by
  classical
  rintro ⟨p, hp⟩
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 (p.totalDegree + 1)
  have hd : p.coeff d = 0 :=
    MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by
      change p.totalDegree < d.degree
      simpa only [d, Finsupp.degree_single] using Nat.lt_succ_self p.totalDegree)
  have hd0 : d ≠ 0 := by simp [d]
  have hd1 : d ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    have h1 := congrArg (fun t : Fin 2 →₀ ℕ => t 1) h
    simpa [d] using h1
  have h := congrArg (MvPowerSeries.coeff d) hp
  rw [MvPolynomial.coeff_coe, hd] at h
  have hc : MvPowerSeries.coeff d badLift = -1 := badLift_coeff _
  simp only [map_add, MvPowerSeries.coeff_X, if_neg hd1, hc,
    MvPowerSeries.coeff_C, if_neg hd0, zero_add, add_zero] at h
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) h.symm

-- Negation of the entire target, including its implicit dimension parameter.
theorem solution : ¬ (∀ {m : ℕ} (D : Fin m → PowerSeries ℂ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ),
    MvPowerSeries.subst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
      (MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) =
    MvPolynomial.aeval MvPowerSeries.X Q) := by
  classical
  intro h
  let D : Fin 1 → PowerSeries ℂ := fun _ => badLog
  let a : Fin 2 → MvPowerSeries (Fin 2) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ - liftLogSeries 1 (D i))
  have ha : MvPowerSeries.constantCoeff (a 1) = 1 := by
    change MvPowerSeries.constantCoeff (MvPowerSeries.X 1 - badLift) = 1
    simp [badLift_constant]
  have hf0 : ¬ ∃ p : MvPolynomial (Fin 2) ℂ,
      (p : MvPowerSeries (Fin 2) ℂ) = MvPowerSeries.X 1 + badLift := by
    simpa only [map_zero, add_zero] using badLift_not_polynomial 0
  have hf1 : ¬ ∃ p : MvPolynomial (Fin 2) ℂ,
      (p : MvPowerSeries (Fin 2) ℂ) = MvPowerSeries.X 1 + badLift + 1 := by
    simpa only [map_one] using badLift_not_polynomial 1
  have he : MvPowerSeries.subst a (MvPowerSeries.X 1 + badLift) =
      MvPowerSeries.subst a (MvPowerSeries.X 1 + badLift + 1) :=
    (bad_substitution_default a ha _ hf0).trans
      (bad_substitution_default a ha _ hf1).symm
  have h0 : MvPowerSeries.subst a (MvPowerSeries.X 1 + badLift) =
      MvPowerSeries.X 1 := by
    have hh := h D (MvPolynomial.X ((0 : Fin 1).succ))
    simp only [MvPolynomial.aeval_X, Fin.cases_succ] at hh
    exact hh
  have h1 : MvPowerSeries.subst a (MvPowerSeries.X 1 + badLift + 1) =
      MvPowerSeries.X 1 + 1 := by
    have hh := h D (MvPolynomial.X ((0 : Fin 1).succ) + 1)
    simp only [map_add, map_one, MvPolynomial.aeval_X, Fin.cases_succ] at hh
    exact hh
  have hc := congrArg MvPowerSeries.constantCoeff (h0.symm.trans (he.trans h1))
  simpa using hc