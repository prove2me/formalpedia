-- Prove2me | solution 1 for MasulloGRH.ideleGroup_oneParameterSubgroup_finite_component_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:55:37.459327+00:00
-- url     : https://prove2.me/submissions/a50d270e-3051-4a34-83de-3c5b3bf99047

import Definitions.Def_MasulloGRH_AdelicTheta
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Theorems.Thm_MasulloGRH_idele_group_topology

open MeasureTheory NumberField IsDedekindDomain MasulloGRH Set
set_option autoImplicit false

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (γ : {t : ℝ // 0 < t} →* IdeleGroup F) (hγ : Continuous γ) :
    (∀ t : {t : ℝ // 0 < t}, ((γ t : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = 1) ∧
    ∃! α : ℝ, ∀ t : {t : ℝ // 0 < t}, ideleNorm (γ t) = (t : ℝ) ^ α := by
  let expPos (x : ℝ) : {t : ℝ // 0 < t} := ⟨Real.exp x, Real.exp_pos x⟩
  have hExp : Continuous expPos := Real.continuous_exp.subtype_mk _
  have hExpLog (t : {t : ℝ // 0 < t}) : expPos (Real.log t.val) = t :=
    Subtype.ext (Real.exp_log t.property)
  have hExpAdd (x y : ℝ) : expPos (x + y) = expPos x * expPos y :=
    Subtype.ext (Real.exp_add x y)
  have hExpZero : expPos 0 = 1 := Subtype.ext Real.exp_zero
  obtain ⟨_, _, _, hNormCont, hNormMul, hNormPos, _⟩ := idele_group_topology F
  refine ⟨?_, ?_⟩
  · intro t
    apply DFunLike.ext
    intro v
    let coord (x : ℝ) : v.adicCompletion F :=
      ((γ (expPos x) : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v
    have hVal : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F)) :=
      Units.continuous_val
    have hFinite : Continuous (fun g : AdeleRing (𝓞 F) F => g.2) := continuous_snd
    have hCoord : Continuous coord := (RestrictedProduct.continuous_eval v).comp
      (hFinite.comp (hVal.comp (hγ.comp hExp)))
    have hRange : (Set.range coord).Subsingleton := (isPreconnected_range hCoord).subsingleton
    have h₀ : coord 0 = 1 := by
      change ((γ (expPos 0) : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = _
      rw [hExpZero, map_one]
      rfl
    have h := hRange (mem_range_self (Real.log t.val)) (mem_range_self 0)
    rw [h₀] at h
    change ((γ t : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = (1 : v.adicCompletion F)
    simpa only [coord, hExpLog] using h

  -- The logarithm of the norm is an additive function of the exponential parameter.
  let f : ℝ →+ ℝ :=
    { toFun := fun x => Real.log (ideleNorm (γ (expPos x)))
      map_zero' := by
        have h := hNormMul (1 : IdeleGroup F) 1
        have hp := hNormPos (1 : IdeleGroup F)
        rw [mul_one] at h
        have hOne : ideleNorm (1 : IdeleGroup F) = 1 := by nlinarith
        rw [hExpZero, map_one, hOne, Real.log_one]
      map_add' := fun x y => by
        rw [hExpAdd, map_mul, hNormMul,
          Real.log_mul (hNormPos _).ne' (hNormPos _).ne'] }
  have hF : Continuous f := Real.continuousOn_log.comp_continuous
    (hNormCont.comp (hγ.comp hExp)) (fun x => (hNormPos _).ne')
  have hLinear (x : ℝ) : f x = x * f 1 := by
    have h := map_real_smul f hF x (1 : ℝ)
    simpa only [smul_eq_mul, mul_one] using h
  refine ⟨f 1, ?_, ?_⟩
  · intro t
    have h := congrArg Real.exp (hLinear (Real.log t.val))
    change Real.exp (Real.log (ideleNorm (γ (expPos (Real.log t.val))))) =
      Real.exp (Real.log t.val * f 1) at h
    rw [hExpLog, Real.exp_log (hNormPos _), ← Real.rpow_def_of_pos t.property] at h
    exact h
  · intro a ha
    have h := congrArg Real.log (ha (expPos 1))
    change f 1 = Real.log (Real.exp 1 ^ a) at h
    rw [Real.log_rpow (Real.exp_pos _), Real.log_exp, mul_one] at h
    exact h.symm
