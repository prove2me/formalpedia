-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationJointCharFactorizationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:11:29.369577+00:00
-- url     : https://prove2.me/submissions/7620ea93-2469-4d3a-ba28-1a4788a80eff

import Theorems.Thm_Kyprianou_Ch02_independentRandomTimeVectorIntegralV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyIncrementCharFunEqualsLagV1
import Theorems.Thm_Kyprianou_Ch02_levyCharFunTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_subordinatedIncrementCharMixtureV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (θ : Fin n → ℝ) :
    (∫ ω, ∏ k : Fin n, Complex.exp ((θ k : ℂ) *
      (increment (fun t ω => X (τ t ω) ω) (t k.castSucc) (t k.succ) ω : ℂ) * Complex.I) ∂P) =
    ∏ k : Fin n, charFun (P.map (increment (fun t ω => X (τ t ω) ω)
      (t k.castSucc) (t k.succ))) (θ k) := by
  let G : (Fin (n+1) → ℝ) → ℂ := fun v =>
    ∏ k : Fin n, Complex.exp ((θ k : ℂ) * ((v k.succ - v k.castSucc : ℝ) : ℂ) * Complex.I)
  have hG : Measurable G := by unfold G; fun_prop
  have hb : ∀ v, ‖G v‖ ≤ 1 := by
    intro v
    simp [G, norm_prod, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  obtain ⟨_, he⟩ := Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
    P X τ hX hτ hind (n+1) t G hG
  let K (k : Fin n) (r : ℝ) := charFun (P.map (X r.toNNReal)) (θ k)
  have hK (k : Fin n) : Measurable (K k) :=
    (Kyprianou.Ch02.levyCharFunTimeMeasurableV1 P X hX (θ k)).comp measurable_real_toNNReal
  let D (k : Fin n) := increment (fun t ω => (τ t ω : ℝ)) (t k.castSucc) (t k.succ)
  have hi : iIndepFun D P := hτ.indep_increments n t ht
  have hτm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P _ hτ
  have hm (k : Fin n) : AEMeasurable (D k) P :=
    (hτm (t k.succ)).sub (hτm (t k.castSucc))
  calc
    _ = ∫ ω, (∫ ω', G (fun i => X (τ (t i) ω) ω') ∂P) ∂P := by
      simpa [G, increment] using he 1 hb
    _ = ∫ ω, ∏ k : Fin n, K k (D k ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hmon] with ω hw
      let r : Fin (n+1) → ℝ≥0 := fun i => τ (t i) ω
      let DX (k : Fin n) := increment X (r k.castSucc) (r k.succ)
      have hDX : iIndepFun DX P := hX.indep_increments n r (hw.comp ht)
      have hXm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
      have hDXm (k : Fin n) : AEMeasurable (DX k) P :=
        (hXm (r k.succ)).sub (hXm (r k.castSucc))
      let f (k : Fin n) (x : ℝ) := Complex.exp ((θ k : ℂ) * (x : ℂ) * Complex.I)
      have hfm (k : Fin n) : Measurable (f k) := by unfold f; fun_prop
      change (∫ ω', ∏ k : Fin n, f k (DX k ω') ∂P) = _
      rw [hDX.integral_fun_prod_comp hDXm (fun k => (hfm k).aestronglyMeasurable)]
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := hw (ht (Fin.castSucc_le_succ k))
      rw [show K k (D k ω) = charFun (P.map (X (r k.succ - r k.castSucc))) (θ k) by
        simp [K, D, r, increment, ← NNReal.coe_sub hk']]
      rw [← Kyprianou.Ch02.levyIncrementCharFunEqualsLagV1 P X hX _ _ hk' (θ k),
        charFun_apply_real, integral_map (hDXm k) (by fun_prop)]
    _ = ∏ k : Fin n, ∫ ω, K k (D k ω) ∂P :=
      hi.integral_fun_prod_comp hm (fun k => (hK k).aestronglyMeasurable)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := ht (Fin.castSucc_le_succ k)
      rw [(Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
        P X τ hX hτ hmon hind _ _ hk' (θ k)).2]
      apply integral_congr_ae
      filter_upwards [hmon] with ω hw
      simp [K, D, increment, ← NNReal.coe_sub (hw hk')]
