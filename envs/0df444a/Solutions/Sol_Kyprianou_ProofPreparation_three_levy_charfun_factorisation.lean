-- Prove2me | solution 1 for Kyprianou.ProofPreparation.three_levy_charfun_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:20:04.992632+00:00
-- url     : https://prove2.me/submissions/308401a4-892b-4ba7-b26f-6e4c45726e9c

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation

theorem levy_aemeasurable_apply {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLevyProcess X P) (t : ℝ≥0) : AEMeasurable (X t) P := by
  have h := (hX.stationary_increments 0 t).aemeasurable_fst
  have he : increment X 0 (0 + t) = X t := by
    funext ω
    simp [increment, hX.start_zero]
  rwa [he] at h

theorem three_levy_charfun_factorisation
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents
      P Xgauss Xlarge Xsmall)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      charFun (P.map (Xgauss t)) ξ *
      charFun (P.map (Xlarge t)) ξ *
      charFun (P.map (Xsmall t)) ξ := by
  let G : Fin 3 → Ω → ℝ := fun i ω =>
    if i = 0 then Xgauss t ω else if i = 1 then Xlarge t ω else Xsmall t ω
  have hG : iIndepFun G P :=
    hind.comp (fun (_ : Fin 3) (x : ℝ≥0 → ℝ) => x t) (fun _ => measurable_pi_apply t)
  have hG0 : G 0 = Xgauss t := rfl
  have hG1 : G 1 = Xlarge t := rfl
  have hG2 : G 2 = Xsmall t := rfl
  have hm : ∀ i, AEMeasurable (G i) P := by
    intro i
    fin_cases i
    · exact levy_aemeasurable_apply hgauss t
    · exact levy_aemeasurable_apply hlarge t
    · exact levy_aemeasurable_apply hsmall t
  have h01 : IndepFun (Xgauss t) (Xlarge t) P := by
    rw [← hG0, ← hG1]; exact hG.indepFun (by decide)
  have h012 : IndepFun (fun ω => Xgauss t ω + Xlarge t ω) (Xsmall t) P := by
    have := hG.indepFun_finsetSum_of_notMem₀ hm (s := {0, 1}) (i := 2) (by decide)
    rw [hG2] at this
    convert this using 1
    funext ω
    simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), G]
  have mg := levy_aemeasurable_apply hgauss t
  have ml := levy_aemeasurable_apply hlarge t
  have ms := levy_aemeasurable_apply hsmall t
  have mgl : AEMeasurable (fun ω => Xgauss t ω + Xlarge t ω) P := mg.add ml
  rw [h012.charFun_map_fun_add_eq_mul mgl ms, Pi.mul_apply,
    h01.charFun_map_fun_add_eq_mul mg ml, Pi.mul_apply]

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents
      P Xgauss Xlarge Xsmall)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      charFun (P.map (Xgauss t)) ξ *
      charFun (P.map (Xlarge t)) ξ *
      charFun (P.map (Xsmall t)) ξ :=
  Kyprianou.ProofPreparation.three_levy_charfun_factorisation P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind t ξ
