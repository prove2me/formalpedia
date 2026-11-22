-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_scale_transfer_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:14:26.902461+00:00
-- url     : https://prove2.me/submissions/6c0d7750-05e4-4444-b276-6b67d81be616

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_convex_root_bridge
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_marginals_antitone_universe
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_exponent_unbounded_universe
import Mathlib.Probability.Moments.MGFAnalytic
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (ψ : ℝ → ℝ) (hexp : ∀ β : ℝ, 0 ≤ β → A.ψ β = ψ β)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)))
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hWq : Kyprianou.Ch08.IsQScale ψ q W) :
    AvramDividend.Classical.IsScaleFunction A q W := by
  have hbridge : IsScaleTransformDomainBridge A.ψ q := by
    have hmgf_exp (x : ℝ) (hx : 0 ≤ x) : mgf (A.X 1) P x = Real.exp (A.ψ x) := by
      simpa only [mgf, NNReal.coe_one, one_mul, AvramDividend.Classical.SpectrallyNegativeLevy.ψ]
        using (A.laplace 1 x hx).2
    have hzero : A.ψ 0 = 0 := by
      have h := hmgf_exp 0 le_rfl
      have hmgf_zero : mgf (A.X 1) P 0 = 1 := by simp [mgf]
      rw [hmgf_zero, ← Real.exp_zero] at h
      exact (Real.exp_injective h).symm
    have hinterior : Ioi (0 : ℝ) ⊆ interior (integrableExpSet (A.X 1) P) :=
      interior_maximal (fun x hx => (A.laplace 1 x (show 0 < x from hx).le).1) isOpen_Ioi
    have hmgf := (continuousOn_mgf (X := A.X 1) (μ := P)).mono hinterior
    have hcont : ContinuousOn A.ψ (Ioi (0 : ℝ)) := (hmgf.log fun x hx => by
      rw [hmgf_exp x (show 0 < x from hx).le]; exact Real.exp_ne_zero _).congr fun x hx => by
        change A.ψ x = Real.log (mgf (A.X 1) P x)
        rw [hmgf_exp x (show 0 < x from hx).le, Real.log_exp]
    have ht : ∃ t : ℝ≥0, ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0) := by
      by_contra! h
      exact hnotneg (source_result81_levy_marginals_antitone_universe A h)
    obtain ⟨t, ht⟩ := ht
    exact source_result81_convex_root_bridge A.ψ hzero
      (AvramDividend.Classical.levy_laplace_exponent_convexOn_nonnegative A)
      hcont (fun qq => source_result81_levy_exponent_unbounded_universe A (t := t) ht qq) q hq.le
  obtain ⟨hrootW, hneg, hnon, hcontW, hmonoW, hlap⟩ := hWq
  have hsets : RightRootSet ψ q = RightRootSet A.ψ q := by
    ext β
    change (0 ≤ β ∧ ψ β = q) ↔ (0 ≤ β ∧ A.ψ β = q)
    constructor
    · rintro ⟨hβ, heq⟩; exact ⟨hβ, (hexp β hβ).trans heq⟩
    · rintro ⟨hβ, heq⟩; exact ⟨hβ, (hexp β hβ).symm.trans heq⟩
  have hPhi : Phi ψ q = Phi A.ψ q := congrArg sSup hsets
  refine ⟨hneg, ?_, hcontW, hmonoW, ?_⟩
  · intro y hy; exact hnon y
  · intro β hβ0 hβq
    have hPhiA : Phi A.ψ q < β := (hbridge.2 β hβ0).2 hβq
    have hPhiψ : Phi ψ q < β := by
      rw [hPhi]
      exact hPhiA
    obtain ⟨hint, hval⟩ := hlap β hβ0 hPhiψ
    refine ⟨?_, ?_⟩
    · simpa only [neg_mul] using hint
    · have hvalA : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) * W x ∂volume) = (A.ψ β - q)⁻¹ := by
        have h2 := hval
        rw [← hexp β hβ0] at h2
        exact h2
      simpa only [neg_mul] using hvalA
