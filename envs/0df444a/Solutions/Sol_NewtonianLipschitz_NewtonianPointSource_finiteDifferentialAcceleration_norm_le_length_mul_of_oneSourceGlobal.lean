-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:00:18.007097+00:00
-- url     : https://prove2.me/submissions/6b4d63f1-c0a4-40ae-a3da-7c5750f72524

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
public import Theorems.Thm_NewtonianLipschitz_sourceGravitationalParameter_sum_le_length_mul
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (hOne : oneSourceGlobalCandidateBound)
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d M : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖)
    (hcap : ∀ source ∈ sources,
      (source t).gravitationalParameter ≤ M) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        (((sources.length : ℝ) * M) * candidateMaximum)) * ‖q‖ := by
  have hfinite :=
    NewtonianPointSource.finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
      hOne sources t q d hd hsafe
  have hmass :=
    sourceGravitationalParameter_sum_le_length_mul sources t M hcap
  have hmul :
      ((sources.map (fun source =>
        (source t).gravitationalParameter)).sum * candidateMaximum) ≤
        ((sources.length : ℝ) * M) * candidateMaximum :=
    mul_le_mul_of_nonneg_right hmass candidateMaximum_nonneg
  have hcoef :
      ((1 / d ^ 3) *
        ((sources.map (fun source =>
          (source t).gravitationalParameter)).sum * candidateMaximum)) ≤
        ((1 / d ^ 3) *
          (((sources.length : ℝ) * M) * candidateMaximum)) :=
    mul_le_mul_of_nonneg_left hmul (by positivity)
  exact hfinite.trans
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg q))
end NewtonianPointSource
end NewtonianLipschitz
