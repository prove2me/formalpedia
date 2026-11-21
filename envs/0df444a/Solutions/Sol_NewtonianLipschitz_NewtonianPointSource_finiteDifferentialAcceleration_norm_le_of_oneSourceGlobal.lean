-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:48:44.726642+00:00
-- url     : https://prove2.me/submissions/023bf302-0751-4ed8-822d-6a5059f59bff

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_exactDifferentialAcceleration_eq_sub
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (hOne : oneSourceGlobalCandidateBound)
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d : ℝ) (hd : 0 < d) :
    (∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖) →
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        ((sources.map (fun source =>
          (source t).gravitationalParameter)).sum * candidateMaximum)) *
        ‖q‖ := by
  induction sources with
  | nil =>
      intro _
      simp only [NewtonianPointSource.finiteDifferentialAcceleration_nil,
        List.map_nil, List.sum_nil, zero_mul, mul_zero, norm_zero, le_refl]
  | cons source rest ih =>
      intro hsafe
      have hheadsafe :
          d ≤ ‖(source t).displacement‖ ∧
            d ≤ ‖(source t).displacement + q‖ :=
        hsafe source (by simp)
      have hrestsafe :
          ∀ s ∈ rest,
            d ≤ ‖(s t).displacement‖ ∧
              d ≤ ‖(s t).displacement + q‖ := by
        intro s hs
        exact hsafe s (by simp [hs])
      have hhead :
          ‖(source t).exactDifferentialAcceleration q‖ ≤
            ((1 / d ^ 3) *
              ((source t).gravitationalParameter * candidateMaximum)) *
                ‖q‖ := by
        rw [(source t).exactDifferentialAcceleration_eq_sub]
        simpa only [add_sub_cancel_left] using
          (hOne (source t)
            ((source t).displacement + q)
            (source t).displacement d hd hheadsafe.2 hheadsafe.1)
      have htail := ih hrestsafe
      calc
        ‖NewtonianPointSource.finiteDifferentialAcceleration
            (source :: rest) t q‖ =
          ‖(source t).exactDifferentialAcceleration q +
            NewtonianPointSource.finiteDifferentialAcceleration rest t q‖ := by
          rw [NewtonianPointSource.finiteDifferentialAcceleration_cons]
        _ ≤ ‖(source t).exactDifferentialAcceleration q‖ +
              ‖NewtonianPointSource.finiteDifferentialAcceleration rest t q‖ :=
          norm_add_le _ _
        _ ≤ ((1 / d ^ 3) *
              ((source t).gravitationalParameter * candidateMaximum)) * ‖q‖ +
            ((1 / d ^ 3) *
              ((rest.map (fun s =>
                (s t).gravitationalParameter)).sum * candidateMaximum)) * ‖q‖ :=
          add_le_add hhead htail
        _ = ((1 / d ^ 3) *
              (((source :: rest).map (fun s =>
                (s t).gravitationalParameter)).sum * candidateMaximum)) *
                ‖q‖ := by
          simp only [List.map_cons, List.sum_cons]
          ring
end NewtonianPointSource
end NewtonianLipschitz
