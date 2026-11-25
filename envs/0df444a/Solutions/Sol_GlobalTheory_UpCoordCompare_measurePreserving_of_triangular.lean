-- Prove2me | solution 1 for GlobalTheory.UpCoordCompare.measurePreserving_of_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:49.320825+00:00
-- url     : https://prove2.me/submissions/3ad24a12-85ae-494d-beda-278e41bd18d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
import Theorems.Thm_GlobalTheory_UpCoordCompare_det_one_add_of_isNilpotent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section
namespace GlobalTheory.UpCoordCompare
theorem _root_.solution {n : ℕ} (F : V n → V n) (hF : Differentiable ℝ F)
    (hb : Function.Bijective F) (ρ : Fin n → ℕ)
    (htri : ∀ (i : Fin n) (z w : V n), (∀ j, ρ j < ρ i → z j = w j) → F z i - z i = F w i - w i) :
    MeasurePreserving F volume volume := by
  have hdet : ∀ z, (fderiv ℝ F z).det = 1 := by
    intro z
    set K : V n →ₗ[ℝ] V n := (fderiv ℝ F z : V n →ₗ[ℝ] V n) - 1 with hK
    have hstep : ∀ (i : Fin n) (h : V n), (∀ j, ρ j < ρ i → h j = 0) → K h i = 0 := by
      intro i h hh
      have h1 : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
      have h2 : HasDerivAt (fun t : ℝ => F (z + t • h)) (fderiv ℝ F z h) 0 := by
        exact (hF z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
      have h3 := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℂ) i).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (h2.sub h1)
      have h4 : (fun t : ℝ => F (z + t • h) i - (z + t • h) i) = fun _ => F z i - z i := by
        funext t
        exact htri i _ _ fun j hj => by simp [hh j hj]
      have h5 : HasDerivAt (fun t : ℝ => F (z + t • h) i - (z + t • h) i)
          (fderiv ℝ F z h i - h i) 0 := h3
      rw [h4] at h5
      have := h5.unique (hasDerivAt_const _ _)
      simpa [hK] using this
    have hpow : ∀ (m : ℕ) (h : V n) (i : Fin n), ρ i < m → (K ^ m) h i = 0 := by
      intro m
      induction m with
      | zero => intro h i hi; omega
      | succ m ih =>
        intro h i hi
        rw [pow_succ', Module.End.mul_apply]
        exact hstep i _ fun j hj => ih h j (by omega)
    have hnil : IsNilpotent K := by
      refine ⟨Finset.univ.sup ρ + 1, ?_⟩
      ext h i
      have : ρ i ≤ Finset.univ.sup ρ := Finset.le_sup (Finset.mem_univ i)
      simpa using hpow _ h i (by omega)
    have := det_one_add_of_isNilpotent hnil
    rw [hK, add_sub_cancel] at this
    exact this
  refine ⟨hF.continuous.measurable, ?_⟩
  have := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (V n)) (s := Set.univ)
    (f := F) (f' := fderiv ℝ F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hF x).hasFDerivAt.hasFDerivWithinAt) hb.1.injOn
  simpa [hdet, hb.2.range_eq] using this
end GlobalTheory.UpCoordCompare
