-- Prove2me | solution 1 for GroundTheory.Global.normOneMeasureAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:24.103247+00:00
-- url     : https://prove2.me/submissions/f58682f4-5a13-4bce-9fd1-e13d7293d173

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Theorems.Thm_GroundTheory_Global_map_normOneSplitting_eq_prod_at
import Theorems.Thm_GroundTheory_Global_moduleSection_mul_inv_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (w w' : InfinitePlace K) :
    normOneMeasureAt w' = normOneMeasureAt w := by
  set m := normOneMeasureAt w
  let c : {r : ℝ // 0 < r} → normOneSubgroup K := fun t ↦
    ⟨moduleSection w t * (moduleSection w' t)⁻¹, moduleSection_mul_inv_mem w w' t⟩
  have hc : Continuous c :=
    ((continuous_moduleSection w).mul (continuous_moduleSection w').inv).subtype_mk _
  let φ : normOneSubgroup K × {r : ℝ // 0 < r} → normOneSubgroup K × {r : ℝ // 0 < r} :=
    fun p ↦ (c p.2 * p.1, p.2)
  have hsplit : (normOneSplitting w' : IdeleGroup K → _) = φ ∘ normOneSplitting w := by
    funext x
    refine Prod.ext (Subtype.ext ?_) rfl
    change x * (moduleSection w' (ideleModule K x))⁻¹ =
      moduleSection w (ideleModule K x) * (moduleSection w' (ideleModule K x))⁻¹ *
        (x * (moduleSection w (ideleModule K x))⁻¹)
    generalize moduleSection w (ideleModule K x) = a
    generalize moduleSection w' (ideleModule K x) = b
    rw [show a * b⁻¹ * (x * a⁻¹) = (a * a⁻¹) * (x * b⁻¹) by ac_rfl, mul_inv_cancel, one_mul]
  have hψ : MeasurePreserving (fun p : {r : ℝ // 0 < r} × normOneSubgroup K ↦ (id p.1, c p.1 * p.2))
      (posRealMeasure.prod m) (posRealMeasure.prod m) :=
    (MeasurePreserving.id posRealMeasure).skew_product (g := fun t u ↦ c t * u)
      ((hc.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun t ↦ map_mul_left_eq_self m (c t))
  have hφ : MeasurePreserving φ (m.prod posRealMeasure) (m.prod posRealMeasure) :=
    Measure.measurePreserving_swap.comp (hψ.comp Measure.measurePreserving_swap)
  have hmap : (ideleMeasure K).map (normOneSplitting w') = m.prod posRealMeasure := by
    rw [hsplit, ← Measure.map_map hφ.measurable (map_continuous _).measurable,
      map_normOneSplitting_eq_prod_at w, hφ.map_eq]
  rw [normOneMeasureAt, hmap, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.map_fst_prod, Measure.restrict_apply_univ, posRealMeasure_posRealUnitInterval, one_smul]
end GroundTheory.Global
