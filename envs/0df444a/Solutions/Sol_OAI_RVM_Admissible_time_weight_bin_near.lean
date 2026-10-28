-- Prove2me | solution 1 for OAI.RVM.Admissible.time_weight_bin_near
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:40.015347+00:00
-- url     : https://prove2.me/submissions/d9f0bd33-9540-4bec-bd68-9cdd15dbe246

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_representative_receiver_envelope

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma representativeTimeWeightCost_eq (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) {w I : ℝ} (hw : 0<w) (hI : 0<I) (k : Fin 4→ℕ) (a b : ℝ) :
    representativeTimeWeightCost s F zX w I k a b=
      ENNReal.ofReal (w*cappedRepresentative (k 2)/I)*
        representativeReceiverCost s F zX w k a b (fun _=>1) := by
  have hφ := cappedRepresentative_pos (k 2)
  unfold representativeTimeWeightCost representativeReceiverCost
  dsimp only
  simp only [one_mul]
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

lemma Admissible.time_weight_bin_near_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      representativeTimeWeightCost s F zX w I k a b≤
        ENNReal.ofReal (C*(cappedRepresentative (k 3))^2*(sourceRepresentative (k 0))^3*
          (cappedRepresentative (k 1))^3*cappedRepresentative (k 2)) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_receiver_envelope T₀
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hab hI hJI hw
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have he := hbound s T F hs hT hTT zX k a b w (fun _=>1) ha hb hw measurable_const (by simp)
  dsimp only at he
  rw [lintegral_const,one_mul,Measure.restrict_apply_univ,Real.volume_Icc] at he
  rw [representativeTimeWeightCost_eq s F zX hw hI]
  apply (mul_le_mul' le_rfl he).trans
  calc
    _≤ENNReal.ofReal (w*φ/I)*(ENNReal.ofReal (C*(w⁻¹*(h^2*(p*θ)^3)))*ENNReal.ofReal I) := by
      apply mul_le_mul' le_rfl
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.mpr hw.le)) hC))
        (ENNReal.ofReal_le_ofReal hJI)
    _=ENNReal.ofReal (C*h^2*p^3*θ^3*φ) := by
      rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.time_weight_bin_near_oai := @OAI.RVM.Admissible.time_weight_bin_near_oai
