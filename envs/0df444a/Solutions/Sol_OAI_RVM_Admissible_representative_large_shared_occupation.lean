-- Prove2me | solution 1 for OAI.RVM.Admissible.representative_large_shared_occupation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:13:05.576016+00:00
-- url     : https://prove2.me/submissions/90514503-3098-4be2-85d3-6e5d03488317

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_joint_large_budget
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_representativeJointEnergy_sum

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma representativeClosedBin_radius_pos (T w : ℝ) (k : Fin 4→ℕ) :
    0<(representativeClosedBin T w k).rmin := by
  have h : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  dsimp [representativeClosedBin,cappedRepresentative]
  positivity

end RVM

end

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

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SqrtBaselineClippedLength
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

lemma stabilityLength_pos {P C M A p w φ : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) :
    0 < stabilityLength P C M A p w φ := by
  unfold stabilityLength stabilityRate
  have hm : 0 < min p w := lt_min hp hw
  have hr : 0  <  M/φ+Real.sqrt (A*Real.log (2+P)/φ) :=
    add_pos_of_pos_of_nonneg (div_pos hM hφ) (Real.sqrt_nonneg _)
  positivity

end RVM

end

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
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



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.datumEnergyNumber_nonneg {d : Datum} (hd : Admissible d) :
    0≤datumEnergyNumber d := by
  apply integral_nonneg
  intro x
  apply add_nonneg (by positivity)
  exact integral_nonneg (fun v=>mul_nonneg (q_pos v).le (hd.2.2.1 _))

lemma SmoothClassicalPrefix.initial_energy_eq {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) :
    (∫x : Vec,totalEnergy s (0,x))=datumEnergyNumber d := by
  unfold totalEnergy particleEnergy datumEnergyNumber
  simp only [hs.initial_E,hs.initial_B,hs.initial_f]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

open Set MeasureTheory
open scoped ENNReal

end

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma representativeJointEnergy_nonneg {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (n : ℕ×ℕ) :
    0 ≤ representativeJointEnergy s F zX a b I n := ENNReal.toReal_nonneg

lemma shared_budget_radius_scalar {E J I lam : ℝ} (hE : 0≤E) (hJ : 0≤J)
    (hJE : J≤3468*E) (hI : 0<I) (hlam : 0<lam) :
    E+I/min I (lam/2)*J≤(2+3469*E)*(1+Real.sqrt (I/lam)*Real.sqrt J)^2 := by
  have hratio : I/min I (lam/2)≤1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']; linarith [div_pos hI hlam]
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  have hs : 0≤Real.sqrt (I/lam)*Real.sqrt J := by positivity
  have he : (Real.sqrt (I/lam)*Real.sqrt J)^2=(I/lam)*J := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hJ]
  have hprod := mul_le_mul_of_nonneg_right hratio hJ
  have hpos : 0≤3469*E*(1+Real.sqrt (I/lam)*Real.sqrt J)^2 := by positivity
  nlinarith [sq_nonneg (Real.sqrt (I/lam)*Real.sqrt J),
    mul_nonneg hE hs,mul_nonneg hE (sq_nonneg (Real.sqrt (I/lam)*Real.sqrt J))]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CentralOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.representative_large_shared_occupation_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
        (cappedRepresentative (k 2))) < cappedRepresentative (k 3) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (C*cappedRepresentative (k 3)/sourceRepresentative (k 0)*
        (representativeSharedRadius s F zX P M A w a b I (k 0,k 2))^2) := by
  let E := datumEnergyNumber d
  let C := 20480*(max 1 T₀)*(2+3469*E)
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hlarge
  dsimp only
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let m := min p w/128
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let J := representativeJointEnergy s F zX a b I (k 0,k 2)
  let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hHH : H≤ max 1 T₀ := max_le_max le_rfl hTT
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hφ
  have hlen : 0<len := lt_min hI (half_pos hlam)
  have hlenr : len<B.rmax := by
    have hl : len ≤ min I lam := min_le_min le_rfl (by linarith)
    have hr0 : h≤2*H*h := by nlinarith
    exact (hl.trans_lt hlarge).trans_le hr0
  have ho := F.closedEulerian_joint_large_budget hs.energyPrefix hT zX B hd.2.1 (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen (min_le_left _ _) hJI
    le_rfl le_rfl (representativeClosedBin_radius_pos T w k)
    (by change 0≤2*H*h; positivity) hlenr le_rfl le_rfl
  obtain ⟨hsum,hbudget,hJof⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  have hJ0 : 0≤J := representativeJointEnergy_nonneg _ _ _ _ _ _ _
  have hJE : J≤3468*E := (hsum.le_tsum (k 0,k 2) (fun _ _=>representativeJointEnergy_nonneg _ _ _ _ _ _ _)).trans hbudget
  rw [hs.initial_energy_eq,hJof] at ho
  have hrad := shared_budget_radius_scalar hE hJ0 hJE hI hlam
  change E+I/len*J≤(2+3469*E)*R^2 at hrad
  rw [←ENNReal.ofReal_mul (by positivity : 0≤I/len),
    ←ENNReal.ofReal_add hE (by positivity),←ENNReal.ofReal_mul (by change 0≤10240*(2*H*h)/p; positivity : 0≤10240*B.rmax/p)] at ho
  apply ho.trans
  apply ENNReal.ofReal_le_ofReal
  change 10240*(2*H*h)/p*(E+I/len*J)≤C*h/p*R^2
  calc
    _≤10240*(2*H*h)/p*((2+3469*E)*R^2) := mul_le_mul_of_nonneg_left hrad (by positivity)
    _=(20480*H*(2+3469*E))*h/p*R^2 := by ring
    _≤_ := by dsimp [C]; gcongr

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.representative_large_shared_occupation_oai := @OAI.RVM.Admissible.representative_large_shared_occupation_oai
