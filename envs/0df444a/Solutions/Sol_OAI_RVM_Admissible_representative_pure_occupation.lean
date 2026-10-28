-- Prove2me | solution 1 for OAI.RVM.Admissible.representative_pure_occupation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:14:25.292726+00:00
-- url     : https://prove2.me/submissions/bf3307c8-ba14-4dbf-9d3f-c63997609828

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direction_closedEulerian_grid
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_baseline_budget
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_crude_budget

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

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

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


lemma eventually_direction_absorption (C : ℝ) :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ w δ : ℝ, P^(3/5:ℝ)≤w → w^(-3/5:ℝ)≤δ →
        1≤w ∧ 16≤w ∧ P≤w^2 ∧ Real.log (2+P)≤Real.sqrt w ∧
          4*C*(Real.log (2+P))^2≤w*δ := by
  have ht (k : ℕ) (ε : ℝ) (hε : 0<ε) (D : ℝ) :
      ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
    have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
    filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
    have hp0 : 0<P := by linarith
    have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
    have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log (2+P)≤2*Real.log P := by
      calc
        _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
        _=_ := by rw [Real.log_pow]; norm_num
    have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
      simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
        one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
    calc
      D*(Real.log (2+P))^k≤|D| * (Real.log (2+P))^k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _≤|D| * (2*Real.log P)^k := by gcongr
      _=|D*2^k| * (Real.log P)^k := by rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
      _≤_ := hbo
  filter_upwards [ht 1 (3/10) (by norm_num) 1,ht 2 (6/25) (by norm_num) (4*C),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/5)).eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_id)).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with P hroot hcharge h16 hL hP
  refine ⟨hP,hL,?_⟩
  intro w δ hw hδ
  have hp0 := zero_lt_one.trans_le hP
  have hw16 := h16.trans hw
  have hw1 : 1≤w := by linarith
  have hw0 := zero_lt_one.trans_le hw1
  have hsq : P≤w^2 := by
    calc
      P = P^(1:ℝ) := (Real.rpow_one P).symm
      _≤P^(6/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _=(P^(3/5:ℝ))^2 := by rw [←Real.rpow_natCast,←Real.rpow_mul hp0.le]; norm_num
      _≤w^2 := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hw _
  have hs : Real.log (2+P)≤Real.sqrt w := by
    simp only [pow_one,one_mul] at hroot
    apply hroot.trans
    rw [Real.sqrt_eq_rpow]
    calc
      P^(3/10:ℝ) = (P^(3/5:ℝ))^(1/2:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
      _≤w^(1/2:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
  refine ⟨hw1,hw16,hsq,hs,?_⟩
  calc
    4*C*(Real.log (2+P))^2≤P^(6/25:ℝ) := hcharge
    _=(P^(3/5:ℝ))^(2/5:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
    _≤w^(2/5:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
    _=w^(1+(-3/5:ℝ)) := by norm_num
    _=w*w^(-3/5:ℝ) := by rw [Real.rpow_add hw0,Real.rpow_one]
    _≤w*δ := mul_le_mul_of_nonneg_left hδ hw0.le



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PartitionOccupation
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

lemma pureOccupation_crude_scalar {I h H p : ℝ}
    (hI : 0≤I) (hh : 0≤h) (hH : 1≤H) (hp : 0<p) :
    (I+2*H*h)/(p/128)≤(1000000000*H^2)*(max I h/p) := by
  have hR : 0≤ max I h := hI.trans (le_max_left _ _)
  have hIH : I≤H*max I h := (le_max_left _ _).trans (le_mul_of_one_le_left hR hH)
  have hhH : H*h≤H*max I h := mul_le_mul le_rfl (le_max_right _ _) hh (by linarith)
  have hH2 : H≤H^2 := by nlinarith
  have hH0 : 0≤H := by linarith
  calc
    _=128*(I+2*H*h)/p := by ring
    _≤384*H*max I h/p := by
      apply div_le_div_of_nonneg_right _ hp.le
      nlinarith
    _≤(1000000000*H^2)*max I h/p := by gcongr; nlinarith
    _=_ := by ring

lemma pureOccupation_clipped_ratio {I lam h : ℝ} (hI : 0<I) (hlam : 0<lam) :
    1+I/min I (lam/2)≤4*max 1 (max (I/lam) (h/lam)) := by
  let R := max 1 (max (I/lam) (h/lam))
  have hR : 1≤R := le_max_left _ _
  have hIR : I/lam≤R := (le_max_left _ _).trans (le_max_right _ _)
  rcases le_total I (lam/2) with hc|hc
  · rw [min_eq_left hc,div_self hI.ne']; change _≤4*R; linarith
  · rw [min_eq_right hc]
    have he : I/(lam/2)=2*(I/lam) := by field_simp [hlam.ne']
    rw [he]; change _≤4*R; linarith

lemma pureOccupation_stable_scalar {I h H p lam : ℝ}
    (hI : 0<I) (hh : 0≤h) (hH : 1≤H) (hp : 0<p) (hlam : 0<lam) :
    35512320*(2*H*h)/p*(1+I/min I (lam/2))≤
      (1000000000*H^2)*((h/p)*max 1 (max (I/lam) (h/lam))) := by
  have hR : 0≤ max 1 (max (I/lam) (h/lam)) := zero_le_one.trans (le_max_left _ _)
  have hH0 : 0≤H := by linarith
  calc
    _≤35512320*(2*H*h)/p*(4*max 1 (max (I/lam) (h/lam))) :=
      mul_le_mul_of_nonneg_left (pureOccupation_clipped_ratio hI hlam) (by positivity)
    _=(284098560*H)*((h/p)*max 1 (max (I/lam) (h/lam))) := by ring
    _≤_ := by apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith

lemma pureOccupation_improved_scalar {I h H p I₀ φ : ℝ}
    (hh : 0≤h) (hH : 1≤H) (hp : 0<p) (hI₀ : 0<I₀) (hφ : 0≤φ) :
    2*(2*H*h)/(p/128)*φ^(-29/25:ℝ)*max 1 (max (I/I₀) ((2*H*h)/I₀))≤
      (1000000000*H^2)*((h/p)*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (h/I₀))) := by
  let R := max 1 (max (I/I₀) (h/I₀))
  have hR : 1≤R := le_max_left _ _
  have hHH : 1≤2*H := by linarith
  have hH0 : 0≤H := by linarith
  have hR' : max 1 (max (I/I₀) ((2*H*h)/I₀))≤2*H*R := by
    have hIR : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    have hhR : h/I₀≤R := (le_max_right _ _).trans (le_max_right _ _)
    have hR0 : R≤2*H*R := le_mul_of_one_le_left (zero_le_one.trans hR) hHH
    refine max_le (hR.trans hR0) (max_le (hIR.trans hR0) ?_)
    apply (div_le_iff₀ hI₀).mpr
    have hh' := mul_le_mul_of_nonneg_left ((div_le_iff₀ hI₀).mp hhR)
      (by positivity : 0≤2*H)
    simpa only [mul_assoc] using hh'
  calc
    _≤2*(2*H*h)/(p/128)*φ^(-29/25:ℝ)*(2*H*R) :=
      mul_le_mul_of_nonneg_left hR' (by positivity)
    _=(1024*H^2)*((h/p)*φ^(-29/25:ℝ)*R) := by ring
    _≤_ := by apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith

lemma ImprovedWindow.min_mass {P p w φ : ℝ} (h : ImprovedWindow P p w φ) :
    P^(7/10:ℝ)≤ min p w ∧ (min p w)^(-49/100:ℝ)≤φ ∧ φ≤(min p w)^(-4/25:ℝ) := by
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    exact ⟨h.1,h.2.2.1,by convert h.2.2.2.1 using 1; norm_num⟩
  · rw [min_eq_right hwp]
    exact ⟨h.2.1,h.2.2.2.2.1,by convert h.2.2.2.2.2 using 1; norm_num⟩

lemma pureOccupation_of_three {P C₀ C₁ M A p w φ h I K : ℝ} {O E : ℝ≥0∞}
    (hK : 0≤K)
    (h₀ : O≤ENNReal.ofReal (K*(max I h/p))*E)
    (h₁ : C₀/min p w<φ → O≤ENNReal.ofReal (K*((h/p)*max 1
      (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))))*E)
    (h₂ : ImprovedWindow P p w φ → O≤ENNReal.ofReal (K*((h/p)*φ^(-29/25:ℝ)*
      max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))))*E) :
    O≤ENNReal.ofReal (K*pureOccupationEnvelope P C₀ C₁ M A p w φ h I)*E := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs with ha hi hi <;>
    simp only [mul_min_of_nonneg _ _ hK,ENNReal.ofReal_min,min_mul]
  · exact le_min (le_min h₀ (h₁ ha)) (le_min h₀ (h₂ hi))
  · exact le_min (le_min h₀ (h₁ ha)) h₀
  · exact le_min h₀ (le_min h₀ (h₂ hi))
  · exact le_min h₀ h₀

lemma eventually_log_power_le_positive_rpow (k : ℕ) (ε D : ℝ) (hε : 0<ε) :
    ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
  have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
  filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
  have hp0 : 0<P := by linarith
  have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
  have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2+P)≤2*Real.log P := by
    calc
      _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
      _=_ := by rw [Real.log_pow]; norm_num
  have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
    simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
      one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
  calc
    D*(Real.log (2+P))^k≤|D| *(Real.log (2+P))^k :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _≤|D| *(2*Real.log P)^k := by
      have h : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
      gcongr
    _=|D*2^k| *(Real.log P)^k := by
      rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
    _≤_ := hbo

lemma eventually_direction_window :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ m φ : ℝ, P^(7/10:ℝ)≤ m → m^(-49/100:ℝ)≤φ → φ≤ m^(-4/25:ℝ) →
        0 < m ∧ 0<φ ∧ φ≤1 ∧ P^(3/5:ℝ)≤(m/128)/2 ∧
        ((m/128)/2)^(-3/5:ℝ)≤φ/128 ∧
        512≤ m*φ ∧ 2*(φ/128)+2*(((m/128)/2)⁻¹)^2≤φ/16 ∧
        φ≤P^(-14/125:ℝ) := by
  have hc : ∀ᶠ P : ℝ in atTop, 256≤P^(1/10:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop 256
  have hd : ∀ᶠ P : ℝ in atTop, 128*(256:ℝ)^(3/5:ℝ)≤P^(77/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<77/1000)).eventually_ge_atTop _
  have hg : ∀ᶠ P : ℝ in atTop, 512≤P^(357/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<357/1000)).eventually_ge_atTop _
  have he : ∀ᶠ P : ℝ in atTop, 4194304≤P^(1057/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1057/1000)).eventually_ge_atTop _
  filter_upwards [hc,hd,hg,he,eventually_direction_absorption 0] with P hc hd hg he hlarge
  refine ⟨hlarge.1,hlarge.2.1,?_⟩
  intro m φ hPm hlo hhi
  have hP := hlarge.1
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hm1 : 1≤ m := (Real.one_le_rpow hP (by norm_num : (0:ℝ)≤7/10)).trans hPm
  have hm : 0 < m := zero_lt_one.trans_le hm1
  have hφ : 0<φ := (Real.rpow_pos_of_pos hm _).trans_le hlo
  have hφ1 : φ≤1 := hhi.trans (Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num))
  have hexp (α : ℝ) (hα : 0≤α) : P^((7/10)*α)≤ m^α := by
    rw [Real.rpow_mul hP0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hP0.le _) hPm hα
  have hhigh : P^(3/5:ℝ)≤(m/128)/2 := by
    have hh := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hP0.le (3/5))
    rw [←Real.rpow_add hP0] at hh
    norm_num at hh
    linarith
  have hstep : ((m/128)/2)^(-3/5:ℝ)≤φ/128 := by
    have hh : 128*(256:ℝ)^(3/5:ℝ)≤ m^(11/100:ℝ) :=
      hd.trans (by have hh := hexp (11/100) (by norm_num); norm_num at hh; exact hh)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hm.le (-3/5))
    rw [←Real.rpow_add hm] at hh'
    norm_num at hh'
    have heq : ((m/128)/2)^(-3/5:ℝ)=m^(-3/5:ℝ)*(256:ℝ)^(3/5:ℝ) := by
      rw [show m/128/2=m/256 by ring,Real.div_rpow hm.le (by norm_num)]
      have hh : (256:ℝ)^(-3/5:ℝ)=((256:ℝ)^(3/5:ℝ))⁻¹ := by
        rw [show (-3/5:ℝ)=-(3/5) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤256)]
      rw [hh,div_inv_eq_mul]
    rw [heq]
    nlinarith
  have hgeom : 512≤ m*φ := by
    have hh : 512≤ m^(51/100:ℝ) := hg.trans (by have hh := hexp (51/100) (by norm_num); norm_num at hh; exact hh)
    have heq : m^(51/100:ℝ)=m*m^(-49/100:ℝ) := by
      calc
        _=m^((1:ℝ)+(-49/100)) := by norm_num
        _=m^(1:ℝ)*m^(-49/100:ℝ) := Real.rpow_add hm _ _
        _=_ := by rw [Real.rpow_one]
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlo hm.le)
  have hdef : (((m/128)/2)⁻¹)^2≤φ/64 := by
    have hh : 4194304≤ m^(151/100:ℝ) := he.trans (by have hh := hexp (151/100) (by norm_num); norm_num at hh; exact hh)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hm.le (-2))
    rw [←Real.rpow_add hm] at hh'
    norm_num at hh'
    have heq : (((m/128)/2)⁻¹)^2=65536*(m^2)⁻¹ := by field_simp; ring
    rw [heq]
    linarith
  have hupper : φ≤P^(-14/125:ℝ) := by
    apply hhi.trans
    calc
      m^(-4/25:ℝ)≤(P^(7/10:ℝ))^(-4/25:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hP0 _) hPm (by norm_num)
      _=_ := by rw [←Real.rpow_mul hP0.le]; norm_num
  exact ⟨hm,hφ,hφ1,hhigh,hstep,hgeom,by linarith,hupper⟩

lemma eventually_direction_window_absorption (D : ℝ) :
    ∀ᶠ P : ℝ in atTop, ∀ φ : ℝ,0<φ → φ≤P^(-14/125:ℝ) →
      D*(Real.log (2+P))^7≤φ^(-4/25:ℝ) := by
  filter_upwards [eventually_log_power_le_positive_rpow 7 (56/3125) D (by norm_num),
    eventually_gt_atTop (0:ℝ)] with P hlog hP
  intro φ hφ hφP
  calc
    _≤P^(56/3125:ℝ) := hlog
    _=(P^(-14/125:ℝ))^(-4/25:ℝ) := by rw [←Real.rpow_mul hP.le]; norm_num
    _≤φ^(-4/25:ℝ) := Real.rpow_le_rpow_of_nonpos hφ hφP (by norm_num)

lemma directionGridRate_lower (M A L : ℝ) : 131072≤directionGridRate M A L := by
  unfold directionGridRate
  exact le_add_of_nonneg_right (by positivity)

lemma directionGridConstant_pos {M A : ℝ} (hA : 0≤A) : 0<directionGridConstant M A := by
  unfold directionGridConstant
  positivity

lemma directionGridRate_log_bound {M A L : ℝ} (hA : 0≤A) (hL : 1≤L) :
    directionGridRate M A L≤directionGridConstant M A*L := by
  have hAL : 0≤A*L := mul_nonneg hA (zero_le_one.trans hL)
  have hs := Real.sq_sqrt hAL
  have hc := sq_nonneg (M-Real.sqrt (A*L))
  have hML := mul_le_mul_of_nonneg_left hL (sq_nonneg M)
  unfold directionGridRate directionGridConstant
  nlinarith

lemma directionGridLength_scales {P M A L m : ℝ} (hP : 0<P) (hM : 0<M) (hm : 0 < m) :
    let len := (m/P)^2/directionGridRate M A L
    0<len ∧
    2*len≤(128*(P/(m/128))*(M+Real.sqrt (A*L)))⁻¹^2 ∧
    2*len≤((m/128)/2/P)^2 := by
  dsimp only
  let Q := directionGridRate M A L
  let S := M+Real.sqrt (A*L)
  have hQlower : 131072≤Q := directionGridRate_lower M A L
  have hQ : 0<Q := by linarith
  have hS : 0<S := add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
  have hI : 0<(m/P)^2 := sq_pos_of_pos (div_pos hm hP)
  have heq : (128*(P/(m/128))*(M+Real.sqrt (A*L)))⁻¹^2=
      (m/P)^2/(268435456*S^2) := by
    dsimp only [S]
    field_simp
    ring
  refine ⟨div_pos hI hQ,?_,?_⟩
  · rw [heq]
    change 2*((m/P)^2/Q)≤_
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hQ (by positivity : 0<268435456*S^2)).mpr
    have hh : 2*(268435456*S^2)≤Q := by dsimp [Q,directionGridRate,S]; nlinarith
    nlinarith
  · change 2*((m/P)^2/Q)≤_
    have heq' : ((m/128)/2/P)^2=(m/P)^2/65536 := by ring
    rw [heq',←mul_div_assoc]
    apply (div_le_div_iff₀ hQ (by norm_num : (0:ℝ)<65536)).mpr
    nlinarith

lemma direction_grid_count_scalar {I r I₀ Q : ℝ} (hI₀ : 0<I₀) (hQ : 1≤Q) :
    2+(I+r)/(I₀/Q)≤4*Q*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 1≤R := le_max_left _ _
  have hIQ : I≤I₀*R := by
    have hh : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hrQ : r≤I₀*R := by
    have hh : r/I₀≤R := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hQ0 : 0<Q := zero_lt_one.trans_le hQ
  have hdiv : (I+r)/(I₀/Q)≤2*Q*R := by
    apply (div_le_iff₀ (div_pos hI₀ hQ0)).mpr
    have he : 2*Q*R*(I₀/Q)=2*I₀*R := by field_simp
    rw [he]
    linarith
  have hQR : R≤Q*R := le_mul_of_one_le_left (zero_le_one.trans hR) hQ
  change _≤4*Q*R
  linarith

lemma direction_short_occupation_scalar {C Cq L Q I₀ I r q φ : ℝ}
    (hC : 0≤C) (_ : 0≤Cq) (hL : 1≤L) (hQ : 1≤Q) (hQL : Q≤Cq*L)
    (hI₀ : 0<I₀) (hr : 0 ≤ r) (hq : 0<q) (hφ : 0<φ)
    (habs : 1024*C*Cq*L^7≤φ^(-4/25:ℝ)) :
    2*C*r/q*L^6/(φ/128)*(2+(I+r)/(I₀/Q))≤
      r/q*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 0≤R := zero_le_one.trans (le_max_left _ _)
  have hL0 := zero_le_one.trans hL
  have hcount := direction_grid_count_scalar (I:=I) (r:=r) hI₀ hQ
  have hpowers : φ^(-4/25:ℝ)/φ=φ^(-29/25:ℝ) := by
    calc
      _=φ^(-4/25:ℝ)/φ^(1:ℝ) := by rw [Real.rpow_one]
      _=φ^((-4/25)-1:ℝ) := (Real.rpow_sub hφ _ _).symm
      _=_ := by norm_num
  calc
    _≤2*C*r/q*L^6/(φ/128)*(4*Q*R) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _≤2*C*r/q*L^6/(φ/128)*(4*(Cq*L)*R) := by gcongr
    _=(1024*C*Cq*L^7)*(r/q/φ*R) := by ring
    _≤φ^(-4/25:ℝ)*(r/q/φ*R) := mul_le_mul_of_nonneg_right habs (by positivity)
    _=r/q*(φ^(-4/25:ℝ)/φ)*R := by ring
    _=_ := by rw [hpowers]

lemma direction_long_occupation_scalar {I₀ Q I r q φ : ℝ}
    (hI₀ : 0<I₀) (hQ : 1≤Q) (hr : I₀/Q ≤ r) (hq : 0<q)
    (habs : Q≤φ^(-29/25:ℝ)) :
    (I+r)/q≤2*r/q*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 1≤R := le_max_left _ _
  have hQ0 := zero_lt_one.trans_le hQ
  have hr0 : 0 < r := (div_pos hI₀ hQ0).trans_le hr
  have hI₀r : I₀ ≤ r*Q := (div_le_iff₀ hQ0).mp hr
  have hIR : I≤I₀*R := by
    have hh : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hIr : I ≤ r*Q*R := hIR.trans (mul_le_mul_of_nonneg_right hI₀r (zero_le_one.trans hR))
  have hrR : r ≤ r*Q*R := by
    exact (le_mul_of_one_le_right hr0.le hQ).trans (le_mul_of_one_le_right (by positivity) hR)
  calc
    (I+r)/q≤(2*r*Q*R)/q := div_le_div_of_nonneg_right (by linarith) hq.le
    _≤(2*r*φ^(-29/25:ℝ)*R)/q := by gcongr
    _=_ := by ring

lemma Admissible.direction_closedEulerian_improved {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b m φ I : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → b-a≤I →
      m/128≤B.qmin → m/128≤B.wmin →
      P^(7/10:ℝ)≤ m → m^(-49/100:ℝ)≤φ → φ≤ m^(-4/25:ℝ) →
      0<B.rmin → 0≤B.rmax →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (2*B.rmax/B.qmin*φ^(-29/25:ℝ)*
        max 1 (max (I/(m/P)^2) (B.rmax/(m/P)^2)))*ENNReal.ofReal (datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hgrid⟩ := hd₀.direction_closedEulerian_grid T₀ M A hM hA
  let Cq := directionGridConstant M A
  have hCq : 0<Cq := directionGridConstant_pos hA.le
  let D := Cq+1024*C*Cq
  filter_upwards [hgrid,eventually_direction_window,eventually_direction_window_absorption D]
    with P hgrid hwindow habs
  intro s T F hs hT hTT zX B a b m φ I hzX ha hb hab hJI hmq hmw hhigh hlo hhi hr hrmax hd hDlo hDhi hsource HZ
  have hP : 0<P := zero_lt_one.trans_le hwindow.1
  have hL := hwindow.2.1
  obtain ⟨hm,hφ,hφ1,hhigh',hstep,hgeom,hsmall,hφP⟩ := hwindow.2.2 m φ hhigh hlo hhi
  have hq : 0<B.qmin := (by positivity : 0< m/128).trans_le hmq
  have hw : 4≤φ*B.wmin := by
    have hh := mul_le_mul_of_nonneg_left hmw hφ.le
    nlinarith
  let L := Real.log (2+P)
  let Q := directionGridRate M A L
  let I₀ := (m/P)^2
  let len := I₀/Q
  have hI₀ : 0<I₀ := sq_pos_of_pos (div_pos hm hP)
  have hQlower : 131072≤Q := directionGridRate_lower M A L
  have hQ : 1≤Q := by linarith
  have hQL : Q≤Cq*L := directionGridRate_log_bound hA.le hL
  have hscales := directionGridLength_scales (A:=A) (L:=L) hP hM hm
  have hlen : 0<len := hscales.1
  have h7 : L≤L^7 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (show 1≤7 by norm_num))
  have hAbs : D*L^7≤φ^(-4/25:ℝ) := habs φ hφ hφP
  have hAbsShort : 1024*C*Cq*L^7≤φ^(-4/25:ℝ) := by
    apply le_trans _ hAbs
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [D]
    linarith
  have hpowers : φ^(-4/25:ℝ)/φ=φ^(-29/25:ℝ) := by
    calc
      _=φ^(-4/25:ℝ)/φ^(1:ℝ) := by rw [Real.rpow_one]
      _=φ^((-4/25)-1:ℝ) := (Real.rpow_sub hφ _ _).symm
      _=_ := by norm_num
  have hQabs : Q≤φ^(-29/25:ℝ) := by
    calc
      Q≤Cq*L := hQL
      _≤Cq*L^7 := mul_le_mul_of_nonneg_left h7 hCq.le
      _≤D*L^7 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [D]
        nlinarith
      _≤φ^(-4/25:ℝ) := hAbs
      _≤φ^(-4/25:ℝ)/φ := by
        apply (le_div_iff₀ hφ).mpr
        exact mul_le_of_le_one_right (Real.rpow_nonneg hφ.le _) hφ1
      _=_ := hpowers
  by_cases hrad : B.rmax≤len
  · have ho := hgrid s T F hs hT hTT zX B a b (m/128) (φ/128) φ len
      hzX ha hb hab hlen (by positivity) hmq hmw hscales.2.1 hscales.2.2 hhigh' hstep
      (by linarith) hr hrmax hrad hφ hd hDlo hDhi hw hsmall hsource HZ
    have hscalar := direction_short_occupation_scalar hC.le hCq.le hL hQ hQL hI₀ hrmax hq hφ hAbsShort
      (I:=I)
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    calc
      _≤2*C*B.rmax/B.qmin*L^6/(φ/128)*(2+(I+B.rmax)/len) := by
        have hL0 : 0≤L := zero_le_one.trans hL
        gcongr
      _≤B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀)) := hscalar
      _≤_ := by
        have hR : 0≤ max 1 (max (I/I₀) (B.rmax/I₀)) := zero_le_one.trans (le_max_left _ _)
        have hn : 0≤B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀)) := by positivity
        calc
          _≤2*(B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀))) :=
            le_mul_of_one_le_left hn (by norm_num)
          _=_ := by dsimp only [I₀]; ring

  · have ho := F.closedEulerian_crude_budget hs.energyPrefix hT zX B hd₀.2.1 (Icc_subset_Icc ha hb) hJI hr.le hq
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq]
    exact ENNReal.ofReal_le_ofReal (direction_long_occupation_scalar hI₀ hQ (le_of_not_ge hrad) hq hQabs)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.representative_pure_occupation_oai {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal ((1000000000*(max 1 T₀)^2)*pureOccupationEnvelope P 512 16384 M A
        (sourceRepresentative (k 0)) w (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I)*
        ENNReal.ofReal (datumEnergyNumber d₀) := by
  filter_upwards [hd₀.direction_closedEulerian_improved T₀ M A hM hA,eventually_direction_window]
    with P himproved hwindow
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let H₀ := max 1 T₀
  let B := representativeClosedBin T w k
  let E := ENNReal.ofReal (datumEnergyNumber d₀)
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH₀ : 1≤H₀ := le_max_left _ _
  have hHH : H≤H₀ := max_le_max le_rfl hTT
  have hP : 0<P := zero_lt_one.trans_le hwindow.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hwindow.2.1
  have hKH : 1000000000*H^2≤1000000000*H₀^2 := by gcongr
  have hq : 0<B.qmin := by change 0<p/128; positivity
  have hr : 0<B.rmin := representativeClosedBin_radius_pos T w k
  have hrmax : 0≤B.rmax := by change 0≤2*H*h; positivity
  have hd : B.dmax≤φ^2/32 := by
    have hθ := (cappedRepresentative_pos (k 1)).le
    have hh' := sq_le_sq₀ hθ (by positivity : 0≤φ/16) |>.mpr hsmall
    change 8*(cappedRepresentative (k 1))^2≤φ^2/32
    nlinarith
  have hcrude : O≤ENNReal.ofReal ((1000000000*H₀^2)*(max I h/p))*E := by
    have ho := F.closedEulerian_crude_budget hs.energyPrefix hT zX B hd₀.2.1
      (Icc_subset_Icc ha hb) hJI hr.le hq
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq]
    apply ENNReal.ofReal_le_ofReal
    exact (pureOccupation_crude_scalar hI.le hh.le hH hp).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))
  apply pureOccupation_of_three (by positivity : 0≤1000000000*H₀^2) hcrude
  · intro hactual
    let m := min p w/128
    let lam := stabilityLength P 16384 M A p w φ
    let len := min I (lam/2)
    have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
    have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hφ
    have hlen : 0<len := lt_min hI (half_pos hlam)
    have hstable : 2*len≤(128*(P/m)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 := by
      have heq : (128*(P/m)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2=lam := by
        dsimp [lam,stabilityLength,stabilityRate,m]
        congr 2
        ring
      rw [heq]
      have hl : len≤lam/2 := min_le_right _ _
      linarith
    have hmw : m≤B.wmin := by
      change min p w/128≤w/8
      have he := min_le_right p w
      linarith
    have hmq : m≤B.qmin := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hwφ : 4≤φ*B.wmin := by
      have hmin : 0 < min p w := lt_min hp hw
      have he := (div_lt_iff₀ hmin).mp hactual
      have he' := mul_le_mul_of_nonneg_left (min_le_right p w) hφ.le
      change 4≤φ*(w/8)
      nlinarith
    have ho := F.closedEulerian_baseline_budget hs.energyPrefix hT zX B hd₀.2.1 (k 0) (k 2)
      (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen (min_le_left _ _) hJI
      hM hA.le hP hL hm hφ (cappedRepresentative_le_one _) (by norm_num : (128:ℝ)≤128)
      hstable le_rfl le_rfl hmq hmw hr hrmax hd le_rfl le_rfl hwφ (HZ zX hzX) HZ
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact (pureOccupation_stable_scalar hI hh.le hH hp hlam).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))
  · intro hwin
    obtain ⟨hhigh,hlo,hhi⟩ := hwin.min_mass
    have hmq : min p w/128≤B.qmin := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hmw : min p w/128≤B.wmin := by
      change min p w/128≤w/8
      have hh' := min_le_right p w
      linarith
    have ho := himproved s T F hs hT hTT zX B a b (min p w) φ I hzX ha hb hab hJI hmq hmw
      hhigh hlo hhi hr hrmax hd le_rfl le_rfl hsource HZ
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hI₀ : 0<(min p w/P)^2 := sq_pos_of_pos (div_pos (lt_min hp hw) hP)
    exact (pureOccupation_improved_scalar (I:=I) hh.le hH hp hI₀ hφ.le).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.representative_pure_occupation_oai := @OAI.RVM.Admissible.representative_pure_occupation_oai
