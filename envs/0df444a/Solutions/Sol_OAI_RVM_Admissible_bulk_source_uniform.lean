-- Prove2me | solution 1 for OAI.RVM.Admissible.bulk_source_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:33:03.844965+00:00
-- url     : https://prove2.me/submissions/fb7b03f9-06bb-4302-907f-3e7ebaa815b7

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_good_structural_uniform
import Theorems.Thm_OAI_RVM_Admissible_magnetic_small_uniform
import Theorems.Thm_OAI_RVM_Admissible_representative_pure_occupation
import Theorems.Thm_OAI_RVM_Admissible_uniform_actual_bin_Cauchy
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform
import Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkSource_cost_sum

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma dyadicWindow_one_sqrt {D : ℝ} (j : ℕ)
    (hlo : ((2:ℝ)^j)⁻¹^2/2≤D) (hhi : D≤8*((2:ℝ)^j)⁻¹^2) :
    DyadicWindow 1 j (Real.sqrt (D/2)) := by
  have hp : 0<(2:ℝ)^j := by positivity
  have hi : 0<((2:ℝ)^j)⁻¹ := inv_pos.mpr hp
  have hD0 : 0≤D := (by positivity : 0≤((2:ℝ)^j)⁻¹^2/2).trans hlo
  have hD : 0≤D/2 := by positivity
  have hsq := Real.sq_sqrt hD
  have hlo' : ((2:ℝ)^j)⁻¹/2≤Real.sqrt (D/2) := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  have hhi' : Real.sqrt (D/2)≤2*((2:ℝ)^j)⁻¹ := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo' hp.le
    simpa only [pow_one,← mul_div_assoc,mul_inv_cancel₀ hp.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hhi' hp.le
    simpa only [pow_one,mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one] using hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicCut
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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_dyadicCut : ContDiff ℝ ∞ dyadicCut :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
lemma contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCut.sub (contDiff_dyadicCut.comp (contDiff_const.mul contDiff_id))

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_support : tsupport dyadicBump ⊆ Icc (1/2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hx (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

lemma hasDerivAt_dyadicFactor (n : ℕ) (x : ℝ) :
    HasDerivAt (dyadicFactor n) ((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) x := by
  have hh := ((contDiff_dyadicBump.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul ((2:ℝ)^n))
  change HasDerivAt (fun y => dyadicBump ((2:ℝ)^n*y)) _ x
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using hh

lemma dyadicFactor_log_derivative_bound : ∃ C : ℝ, 0≤C ∧
    ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C := by
  have hd : Continuous (deriv dyadicBump) := contDiff_dyadicBump.continuous_deriv (by simp)
  have hcon : Continuous (fun x : ℝ => x*deriv dyadicBump x) := continuous_id.mul hd
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hcon).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,fun n x => ?_⟩
  rw [(hasDerivAt_dyadicFactor n x).deriv]
  have he : x*((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) =
      ((2:ℝ)^n*x)*deriv dyadicBump ((2:ℝ)^n*x) := by ring
  rw [he]
  by_cases hx : (2:ℝ)^n*x ∈ Icc (1/2:ℝ) 2
  · exact (hC _ ⟨(2:ℝ)^n*x,hx,rfl⟩).trans (le_max_right _ _)
  · rw [deriv_of_notMem_tsupport (fun h => hx (dyadicBump_support h)),mul_zero,abs_zero]
    exact le_max_left _ _

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

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

lemma finset_subset_dyadicBox {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) :
    ∃M : ℕ,S⊆dyadicBox ι M := by
  classical
  obtain ⟨M,hM⟩ := (S.biUnion (fun k=>Finset.univ.image k)).exists_nat_subset_range
  refine ⟨M,?_⟩
  intro k hk
  simp only [dyadicBox,Fintype.mem_piFinset]
  intro i
  apply hM
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology

namespace RVM

lemma pureOccupationEnvelope_nonneg
    {P C₀ C₁ M A p w φ h I : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hh : 0 ≤ h) (hI : 0 ≤ I) :
    0 ≤ pureOccupationEnvelope P C₀ C₁ M A p w φ h I := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs <;> positivity

end RVM

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

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_QuadIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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

lemma tsum_quad_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'np,∑'nt,∑'nf,∑'nr,f ![np,nt,nf,nr] := by
  have h := quadIndexEquiv.symm.tsum_eq f
  rw [←h]
  simp only [ENNReal.tsum_prod']
  rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCutoffs
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

namespace RVM

lemma sqrt_near_product {a b I E r φ D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hI : 0≤I) (hE : 0≤E) (hr : 0 ≤ r) (hφ : 0≤φ) (hD : 0≤D) :
    Real.sqrt (a*E)*Real.sqrt (D^2*(b*I*r*φ^2))=
      D*φ*Real.sqrt (a*I)*Real.sqrt (b*E)*Real.sqrt r := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hD]
  calc
    _ = D*Real.sqrt ((a*E)*(b*I*r*φ^2)) := by
      rw [Real.sqrt_mul (mul_nonneg ha hE)]
      ring
    _ = D*Real.sqrt ((a*I)*(b*E)*r*φ^2) := by congr 2; ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)*r),
        Real.sqrt_sq hφ,Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)),
        Real.sqrt_mul (mul_nonneg ha hI)]
      ring

end RVM

end

open Set Filter Metric MeasureTheory
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
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

lemma Admissible.representative_good_Cauchy {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let B := representativeClosedBin T w k
      let O := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
          (max 0 (a-B.rmax)) (min T (b-B.rmin)))
      let E := datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
            (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_bin_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' _ _) le_rfl
        · rw [Real.volume_Icc]
          exact ENNReal.ofReal_le_ofReal hab
        · apply ENNReal.ofReal_le_ofReal
          rw [hBmax,hBmin]
          linarith only [hr]
      _ = _ := by rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)≤
      ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*datumEnergyNumber d)) := mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0 < r/2; positivity) (by change 0<φ^2/2; positivity)
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  unfold representativeGoodCost
  dsimp only
  apply mul_le_mul' le_rfl
  apply hbnd.trans
  apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact min_le_min (mul_le_mul' le_rfl hmeasure) le_rfl

lemma direct_good_near_scalar {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*(H*h)*φ^2)))=
    (128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
  rw [sqrt_near_product (by positivity : 0≤20*I) (by norm_num : (0:ℝ)≤768)
    hI hE (mul_nonneg hH hh) hφ (by positivity)]
  rw [show (20:ℝ)*I*I=20*(I:ℝ)^2 from by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤20),Real.sqrt_sq hI,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤768),Real.sqrt_mul hH]
  have he : Real.sqrt (20:ℝ)*Real.sqrt 768=Real.sqrt 15360 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤20)]
    norm_num
  calc
    _ = (128*C*(Real.sqrt 20*Real.sqrt 768)*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
      field_simp
    _ = _ := by rw [he]

lemma direct_good_far_sqrt {C K E p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 0<H) (hh : 0<h) (hφ : 0<φ) :
    Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8)))=
      Real.sqrt (1024*C*K*E)*p*θ*Real.sqrt (p*O)/(H*h*φ) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤1024*C*K*E),
    Real.sq_sqrt (mul_nonneg hp.le hO)]
  field_simp
  ring

lemma direct_good_far_scalar {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8))))≤
      (Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [direct_good_far_sqrt hC hK hE hp hθ hO hH0 hh hφ]
  have hsq : Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E)=
      Real.sqrt (20480*C*K)*E*Real.sqrt I := by
    rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
    rw [show (20*I*E)*(1024*C*K*E)=((20480*C*K)*E^2)*I by ring,
      Real.sqrt_mul (by positivity : 0≤(20480*C*K)*E^2),
      Real.sqrt_mul (by positivity : 0≤20480*C*K),Real.sqrt_sq hE]
  calc
    _ = ((Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E))*Real.sqrt (p*O)/(θ*h))/H := by
      field_simp
    _ = ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)))/H := by
      rw [hsq]
      ring
    _ ≤ _ := div_le_self (by positivity) hH

lemma direct_good_near_ennreal {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ))=
    ENNReal.ofReal ((128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2)) := by
  rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*θ^2),
    ←ENNReal.ofReal_mul (sq_nonneg _),ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    direct_good_near_scalar hC hI hE hH hh hφ hp hθ]

lemma direct_good_far_ennreal {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))*(ENNReal.ofReal (K*O)*ENNReal.ofReal E/
        ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ))≤
    ENNReal.ofReal ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h))) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [←ENNReal.ofReal_mul (by positivity : 0≤K*O),
    ←ENNReal.ofReal_div_of_pos (by positivity : 0<(H*h)^2*φ^2/8),
    ←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (direct_good_far_scalar hC hK hE hI hp hθ hO hH hh hφ)

lemma selectionDecay_pos : 0 < selectionDecay := Real.rpow_pos_of_pos (by norm_num) _
lemma selectionDecay_lt_one : selectionDecay<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma selectionDecay_pow (n : ℕ) :
    selectionDecay^n=((2:ℝ)^n)^(-1/100000:ℝ) := by
  rw [selectionDecay,←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma cappedRepresentative_selection_pow (n : ℕ) :
    (cappedRepresentative n)^(1/100000:ℝ)=selectionDecay^n := by
  rw [selectionDecay_pow]
  dsimp [cappedRepresentative]
  rw [inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
  congr 1
  norm_num

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np ≤ cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma selectionWeight_gap_bound {P : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : sourceRepresentative N≤P) (h0 : k 0≤N) (h1 : k 1≤k 0+6) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤
      selectionDecay^(N-k 0)*selectionDecay^(k 0+6-k 1)*selectionDecay^(k 2)*selectionDecay^(k 3) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hN := sourceRepresentative_two_pow N
  have hle : k 1≤N+6 := by omega
  have hid : sourceRepresentative N*cappedRepresentative (k 1)=(2:ℝ)^(N+6-k 1) := by
    rw [hN]
    dsimp [cappedRepresentative]
    rw [inv_pow, pow_sub₀ (2:ℝ) (by norm_num) hle]
  have hdec : (P*cappedRepresentative (k 1))^(-1/100000:ℝ)≤ selectionDecay^(N+6-k 1) := by
    rw [selectionDecay_pow,←hid]
    exact Real.rpow_le_rpow_of_nonpos (by rw [hN]; positivity)
      (mul_le_mul_of_nonneg_right hP hθ.le) (by norm_num)
  have he : N+6-k 1=(N-k 0)+(k 0+6-k 1) := by omega
  unfold selectionWeight
  rw [cappedRepresentative_selection_pow,cappedRepresentative_selection_pow]
  rw [he,pow_add] at hdec
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdec
    (pow_nonneg selectionDecay_pos.le _)) (pow_nonneg selectionDecay_pos.le _)

lemma sum_selectionDecay (N : ℕ) :
    ∑n∈Finset.range N,selectionDecay^n≤(1-selectionDecay)⁻¹ := by
  have hr : |selectionDecay|<1 := by rw [abs_of_pos selectionDecay_pos]; exact selectionDecay_lt_one
  exact ((summable_geometric_of_abs_lt_one hr).sum_le_tsum (Finset.range N)
    (fun _ _=>pow_nonneg selectionDecay_pos.le _)).trans_eq (tsum_geometric_of_abs_lt_one hr)

lemma sum_selectionDecay_box (N : ℕ) :
    ∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  classical
  have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
      (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  have hh := Finset.sum_prod_piFinset (Finset.range N) (fun (_i : Fin 4) (n : ℕ)=>selectionDecay^n)
  rw [heq] at hh
  have hsum : (∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i))=
      (∑n∈Finset.range N,selectionDecay^n)^4 := by
    simpa [dyadicBox,Fin.prod_univ_four,pow_succ] using hh
  rw [hsum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))
    (sum_selectionDecay N) 4

lemma sum_selectionDecay_finset (S : Finset (Fin 4→ℕ)) :
    ∑k∈S,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  obtain ⟨N,hN⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _=>Finset.prod_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))).trans
    (sum_selectionDecay_box N)

lemma sum_selectionWeight (S : Finset (Fin 4→ℕ)) {P : ℝ}
    (hP : ∀k∈S,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈S,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1)) :
    ∑k∈S,selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤((1-selectionDecay)⁻¹)^4 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.sup (fun k=>k 0)
    have hN (k) (hk : k∈S) : k 0≤N := Finset.le_sup (f:=fun k : Fin 4→ℕ=>k 0) hk
    have hNP : sourceRepresentative N≤P := by
      obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup S hS (fun k=>k 0)
      change sourceRepresentative (S.sup (fun k : Fin 4→ℕ=>k 0))≤P
      rw [he]
      exact hP k hk
    let g : (Fin 4→ℕ)→(Fin 4→ℕ) := fun k=>![N-k 0,k 0+6-k 1,k 2,k 3]
    have hg : Set.InjOn g ↑S := by
      intro k hk l hl hkl
      have hk1 := selection_angle_index (hθ k hk)
      have hl1 := selection_angle_index (hθ l hl)
      have h00 := congrFun hkl 0
      have h11 := congrFun hkl 1
      have h22 := congrFun hkl 2
      have h33 := congrFun hkl 3
      change N-k 0=N-l 0 at h00
      change k 0+6-k 1=l 0+6-l 1 at h11
      change k 2=l 2 at h22
      change k 3=l 3 at h33
      have hk0 := hN k hk
      have hl0 := hN l hl
      have h0e : k 0=l 0 := by omega
      have h1e : k 1=l 1 := by omega
      apply funext
      intro i
      fin_cases i
      · exact h0e
      · exact h1e
      · exact h22
      · exact h33
    calc
      _≤∑k∈S,∏i,selectionDecay^(g k i) := Finset.sum_le_sum (fun k hk=>by
        simpa [g,Fin.prod_univ_four] using selectionWeight_gap_bound hNP (hN k hk) (selection_angle_index (hθ k hk)))
      _=∑k∈S.image g,∏i,selectionDecay^(k i) := (Finset.sum_image (f:=fun k : Fin 4→ℕ=>∏i,selectionDecay^(k i)) (fun k hk l hl he=>hg hk hl he)).symm
      _≤_ := sum_selectionDecay_finset _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

lemma Admissible.representative_good_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeGoodCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P 512 16384 M A p w φ h I)/(θ*h))) := by
  obtain ⟨Cg,hCg,hcauchy⟩ := hd.representative_good_Cauchy
  let E := datumEnergyNumber d
  let H₀ := max 1 T₀
  let K := 1000000000*H₀^2
  let Cn := 128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H₀
  let Cf := Real.sqrt (20480*Cg*K)*E
  let C := max Cn Cf
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hK : 0≤K := by dsimp [K]; positivity
  have hCn : 0≤Cn := by dsimp [Cn]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hC : 0≤C := hCn.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hd.representative_pure_occupation T₀ M A hM hA] with P hoccup
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
      (max 0 (a-B.rmax)) (min T (b-B.rmin)))
  let U := pureOccupationEnvelope P 512 16384 M A p w φ h I
  let D := ENNReal.ofReal (128*Cg*p^3*θ^2)
  let N := I*Real.sqrt h*p^2*φ^2
  let R := Real.sqrt I*Real.sqrt (p*U)/(θ*h)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH
  have hHH : H≤H₀ := max_le_max le_rfl hTT
  have hU : 0≤U := pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI.le
  have hN : 0≤N := by dsimp [N]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hc := hcauchy s T F hs hT zX k a b I w ha hb hI hJI
  change representativeGoodCost s F zX w k a b≤
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
        (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) at hc
  have ho : O≤ENNReal.ofReal (K*U)*ENNReal.ofReal E :=
    hoccup s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)))
      _ = ENNReal.ofReal ((128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*N) :=
        direct_good_near_ennreal hCg hI.le hE hH0 hh.le hφ.le hp hθ
      _ ≤ ENNReal.ofReal (C*N) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hN
        apply le_trans _ (le_max_left _ _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHH) (by positivity)
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D*(ENNReal.ofReal (K*U)*ENNReal.ofReal E/ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ)) := by
        apply mul_le_mul' le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact (min_le_right _ _).trans (mul_le_mul' le_rfl (ENNReal.div_le_div_right ho _))
      _ ≤ ENNReal.ofReal (Cf*R) := direct_good_far_ennreal hCg hK hE hI.le hp hθ hU hH hh hφ
      _ ≤ ENNReal.ofReal (C*R) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

lemma selectionWeight_nonneg {P θ φ h : ℝ} (hP : 0≤P) (hθ : 0≤θ) (hφ : 0≤φ) (hh : 0≤h) :
    0 ≤ selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selection_weighted_tsum {P c : ℝ} (hP0 : 0≤P) (hc : 0 ≤ c)
    (Q : Set (Fin 4→ℕ)) (hP : ∀k∈Q,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈Q,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1))
    (f : (Fin 4→ℕ)→ℝ≥0∞)
    (hf : ∀k∈Q,f k≤ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) :
    (∑'k,Q.indicator f k)≤ENNReal.ofReal (c*((1-selectionDecay)⁻¹)^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun k=>k∈Q)
  have hU (k) (hk : k∈U) : k∈Q := (Finset.mem_filter.mp hk).2
  have hsum : (∑k∈S,Q.indicator f k)=∑k∈U,f k := by simp [U,Finset.sum_filter,indicator_apply]
  rw [hsum]
  calc
    _ ≤ ∑k∈U,ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := Finset.sum_le_sum (fun k hk=>hf k (hU k hk))
    _ = ENNReal.ofReal (c*(∑k∈U,selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun k _=>mul_nonneg hc
        (selectionWeight_nonneg hP0 (cappedRepresentative_pos _).le
          (cappedRepresentative_pos _).le (cappedRepresentative_pos _).le)),Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_selectionWeight U (fun k hk=>hP k (hU k hk)) (fun k hk=>hθ k (hU k hk))) hc)

lemma Admissible.unselected_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*P*Real.sqrt I) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_good_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hbound M A hM hA,eventually_ge_atTop (1:ℝ)] with P hbnd hP
  intro s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hsource HZ
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  have hh := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*P*Real.sqrt I)
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>representativeGoodCost s F zX w k a b) (fun k hk=>by
      have he := hbnd s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hk.1.2.2 hsource HZ
      have hnot := le_of_not_gt hk.2
      exact he.trans (ENNReal.ofReal_le_ofReal (by
        have hmul := mul_le_mul_of_nonneg_left hnot hC
        simpa only [mul_assoc] using hmul)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory
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


lemma tsum_quad_pair_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'n : ℕ×ℕ,∑'nt : ℕ,∑'nr : ℕ,f ![n.1,nt,n.2,nr] := by
  rw [tsum_quad_index,ENNReal.tsum_prod']
  apply tsum_congr
  intro np
  exact ENNReal.tsum_comm

lemma tsum_centralIndexSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(centralIndexSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative n.2/16
          then f ![n.1,nt,n.2,nr] else 0) n := by
  classical
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈centralIndexSector P) ↔
        cappedRepresentative nt ≤ cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
        cappedRepresentative nt ≤ cappedRepresentative n.2/16) ↔_
      simp only [hn.1,hn.2,true_and]
    simp only [indicator_apply,hi]
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn']
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    change ¬(sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
      cappedRepresentative nt ≤ cappedRepresentative n.2/16)
    exact fun h=>hn ⟨h.1,h.2.1⟩

lemma representativeSmallSector_subset_centralIndexSector (P : ℝ) :
    representativeSmallSector P⊆centralIndexSector P := by
  intro k hk
  refine ⟨hk.1,hk.2.1.trans (hk.2.2.trans ?_),hk.2.2⟩
  have hφ := (cappedRepresentative_pos (k 2)).le
  linarith



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SpatialEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma tsum_structuralCentralSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,({k | k∈centralIndexSector P ∧
      cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1)}).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧
          cappedRepresentative nt ≤ cappedRepresentative n.2/16 then f ![n.1,nt,n.2,nr] else 0) n := by
  have he : ({k | k∈centralIndexSector P ∧
      cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1)}).indicator f=
      (centralIndexSector P).indicator (fun k=>if cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1) then f k else 0) := by
    funext k
    simp only [indicator_apply,mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,tsum_centralIndexSector]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn',indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    split_ifs <;> simp_all
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn',indicator_of_notMem hn']

lemma Admissible.bulk_source_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'k : Fin 4→ℕ,(bulkSourceBoundary P M A w I).indicator
        (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hstruct⟩ := hd.good_structural_uniform T₀
  obtain ⟨Cu,hCu,hunsel⟩ := hd.unselected_good_uniform T₀
  refine ⟨Cs+Cu,add_nonneg hCs hCu,?_⟩
  intro M A hM hA
  filter_upwards [hunsel M A (zero_lt_one.trans_le hM) hA] with P hu
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  let f := fun k=>representativeGoodCost s F zX w k a b
  let S := {k | k∈centralIndexSector P ∧ cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1)}
  let U := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hPB : P*Real.sqrt I≤B := le_add_of_nonneg_right (by positivity)
  have hbnd : (∑'k,(bulkSourceBoundary P M A w I).indicator f k)≤
      (∑'k,S.indicator f k)+(∑'k,U.indicator f k) := by
    rw [←ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈bulkSourceBoundary P M A w I
    · rw [indicator_of_mem hk]
      rcases hk.2 with hstr|htr
      · have hks : k∈S := ⟨representativeSmallSector_subset_centralIndexSector P hk.1,hstr⟩
        rw [indicator_of_mem hks]
        exact le_add_right le_rfl
      · have hku : k∈U := ⟨hk.1,htr.1⟩
        rw [indicator_of_mem hku]
        exact le_add_left le_rfl
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hst : (∑'k,S.indicator f k)≤ENNReal.ofReal (Cs*B) := by
    rw [show S={k | k∈centralIndexSector P ∧ cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1)} by rfl,
      tsum_structuralCentralSector]
    exact hstruct M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have hun : (∑'k,U.indicator f k)≤ENNReal.ofReal (Cu*(P*Real.sqrt I)) := by
    simpa only [mul_assoc] using hu s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI
      (zero_lt_one.trans_le hw) hsource HZ
  apply hbnd.trans
  calc
    _≤ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cu*(P*Real.sqrt I)) := add_le_add hst hun
    _≤ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cu*B) := add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPB hCu))
    _=ENNReal.ofReal ((Cs+Cu)*B) := by
      rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCu hB)]; congr 1; ring


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MagneticEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_source_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
        (coneSourceCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hgood⟩ := hd.bulk_source_good_uniform T₀
  obtain ⟨Cm,hCm,hmag⟩ := hd.magnetic_small_uniform T₀
  obtain ⟨Cd,hCd,hder⟩ := dyadicFactor_log_derivative_bound
  refine ⟨99840000*Cd*(Cs+Cm),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hgood M A hM hA] with P hg
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource hphysical hband HZ W hW hW1
  let R := bulkSourceBoundary P M A w I
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hmg : (∑'k : Fin 4→ℕ,R.indicator (fun k=>representativeMagneticCost s F zX w k a b) k)≤
      ENNReal.ofReal (Cm*B) := by
    calc
      _≤∑'k : Fin 4→ℕ,(centralIndexSector P).indicator (fun k=>representativeMagneticCost s F zX w k a b) k := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k∈R
        · rw [indicator_of_mem hk,indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
        · rw [indicator_of_notMem hk]; exact bot_le
      _≤_ := by
        rw [tsum_centralIndexSector]
        exact hmag M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have hgd := hg hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  have hsum : (∑'k : Fin 4→ℕ,R.indicator
      (fun k=>representativeGoodCost s F zX w k a b+representativeMagneticCost s F zX w k a b) k)≤
      ENNReal.ofReal ((Cs+Cm)*B) := by
    rw [show R.indicator (fun k=>representativeGoodCost s F zX w k a b+representativeMagneticCost s F zX w k a b)=
      (fun k=>R.indicator (fun k=>representativeGoodCost s F zX w k a b) k+
        R.indicator (fun k=>representativeMagneticCost s F zX w k a b) k) by
          funext k; simp only [indicator_add],ENNReal.tsum_add]
    apply (add_le_add hgd hmg).trans_eq
    rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCm hB)]
    congr 1; ring
  apply (F.bulkSource_cost_sum hs.energyPrefix hT zX ha hb hband hphysical hW hW1 hCd hder).trans
  apply (mul_le_mul' le_rfl hsum).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity : 0≤99840000*Cd)]
  congr 1; ring

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.bulk_source_uniform_oai := @OAI.RVM.Admissible.bulk_source_uniform_oai
