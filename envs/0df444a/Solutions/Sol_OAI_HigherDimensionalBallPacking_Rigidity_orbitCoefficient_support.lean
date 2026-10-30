-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:54.762161+00:00
-- url     : https://prove2.me/submissions/0f60d111-3562-4fe9-8bd8-fa595a34884d

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp006
import Definitions.Def_OAIQ10Bp004
import Definitions.Def_OAIQ10Bp008

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrameFredholm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
section
universe v
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c1HolderValue_bound (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    ‖holderValue α (c1HolderValue α u) x‖ ≤ ‖u‖ :=
  ((holderValue α (c1HolderValue α u)).norm_coe_le_norm x).trans
    ((le_max_left _ _).trans (le_max_left _ _))

end

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter





open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped ContDiff Topology
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem affineProfile_lower_bound (c d v : E) (A B : ℂ →L[ℝ] E) (m U R t : ℝ)
    (_hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖A z‖) (hd : ‖d‖≤1) (hB : ‖B‖≤ m/2)
    (hv : ‖v‖≤U) (ht : t∈Icc (0:ℝ) 1) (z : ℂ)
    (hz : R+‖c‖+1+U ≤ m/2*‖z‖) :
    R ≤ ‖c+A z+t • (d+B z)+v‖ := by
  have hb : ‖t • (d+B z)‖ ≤ 1+(m/2)*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    calc
      t*‖d+B z‖ ≤ ‖d+B z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
      _ ≤ ‖d‖+‖B z‖ := norm_add_le _ _
      _ ≤ 1+‖B‖*‖z‖ := add_le_add hd (B.le_opNorm z)
      _ ≤ 1+(m/2)*‖z‖ := add_le_add (le_refl 1) (mul_le_mul_of_nonneg_right hB (norm_nonneg z))
  have hrev : ‖A z‖ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by
    calc
      ‖A z‖ = ‖(c+A z+t • (d+B z)+v)-(c+t • (d+B z)+v)‖ := by congr 1; abel
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c+t • (d+B z)+v‖ := norm_sub_le _ _
      _ ≤ ‖c+A z+t • (d+B z)+v‖+((‖c‖+‖t • (d+B z)‖)+‖v‖) :=
        add_le_add (le_refl _) ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by linarith
  have ha := hA z
  linarith

 

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem compactCoefficient_zero_outside {f : E → F} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0<R ∧ ∀ x, R≤‖x‖ → f x=0 := by
  obtain ⟨R,hR,hs⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0:E)
  refine ⟨R,hR,fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  simp only [Metric.mem_ball,dist_zero_right] at hh
  exact (not_lt_of_ge hx) hh

end HigherDimensionalBallPacking.Rigidity



open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_LocalCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]



attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.localChartsInst12
local instance localChartsInst16_r41f5f1_1 (α : ℝ) : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) := inferInstance
local instance localChartsInst18_r41f5f1_1 (α : ℝ) : AddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :=
  (inferInstance : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α)).toAddCommGroup
omit [FiniteDimensional ℂ E] in
theorem affineC1_uniform_exterior (J : E → E →L[ℝ] E) (B : E →L[ℝ] E)
    (hc : HasCompactSupport (fun x => J x-B))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖ ≤ ‖p.1.2 z‖) :
    ∃ S : ℝ, 0 < S ∧ ∀ q : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3),
      ‖q-p‖ < min 1 (m/2) → ∀ z : ℂ, S < ‖z‖ →
        J (c1HolderAffineCurve ((1:ℝ)/3) q.1.1 q.1.2 q.2 z)=B := by
  obtain ⟨T,hT,hJT⟩ := compactCoefficient_zero_outside hc
  let U := ‖p.2‖+1
  let S := max 1 (2*(T+‖p.1.1‖+1+U)/m)
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨S,hS,?_⟩
  intro q hq z hz
  have hqp₁ : ‖q.1-p.1‖ < min 1 (m/2) := lt_of_le_of_lt (norm_fst_le (q-p)) hq
  have hd : ‖q.1.1-p.1.1‖ ≤ 1 :=
    ((norm_fst_le (q.1-p.1)).trans hqp₁.le).trans (min_le_left _ _)
  have hB : ‖q.1.2-p.1.2‖ ≤ m/2 :=
    ((norm_snd_le (q.1-p.1)).trans hqp₁.le).trans (min_le_right _ _)
  have hq₂ : ‖q.2-p.2‖ ≤ 1 :=
    ((norm_snd_le (q-p)).trans hq.le).trans (min_le_left _ _)
  have hqU : ‖q.2‖ ≤ U := by
    have hh : ‖q.2‖ ≤ ‖q.2-p.2‖+‖p.2‖ := norm_le_norm_sub_add _ _
    change ‖q.2‖ ≤ ‖p.2‖+1
    linarith only [hh,hq₂]
  have hv := (c1HolderValue_bound ((1:ℝ)/3) q.2 z).trans hqU
  have hzS : T+‖p.1.1‖+1+U  ≤  m/2*‖z‖ := by
    have hh := (le_max_right 1 (2*(T+‖p.1.1‖+1+U)/m)).trans hz.le
    have hh' := (div_le_iff₀ hm).mp hh
    linarith
  have he := affineProfile_lower_bound p.1.1 (q.1.1-p.1.1)
    (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) q.2) z)
    p.1.2 (q.1.2-p.1.2) m U T 1 hm hA hd hB hv ⟨zero_le_one,le_rfl⟩ z hzS
  have he' : T ≤ ‖c1HolderAffineCurve ((1:ℝ)/3) q.1.1 q.1.2 q.2 z‖ := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rw [one_smul,sub_apply]
    congr 1
    unfold c1HolderAffineCurve
    abel
  exact sub_eq_zero.mp (hJT _ he')

end HigherDimensionalBallPacking.Rigidity

 

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem orbitCoefficient_value {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v (z+h)) := by
  change f (c+h • a+z • a+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) (z+h))=_
  congr 1
  unfold c1HolderAffineCurve
  rw [affineSlope_apply,add_smul]
  abel

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHGroup
local instance orbitCGroup_r41f5f1_1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
theorem affineCoefficient_exterior {n : ℕ} (f : Phase n → End n) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) :
    ∃ R : ℝ, 0<R ∧ ∀ z : ℂ, R<‖z‖ → f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)=0 := by
  have hc' : HasCompactSupport (fun x => f x-(0:End n)) := by simpa only [sub_zero] using hc
  obtain ⟨R,hR,hh⟩ := affineC1_uniform_exterior f 0 hc' ((c,affineSlope a),v) ‖a‖ (norm_pos_iff.mpr ha) (by
    intro z
    rw [affineSlope_apply,norm_smul,mul_comm])
  refine ⟨R,hR,?_⟩
  exact hh ((c,affineSlope a),v) (by simp only [sub_self,norm_zero]; exact lt_min zero_lt_one (half_pos (norm_pos_iff.mpr ha)))

 theorem orbitCoefficient_support_oai {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) :
    ∃ b : ContDiffBump (0:ℂ), ∀ h : ℂ, ‖h‖<1 → ∀ z : ℂ, b.rIn<‖z‖ →
      holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=0 := by
  obtain ⟨R,hR,hs⟩ := affineCoefficient_exterior f hc c a ha v
  let b : ContDiffBump (0:ℂ) := ⟨R+1,R+2,by linarith,by linarith⟩
  refine ⟨b,?_⟩
  intro h hh z hz
  rw [orbitCoefficient_value]
  apply hs
  have hn : ‖z‖≤‖z+h‖+‖h‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z+h) h
  change R+1<‖z‖ at hz
  linarith

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support_oai := @OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient_support_oai
