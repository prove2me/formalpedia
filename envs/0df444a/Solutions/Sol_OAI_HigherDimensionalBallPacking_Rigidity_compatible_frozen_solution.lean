-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.compatible_frozen_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:21:40.298664+00:00
-- url     : https://prove2.me/submissions/c1110e14-e85c-49ba-8075-310b09b20eca

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_framed_frozen_solution
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_principalFrameLower_equation
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_principalFrameLower_support

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

end Rigidity
end
end HigherDimensionalBallPacking

end OAI
end

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


 theorem CompatibleWith.form_left {η : E →L[ℝ] E →L[ℝ] ℝ} {J : E →L[ℝ] E}
    (hJ : CompatibleWith η J) (u v : E) : η (J u) v = -η u (J v) := by
  have h := hJ.2.1 u (J v)
  rw [hJ.1 v, map_neg] at h
  linarith


 theorem relativeTransition_apply_B {η : E →L[ℝ] E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (hB : CompatibleWith η B) (t : ℝ) (J : E →L[ℝ] E) (v : E) :
    relativeTransition t B J (B v) = B v + t • J v := by
  simp [hB.1, sub_eq_add_neg]

 theorem relativeTransition_positive_identity {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    (t : ℝ) (v : E) :
    η (relativeTransition t B J v) (relativeTransition t B J (B v)) =
      (1+t^2) * η v (B v) + t * η v (J v) + t * η (B v) (J (B v)) := by
  rw [relativeTransition_apply_B hB, relativeTransition_apply]
  simp only [map_add, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, hJ.2.1, hJ.form_left]
  rw [hB.form_left v v]
  ring

 theorem relativeTransition_positive {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    {t : ℝ} (ht : 0 ≤ t) {v : E} (hv : v ≠ 0) :
    0 < η (relativeTransition t B J v) (relativeTransition t B J (B v)) := by
  rw [relativeTransition_positive_identity hB hJ]
  have hBv : B v ≠ 0 := by
    intro hh
    have h := congrArg B hh
    exact hv (by simpa only [hB.1, map_zero, neg_eq_zero] using h)
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos (by positivity) (hB.2.2 v hv))
      (mul_nonneg ht (hJ.2.2 v hv).le)) (mul_nonneg ht (hJ.2.2 _ hBv).le)

 theorem relativeTransition_isInvertible [FiniteDimensional ℝ E] {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    {t : ℝ} (ht : 0 ≤ t) : (relativeTransition t B J).IsInvertible := by
  have hz (v : E) (hv : relativeTransition t B J v = 0) : v = 0 := by
    by_contra h
    have hp := relativeTransition_positive hB hJ ht h
    simp only [hv, map_zero, zero_apply, lt_self_iff_false] at hp
  have hinj : Injective (relativeTransition t B J) := by
    intro u v huv
    exact sub_eq_zero.mp (hz (u-v) (by rw [map_sub, huv, sub_self]))
  exact ⟨(LinearEquiv.ofBijective (relativeTransition t B J).toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩


end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_EqualDimension
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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem Compatible.compatibleWith_stdOmega {n : ℕ} {J : End n} (hJ : Compatible J) :
    HigherDimensionalBallPacking.Rigidity.CompatibleWith (stdOmega n) J := by
  simpa only [HigherDimensionalBallPacking.Rigidity.CompatibleWith,stdOmega_apply,Compatible] using hJ



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
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
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem normalizedHolderFrame_value {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z=
      (1/2:ℝ) • relativeTransition 1 (standardJ n) (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z) := by
  change (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)-
    (1/2:ℝ) • (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z).comp (standardJ n)=_
  simp only [relativeTransition,one_smul,smul_sub]

 theorem normalizedFrame_intertwines {n : ℕ} {K : End n} (hK : Compatible K) (x : Phase n) :
    ((1/2:ℝ) • relativeTransition 1 (standardJ n) K) (Complex.I • x)=
      K (((1/2:ℝ) • relativeTransition 1 (standardJ n) K) x) := by
  simp only [smul_apply,relativeTransition_apply,one_smul]
  change (1/2:ℝ) • (standardJ n x-K (standardJ n (standardJ n x)))=
    K ((1/2:ℝ) • (x-K (standardJ n x)))
  rw [standardJ_sq,map_neg,map_smul,map_sub,hK.1]
  module

 theorem normalizedFrame_invertible {n : ℕ} {K : End n} (hK : Compatible K) :
    ((1/2:ℝ) • relativeTransition 1 (standardJ n) K).IsInvertible := by
  have ht := relativeTransition_isInvertible (compatible_standardJ n).compatibleWith_stdOmega
    hK.compatibleWith_stdOmega (t := 1) (by norm_num)
  let A : End n := (1/2:ℝ) • relativeTransition 1 (standardJ n) K
  have hi : Injective A := by
    intro x y hxy
    apply ht.injective
    exact (smul_right_injective (Phase n) (by norm_num : (1/2:ℝ)≠0)) hxy
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hi,LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv,rfl⟩

 theorem normalizedFrame_standard {n : ℕ} :
    (1/2:ℝ) • relativeTransition 1 (standardJ n) (standardJ n)=ContinuousLinearMap.id ℝ (Phase n) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,relativeTransition_apply,one_smul,ContinuousLinearMap.id_apply]
  change (1/2:ℝ) • (x-standardJ n (standardJ n x))=x
  rw [standardJ_sq]
  module

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem normalizedHolderFrame_intertwines {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) (z : ℂ) (x : Phase n) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z (Complex.I • x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z
        (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z x) := by
  rw [normalizedHolderFrame_value]
  exact normalizedFrame_intertwines (hK z) x

 theorem compatible_frozen_solution_oai {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z))
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n)
    (f : CompactHolderSpace (Phase n) R) :
    ∃ U : C1HolderSpace (Phase n) ((1:ℝ)/3),
      let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
      (∀ z, fderiv ℝ u z Complex.I-
        holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z (fderiv ℝ u z 1)=compactHolderValue R f z) ∧
        Tendsto u (cocompact ℂ) (𝓝 0) := by
  let A := normalizedHolderFrame K
  have hAout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n) := by
    intro z hz
    rw [normalizedHolderFrame_value,hout z hz,normalizedFrame_standard]
  have hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible := by
    intro z
    rw [normalizedHolderFrame_value]
    exact normalizedFrame_invertible (hK z)
  let M := principalFrameLower R (c1HolderValue ((1:ℝ)/3) K) A hi hAout
  exact framed_frozen_solution R _ hK hout A M
    (principalFrameLower_support R _ A hi hAout) hAout hi
    (normalizedHolderFrame_intertwines K hK)
    (principalFrameLower_equation R _ A hi hAout) f

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.compatible_frozen_solution_oai := @OAI.HigherDimensionalBallPacking.Rigidity.compatible_frozen_solution_oai
