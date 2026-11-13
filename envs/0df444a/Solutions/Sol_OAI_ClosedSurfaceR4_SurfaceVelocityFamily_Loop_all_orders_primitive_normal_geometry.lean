-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:50:13.968344+00:00
-- url     : https://prove2.me/submissions/ea94c45b-a554-4950-9856-1d6bfd2c3c50

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_normal_triple

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalNonvanishing
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old second derivative has a nonzero normal component after changing velocity. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma gram_ne_zero_of_projection {X Y : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPX : P X ≠ 0) (hY : Y ≠ 0) :
    gramDet X Y ≠ 0 := by
  have hYY : Y ⬝ᵥ Y ≠ 0 := (dotProduct_self_eq_zero).not.mpr hY
  intro hD
  let W := (Y ⬝ᵥ Y) • X - (X ⬝ᵥ Y) • Y
  have hW : W ⬝ᵥ W = (Y ⬝ᵥ Y) * gramDet X Y := by
    simp only [W, gramDet, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hW0 : W = 0 := dotProduct_self_eq_zero.mp (by rw [hW, hD, mul_zero])
  have hpW : (Y ⬝ᵥ Y) • P X = 0 := by
    have he := congrArg P hW0
    simpa only [W, hP.map_sub, hP.map_smul, hPY, smul_zero, sub_zero, hP.map_zero] using he
  exact hPX ((smul_eq_zero.mp hpW).resolve_left hYY)

lemma normalPart_ne_zero_of_projection {X Y C : Vec} {P : Vec → Vec}
    (hP : IsLinearMap ℝ P) (hPY : P Y = 0) (hPC : P C = 0) (hPX : P X ≠ 0)
    (hD : gramDet Y C ≠ 0) : realNormalPart X Y C ≠ 0 := by
  intro hz
  let c := ((Y ⬝ᵥ Y) * (X ⬝ᵥ C) - (X ⬝ᵥ Y) * (Y ⬝ᵥ C)) / gramDet X Y
  let d := ((X ⬝ᵥ X) * (Y ⬝ᵥ C) - (X ⬝ᵥ Y) * (X ⬝ᵥ C)) / gramDet X Y
  have hspan : C = c • X + d • Y := by
    apply sub_eq_zero.mp
    calc
      C - (c • X + d • Y) = C - c • X - d • Y := by abel
      _ = 0 := hz
  have hc : c = 0 := by
    have he := congrArg P hspan
    have he' : c • P X = 0 := by
      simpa only [hPC, hP.map_add, hP.map_smul, hPY, smul_zero, add_zero] using he.symm
    exact (smul_eq_zero.mp he').resolve_right hPX
  have hC : C = d • Y := by simpa only [hc, zero_smul, zero_add] using hspan
  apply hD
  rw [hC]
  simp only [gramDet, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma leadingTangent_projection {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) :
    realNormalPart Y C (leadingTangent X Y C V) = V := by
  have hP := realNormalPart_linear Y C
  have hpX := realNormalPart_perp Y C X hD
  change realNormalPart Y C (X - realNormalPart Y C X + V) = V
  rw [hP.map_add, hP.map_sub,
    realNormalPart_of_perp Y C (realNormalPart Y C X) hpX.1 hpX.2,
    realNormalPart_of_perp Y C V hYV hCV, sub_self, zero_add]

/-- Neither the leading tangent pair nor the normal component of `C` degenerates. -/
theorem leading_normal_nondegenerate {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) (hV : V ≠ 0) :
    gramDet (leadingTangent X Y C V) Y ≠ 0 ∧
      realNormalPart (leadingTangent X Y C V) Y C ≠ 0 := by
  have hP := realNormalPart_linear Y C
  have hPY := realNormalPart_self_left Y C hD
  have hPC := realNormalPart_self_right Y C hD
  have hPX : realNormalPart Y C (leadingTangent X Y C V) ≠ 0 := by
    rwa [leadingTangent_projection hD hYV hCV]
  have hY : Y ≠ 0 := by
    intro hz
    apply hD
    simp [gramDet, hz]
  exact ⟨gram_ne_zero_of_projection hP hPY hPX hY,
    normalPart_ne_zero_of_projection hP hPY hPC hPX hD⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactNormalTriple
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normal nondegeneracy from the three bounded derivatives of a
primitive ansatz. No bound on its rapidly oscillating xx derivative is used. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

lemma contDiffAt_tripleNormal {J : NormalTriple}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ tripleNormal J := by
  have hslot (i : Fin 3) : ContDiffAt ℝ ∞ (fun K : NormalTriple => K i) J :=
    (ContinuousLinearMap.proj i : NormalTriple →L[ℝ] Vec).contDiff.contDiffAt
  exact contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 2) hJ

lemma isOpen_normalTripleNeighborhood (c : ℝ) : IsOpen (normalTripleNeighborhood c) := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : NormalTriple => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_tripleNormal hJ.1).continuousAt.norm.eventually
      (lt_mem_nhds hJ.2))

/-- Compact leading tangent/second-derivative triples have one positive
normal margin and one perturbation radius, independent of the fast phase. -/
theorem compact_normal_triple_stability {K : Set NormalTriple}
    (hK : IsCompact K)
    (hD : ∀ J ∈ K, gramDet (J 0) (J 1) ≠ 0)
    (hN : ∀ J ∈ K, tripleNormal J ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ J ∈ K, ∀ H : NormalTriple,
      ‖H-J‖ < ε → gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖tripleNormal H‖ := by
  rcases K.eq_empty_or_nonempty with hzero | hne
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    simp [hzero]
  have hc : ContinuousOn (fun J => ‖tripleNormal J‖) K :=
    fun J hJ => ((contDiffAt_tripleNormal (hD J hJ)).continuousAt.norm).continuousWithinAt
  obtain ⟨J₀,hJ₀,hmin⟩ := hK.exists_isMinOn hne hc
  let c := ‖tripleNormal J₀‖/2
  have hcpos : 0 < c := half_pos (norm_pos_iff.mpr (hN J₀ hJ₀))
  have hsub : K ⊆ normalTripleNeighborhood c := by
    intro J hJ
    exact ⟨hD J hJ,lt_of_lt_of_le (by have hh := hcpos; dsimp [c] at hh ⊢ <;> linarith) (hmin hJ)⟩
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    (isOpen_normalTripleNeighborhood c) hsub
  refine ⟨ε,c,hε,hcpos,?_⟩
  intro J hJ H hHJ
  apply he
  exact Metric.mem_thickening_iff.mpr ⟨J,hJ,by simpa only [dist_eq_norm] using hHJ⟩

/-- Apply the three-derivative stability estimate to the leading velocity
geometry. It controls the actual normal component of the yy derivative. -/
theorem compact_leading_normal_stability {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {X Y C V : E → Vec}
    (hX : ContinuousOn X K) (hY : ContinuousOn Y K)
    (hC : ContinuousOn C K) (hV : ContinuousOn V K)
    (hD : ∀ p ∈ K, gramDet (Y p) (C p) ≠ 0)
    (hYV : ∀ p ∈ K, Y p ⬝ᵥ V p = 0)
    (hCV : ∀ p ∈ K, C p ⬝ᵥ V p = 0)
    (hV0 : ∀ p ∈ K, V p ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ p ∈ K, ∀ H : NormalTriple,
      ‖H-![leadingTangent (X p) (Y p) (C p) (V p),Y p,C p]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  let J : E → NormalTriple := fun p =>
    ![leadingTangent (X p) (Y p) (C p) (V p),Y p,C p]
  have hT : ContinuousOn (fun p => leadingTangent (X p) (Y p) (C p) (V p)) K := by
    intro p hp
    have hn : ContinuousAt (fun q : Vec × Vec × Vec =>
        realNormalPart q.1 q.2.1 q.2.2) (Y p,C p,X p) :=
      (contDiffAt_realNormalPart (E := Vec × Vec × Vec)
        (X := fun q => q.1) (Y := fun q => q.2.1) (W := fun q => q.2.2)
        (p := (Y p,C p,X p)) (by fun_prop) (by fun_prop) (by fun_prop) (hD p hp)).continuousAt
    exact ((hX p hp).sub
      (hn.comp_continuousWithinAt (f := fun q : E => (Y q,C q,X q))
        ((hY p hp).prodMk ((hC p hp).prodMk (hX p hp))))).add (hV p hp)

  have hJ : ContinuousOn J K := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hT
    · exact hY
    · exact hC
  obtain ⟨ε,c,hε,hc,hh⟩ := compact_normal_triple_stability (hK.image_of_continuousOn hJ)
    (by rintro _ ⟨p,hp,rfl⟩; exact (leading_normal_nondegenerate (hD p hp) (hYV p hp) (hCV p hp) (hV0 p hp)).1)
    (by rintro _ ⟨p,hp,rfl⟩; exact (leading_normal_nondegenerate (hD p hp) (hYV p hp) (hCV p hp) (hV0 p hp)).2)
  exact ⟨ε,c,hε,hc,fun p hp H hH => hh (J p) (mem_image_of_mem J hp) H hH⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicNormalStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normal margins over the compact position-period domain. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes CovarianceCorrector

variable {A : Type} [TopologicalSpace A]

/-- A full real fast phase costs no compactness: periodicity reduces the
normal estimate to one compact period. -/
theorem periodic_leading_normal_stability {K : Set A} (hK : IsCompact K)
    {X Y C : A → Vec} (hX : Continuous X) (hY : Continuous Y) (hC : Continuous C)
    (V : A → C(Period, Vec))
    (hVs : Continuous (fun p : A × ℝ => V p.1 (p.2 : Period)))
    (hD : ∀ p ∈ K, gramDet (Y p) (C p) ≠ 0)
    (hYV : ∀ p ∈ K, ∀ θ : Period, Y p ⬝ᵥ V p θ = 0)
    (hCV : ∀ p ∈ K, ∀ θ : Period, C p ⬝ᵥ V p θ = 0)
    (hV0 : ∀ p ∈ K, ∀ θ : Period, V p θ ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ p ∈ K, ∀ t : ℝ, ∀ H : NormalTriple,
      ‖H-![leadingTangent (X p) (Y p) (C p) (V p (t : Period)),Y p,C p]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  obtain ⟨ε,c,hε,hc,hh⟩ := compact_leading_normal_stability
    (hK.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)))
    (hX.comp continuous_fst).continuousOn (hY.comp continuous_fst).continuousOn
    (hC.comp continuous_fst).continuousOn hVs.continuousOn
    (fun p hp => hD p.1 hp.1) (fun p hp => hYV p.1 hp.1 (p.2 : Period))
    (fun p hp => hCV p.1 hp.1 (p.2 : Period))
    (fun p hp => hV0 p.1 hp.1 (p.2 : Period))
  refine ⟨ε,c,hε,hc,?_⟩
  intro p hp t H hH
  let a : ℝ := AddCircle.equivIco 1 0 (t : Period)
  have ha : a ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 (t : Period)).property
  have he : (a : Period) = (t : Period) := AddCircle.coe_equivIco
  apply hh (p,a) ⟨hp,ha.1,ha.2.le⟩ H
  simpa only [he,Function.comp_apply] using hH

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopCompactNormalMargin
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single positive normal margin for the whole compact set of admissible
low jets, before choosing a slow map or a fast scale. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem compact_normal_margin {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ J ∈ Q, ∀ t : ℝ, ∀ H : VelocityFrame.NormalTriple,
      ‖H-![VelocityFrame.leadingTangent (slot 1 J) (slot 2 J) (slot 6 J)
        (l.velocity (J,t)),slot 2 J,slot 6 J]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let X : Q → NormalFrame.Vec := fun J => slot 1 J
  let Y : Q → NormalFrame.Vec := fun J => slot 2 J
  let C : Q → NormalFrame.Vec := fun J => slot 6 J
  let V : Q → C(Period,NormalFrame.Vec) := fun J =>
    ⟨fun t => spaceCoordinates (l.euclideanVelocity J t),
      spaceCoordinates.continuous.comp (l.euclideanVelocity J).continuous⟩
  have hX : Continuous X := (slot_smooth 1).continuous.comp continuous_subtype_val
  have hY : Continuous Y := (slot_smooth 2).continuous.comp continuous_subtype_val
  have hC : Continuous C := (slot_smooth 6).continuous.comp continuous_subtype_val
  have hV : Continuous (fun p : Q × ℝ => V p.1 (p.2 : Period)) := by
    have hi : Continuous (fun p : Q × ℝ => ((p.1 : LowJet),p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact spaceCoordinates.continuous.comp
      (l.euclideanVelocity_smooth.continuousOn.comp_continuous hi
        (fun p => ⟨hQO p.1.property,mem_univ _⟩))
  have hVeq (J : Q) (t : ℝ) : V J (t : Period) = l.velocity (J,t) := by
    change spaceCoordinates (l.euclideanVelocity J (t : Period)) = _
    rw [l.euclideanVelocity_apply (hQO J.property)]
    exact spaceCoordinates.apply_symm_apply _
  have hYV : ∀ J ∈ (univ : Set Q), ∀ t : Period, Y J ⬝ᵥ V J t = 0 := by
    intro J _ t
    refine Quotient.inductionOn' t ?_
    intro t
    rw [hVeq]
    exact l.perpY J (hQO J.property) t
  have hCV : ∀ J ∈ (univ : Set Q), ∀ t : Period, C J ⬝ᵥ V J t = 0 := by
    intro J _ t
    refine Quotient.inductionOn' t ?_
    intro t
    rw [hVeq]
    exact l.perpC J (hQO J.property) t
  have hV0 : ∀ J ∈ (univ : Set Q), ∀ t : Period, V J t ≠ 0 := by
    intro J _ t ht
    change spaceCoordinates (l.euclideanVelocity J t) = 0 at ht
    have he : l.euclideanVelocity J t = 0 := spaceCoordinates.injective
      (by simpa only [map_zero] using ht)
    have hh := l.euclideanVelocity_length (hQO J.property) t
    rw [he,inner_zero_left] at hh
    exact (ne_of_gt (l.q_pos (hQO J.property))) hh.symm
  obtain ⟨ε,c,hε,hc,hh⟩ := VelocityFrame.periodic_leading_normal_stability
    (isCompact_univ : IsCompact (univ : Set Q)) hX hY hC V hV
    (fun J _ => l.gram_ne J (hQO J.property)) hYV hCV hV0
  refine ⟨ε,c,hε,hc,?_⟩
  intro J hJ t H hH
  apply hh ⟨J,hJ⟩ (mem_univ _) t H
  simpa only [X,Y,C,hVeq] using hH

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformPrimitiveMeanRealization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem all_orders_primitive_normal_geometry_oai {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ n : ℕ, ∃ loss : ℕ,
      ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) → D*z/s^loss < ε →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let H := primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
          U ℓ (n+1) z) p
        gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  obtain ⟨ε,c,hε,hc,hn⟩ := l.compact_normal_margin hQ hQO
  refine ⟨ε,c,hε,hc,?_⟩
  intro n
  obtain ⟨loss,hb⟩ := l.uniform_primitive_normal_triple (S := S) hQ hQO n ℓ hx hy
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hbound hsmall U hU hrep hinit p hp
  exact hn _ (hGQ hp) (ℓ p/z) _
    ((hd G hG hGQ s z hz hzs hs1 hbound U hU hrep hinit p hp).trans_lt hsmall)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry_oai
