-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:50:29.353369+00:00
-- url     : https://prove2.me/submissions/9d24e861-070e-40ae-a6fc-7a7f4aa9fd96

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_TiledProbeChainData_source_first_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProbeIntrinsicTiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic ideal increments of the three actual probe sheets -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {I N : Type} [Group I] [Group N]

/-- The intrinsic inverse flow is precisely conjugation back by the
normalized neighbor step. -/
theorem intrinsic_probe_inverse_flow (ι : I →* N) (φ : MulAut I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹) (i : I) :
    k⁻¹ * ι i * k = ι (φ.symm i) := by
  have h := hφ (φ.symm i)
  rw [φ.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionProbeReparametrization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probe coordinates on the original quotient/kernel cell

The sampling law may be chosen on the original Haar cell and composed with
this homeomorphism. Thus the compact set selected by concentration is already
measured by the probability law required by source packing.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {Z I Q K : Type} [TopologicalSpace Z] [TopologicalSpace I]
  [TopologicalSpace Q] [TopologicalSpace K]

theorem sectionProbeCoordinates_snd
    (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I)
    (y : (eQ '' B) ×ˢ (eI '' U)) :
    eI (sectionProbeCoordinates eQ eI B U y).2.val = y.val.2 :=
  eI.apply_symm_apply _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledSourceEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact linked endpoints on the original source probability cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))


local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The selected prefixes agree with the first probe, tile anchor and
second probe in the original source-cell coordinates. -/
theorem TiledProbeChainData.source_linked_endpoints_m_oai
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (k u : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (S : ℕ → MulAut F.N.carrier)
    (E' : Fin 3 → Set W) (γ : M.Bases) (t' : Fin M.letterCount → ℝ)
    (P : ∀ j, M.BoxProbeChains T F hunimod eW bN (E' j) γ t' scale
      (fun n (y : Y n) => S n (D.probe n j (ψ n y))))
    (origin base : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ)
    (L : M.LinkedProbeChains T F hunimod eW bN E' γ t' scale
      (fun j n (y : Y n) => S n (D.probe n j (ψ n y))) P
      (fun n _ => origin n) (fun n _ => base n) ε)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = u n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = u n * S n (k n))
    (n : ℕ) (y : Y n) :
    F.ExpN (F.N.equiv (L.vertex 0 n y (Fin.last (P 0).length))) =
      u n * S n ((y.val.2 : F.N.carrier) * σ y.val.1) ∧
    F.ExpN (F.N.equiv (L.vertex 1 n y (Fin.last (P 1).length))) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n (ψ n y).2))) (k n) ∧
    F.ExpN (F.N.equiv (L.vertex 2 n y (Fin.last (P 2).length))) =
      coneProbeSecond (S n) (u n) (y.val.2 : F.N.carrier) (k n) := by
  let z := ψ n y
  have hback (i : I) : ι ((φ n).symm i) = (k n)⁻¹ * ι i * k n :=
    (intrinsic_probe_inverse_flow ι (φ n).toMulEquiv (k n) (hφ n) i).symm
  have e₁ : (u n * S n (k n)) * S n (D.probe n 1 z) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n z.2))) (k n) := by
    rw [D.second, hback]
    simp only [coneProbeSecond, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  have e₂ : ((u n * S n (k n)) * S n (D.probe n 1 z)) * S n (D.probe n 2 z) =
      coneProbeSecond (S n) (u n) (ι z.2.val) (k n) := by
    rw [D.second, D.third, hback, hback]
    simp [coneProbeSecond, map_mul, mul_assoc]
  have hfirst := TiledProbeChainData.source_first_m (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    (πQ := πQ) (hι := hι) (hrange := hrange) hchartN n y
  have e₀ := L.first_exp n y (Fin.last (P 0).length)
  have e₁' := L.second_exp n y (Fin.last (P 1).length)
  have e₂' := L.third_exp n y (Fin.last (P 2).length)
  have e₀' := e₀.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    (horigin n) ((P 0).vertex_last n y))
  have h₁ := e₁'.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    (hbase n) ((P 1).vertex_last n y))
  have h₂ := e₂'.trans (congrArg₂ (fun a b : F.N.carrier => a * b)
    h₁ ((P 2).vertex_last n y))
  have hfirst' := e₀'.trans (congrArg (fun z => u n * S n z) hfirst)
  have hanchor := h₁.trans e₁
  have hsecond := h₂.trans e₂
  let eQ := TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ)
  have hi := sectionProbeCoordinates_snd eQ (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1) y
  have hi' : ι (ψ n y).2.val = (y.val.2 : F.N.carrier) := congrArg Subtype.val hi
  exact ⟨hfirst', hanchor, hsecond.trans (congrArg (fun i => coneProbeSecond (S n) (u n) i (k n)) hi')⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints_m_oai
