-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:25:06.187697+00:00
-- url     : https://prove2.me/submissions/08b86812-6da4-4bb2-a47e-ce763ebca49c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B272
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedSourceSlicedForecastNumerics_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_relativePatchSliceConclusion_of_normalized_ready_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem forecastJointGridMeshLog_nonneg (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ forecastJointGridMeshLog d P E := by
  unfold forecastJointGridMeshLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem fixedPathSlicedGridMeshFloor_le_exp {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hV : 0 ≤ V) (hc : 0 ≤ cost) (hE : 0 ≤ E) :
    (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤
      Real.exp (fixedPathSlicedGridMeshLog D C V cost E + 1) := by
  have hlog : 0 ≤ fixedPathSlicedGridMeshLog D C V cost E := by
    unfold fixedPathSlicedGridMeshLog
    have := Real.log_nonneg (show (1 : ℝ) ≤ D + C + 8 by linarith)
    linarith
  calc
    _ ≤ Real.exp (fixedPathSlicedGridMeshLog D C V cost E) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := add_comm _ _
    _ ≤ _ := by
      rw [Real.exp_add]
      have hbase := Real.one_le_exp hlog
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith

theorem fixedPathSlicedGridMeshLog_le {D C P V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P) :
    fixedPathSlicedGridMeshLog D C V cost E ≤ D + P + V + cost + E + 11 := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hbase : D + 8 ≤ Real.exp (D + P + 8) := by
    linarith [Real.add_one_le_exp (D + P + 8)]
  have hcb : C ≤ Real.exp (D + P + 8) :=
    hCP.trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : D + C + 8 ≤ Real.exp (D + P + 9) := by
    calc
      _ ≤ 2 * Real.exp (D + P + 8) := by linarith
      _ ≤ Real.exp 1 * Real.exp (D + P + 8) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hl : Real.log (D + C + 8) ≤ D + P + 9 := by
    exact (Real.log_le_iff_le_exp hp).mpr hsum
  unfold fixedPathSlicedGridMeshLog
  linarith

theorem fixedPathSlicedGridMeshFloor_le_exp_of_prefactor {D C P V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P)
    (hV : 0 ≤ V) (hc : 0 ≤ cost) (hE : 0 ≤ E) :
    (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤
      Real.exp (D + P + V + cost + E + 12) := by
  apply (fixedPathSlicedGridMeshFloor_le_exp hD hC hV hc hE).trans
  apply Real.exp_le_exp.mpr
  linarith [fixedPathSlicedGridMeshLog_le (V := V) (cost := cost) (E := E) hD hC hP hCP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3

theorem forecastJointGridSamplerFloor_le_exp (d : ℕ) {P E Q PR : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hQ : 0 ≤ Q) (hPR : 0 ≤ PR) :
    (forecastJointGridSamplerFloor d P E Q PR : ℝ) ≤
      Real.exp (forecastJointGridSamplerLog d P E Q PR + 1) := by
  have hlog : 0 ≤ forecastJointGridSamplerLog d P E Q PR := by
    unfold forecastJointGridSamplerLog
    have hmesh := forecastJointGridMeshLog_nonneg d hP hE
    positivity
  calc
    _ ≤ Real.exp (forecastJointGridSamplerLog d P E Q PR) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (forecastJointGridSamplerLog d P E Q PR) := add_comm _ _
    _ ≤ _ := one_add_le_exp_succ hlog le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))

theorem comparisonPrecisionFloor_le_exp (d : ℕ) {Pu V E : ℝ}
    (hPu : 0 ≤ Pu) (hV : 0 ≤ V) (hcost : 0 ≤ cost) (hE : 0 ≤ E) :
    (comparisonPrecisionFloor s d Pu V E : ℝ) ≤
      Real.exp (allocatedFixedPathSlicedAmbientFloorLog d s.D Pu V cost E
        (comparisonGridLog s Pu) s.PK) := by
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    linarith
  have hF : 0 ≤ 2 * Pu + (E + 4) + 14 := by positivity
  have hsrc := fixedPathSlicedGridMeshFloor_le_exp_of_prefactor s.hD.nonneg
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num) hfour hV hcost hF
  have hgrid := forecastJointGridSamplerFloor_le_exp d
    (hPu.trans (le_max_left _ _) : 0 ≤ comparisonGridLog s Pu)
    (show 0 ≤ E + 4 by linarith) hV s.hPK
  unfold comparisonPrecisionFloor
  rw [Nat.cast_max]
  apply max_le
  · apply hsrc.trans (Real.exp_le_exp.mpr _)
    apply le_trans _ (le_max_left _ _)
    linarith
  · exact hgrid.trans (Real.exp_le_exp.mpr (le_max_right _ _))

end Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastTailCap_stride_le (cost : ℝ) :
    2 * Real.exp cost ≤ preparedSlicedForecastTailCap cost := le_max_right _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloor_bounds
    (periodLog childLog cost comparisonLog : ℝ) :
    let F := preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog
    let Lmin := preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog
    0 ≤ F ∧ 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (F + 1) ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro F Lmin
  have hF : 0 ≤ F := le_max_left _ _
  have hp : periodLog ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hc : childLog ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs : cost + 1 ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have ha : comparisonLog ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hfloor : Real.exp F ≤ (Lmin : ℝ) := Nat.le_ceil _
  have hnat (a : ℝ) (haF : a ≤ F) (k : ℕ) (hk : (k : ℝ) ≤ Real.exp a) :
      k ≤ Lmin := by
    exact_mod_cast hk.trans ((Real.exp_le_exp.mpr haF).trans hfloor)
  refine ⟨hF, one_le_ceil_exp F, ceil_exp_le_exp_add_one hF, ?_, ?_, hnat _ hp, hnat _ ha⟩
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hc)
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)
      _ = Real.exp (cost + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ Real.exp F := Real.exp_le_exp.mpr hs
      _ ≤ Lmin := hfloor

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection_p3 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_comparison_logs {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4)
    (Ptest : ℝ) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.pcap = preparedSlicedForecastPrimitiveCap ∧
      s.slicedComparisonSourceLog Ptest = preparedSlicedForecastSourceLog m M Jalloc Ptest := by
  simp only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog,
    preparedSlicedForecastSourceLog, preparedSlicedForecastPrimitiveCap, pow_two,
    preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection_p3, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth]
  trivial

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection_p2 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_scalar_values {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∧
    s.Pscale = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∧
    s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog ∧
    s.Ppres = cost + 1 ∧
    s.Pκ = preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∧
    s.κ = forecastGeometricJacobian (X := Fin nX) («I» := (PreparedSamplerContinuous L)) U b R S.value
      (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8))) ∧
    s.Pcap = max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1) := by
  simp only [preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection_p2, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth, preparedSlicedForecastJacobianLog]
  trivial

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection_p1 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_scalar_values_extended {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
      s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  simp only [preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection_p1, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth]
  trivial

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteComparisonGridBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_comparison_floor {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4)
    (d : ℕ) (Ptest V E : ℝ) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
        (s.slicedComparisonSourceLog Ptest) =
      preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest ∧
    (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
        (s.slicedComparisonSourceLog Ptest) V E : ℝ) ≤
      Real.exp (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E) ∧
    fixedPathSlicedPerturbationLog s.D (s.D + s.slicedComparisonSourceLog Ptest + 4)
        (cost + 1) (2 * s.slicedComparisonSourceLog Ptest + (E + 4) + 14) m =
      preparedSlicedForecastPerturbationLog m M Jalloc cost Ptest E ∧
    ∀ periodLog childLog : ℝ,
      ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
          (s.slicedComparisonSourceLog Ptest) V E ≤
        preparedSlicedForecastCommonFloor periodLog childLog cost
          (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
            Pdim cost pRadius gainLog Qstride Ptest V E) := by
  intro s
  obtain ⟨hP, hscale, hbad, hpres, hκ, hκeq, hprimitive⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hPK, hPF', hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hpcap, hPu⟩ :=
    preparedActualSlicedForecastSetup_comparison_logs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget Ptest
  change s.P = _ at hP
  change s.Pbad = _ at hbad
  change s.Ppres = _ at hpres
  change s.PK = _ at hPK
  change s.D = _ at hD
  change s.slicedComparisonSourceLog Ptest = _ at hPu
  have hgrid : ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
      (s.slicedComparisonSourceLog Ptest) =
      preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest := by
    simp only [ActualFixedSpatialSlicedForecastPath.comparisonGridLog,
      preparedSlicedForecastGridLog, hPu, hP, hbad, hpres, Fintype.card_fin]
  have hPu0 : 0 ≤ s.slicedComparisonSourceLog Ptest := by
    rw [hPu]
    unfold preparedSlicedForecastSourceLog
    have := preparedSlicedForecastPrimitiveCap_one_le
    positivity
  have hfloor := ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor_le_exp
    s d hPu0 hV hcost hE
  rw [hgrid] at hfloor
  have hbound : (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
      (s.slicedComparisonSourceLog Ptest) V E : ℝ) ≤
      Real.exp (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E) := by
    simpa only [hD, hPu, hPK, preparedSlicedForecastComparisonFloorLog] using hfloor
  refine ⟨hgrid, hbound, ?_, ?_⟩
  · simp only [hD, hPu, preparedSlicedForecastPerturbationLog]
  · intro periodLog childLog
    exact (preparedSlicedForecastCommonFloor_bounds periodLog childLog cost
      (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E)).2.2.2.2.2.2 _ hbound

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSourceSlicedForecastNumerics
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

theorem preparedActualSlicedForecastSetupOfSourceGeometry_comparison_data {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (d : ℕ) (Ptest V E : ℝ) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    s.pcap = preparedSlicedForecastPrimitiveCap ∧
    s.slicedComparisonSourceLog Ptest = preparedSlicedForecastSourceLog m M Jalloc Ptest ∧
    ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
        (s.slicedComparisonSourceLog Ptest) =
      preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest ∧
    (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
        (s.slicedComparisonSourceLog Ptest) V E : ℝ) ≤
      Real.exp (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E) ∧
    fixedPathSlicedPerturbationLog s.D (s.D + s.slicedComparisonSourceLog Ptest + 4)
        (cost + 1) (2 * s.slicedComparisonSourceLog Ptest + (E + 4) + 14) m =
      preparedSlicedForecastPerturbationLog m M Jalloc cost Ptest E ∧
    ∀ periodLog childLog : ℝ,
      ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
          (s.slicedComparisonSourceLog Ptest) V E ≤
        preparedSlicedForecastCommonFloor periodLog childLog cost
          (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
            Pdim cost pRadius gainLog Qstride Ptest V E) := by
  let geometry := Classical.choice hgeometry.1
  have hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ geometry.T j := by
    intro j
    have h := geometry.hsource j
    norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
    exact h
  have hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) *
          (2 * (geometry.siteRadius : ℝ) * R j))) ≤ 1 / 4 := by
    intro j
    simpa only [mul_assoc] using
      (geometry.hbudgets inverse hinverse hInverseBound).2.2 j
  obtain ⟨hpcap, hsource⟩ :=
    preparedActualSlicedForecastSetup_comparison_logs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget Ptest
  have hcomparison :=
    preparedActualSlicedForecastSetup_comparison_floor (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget d Ptest V E hV hE
  exact ⟨hpcap, hsource, hcomparison⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

theorem preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
 :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∧
    s.Pscale = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∧
    s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog ∧
    s.Ppres = cost + 1 ∧
    s.Pκ = preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∧
    s.κ = forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous L) U b R S.value
      (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8))) ∧
    s.Pcap = preparedSlicedForecastPrimitiveCap ∧
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
    s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  let geometry := Classical.choice hgeometry.1
  have hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ geometry.T j := by
    intro j
    have h := geometry.hsource j
    norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
    exact h
  have hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) *
          (2 * (geometry.siteRadius : ℝ) * R j))) ≤ 1 / 4 := by
    intro j
    simpa only [mul_assoc] using
      (geometry.hbudgets inverse hinverse hInverseBound).2.2 j
  obtain ⟨hP, hscale, hbad, hpres, hκ, hJac, hcap⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hK, hF, hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget
  exact ⟨hP, hscale, hbad, hpres, hκ, hJac, hcap, hτ, hK, hF, hD⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedSourceGeometryNormalizedPatchConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m M nX Jalloc : ℕ} {J₀ : Type}
variable (prep : RankPreparationFamily (Fin nX) J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ (EnlargedPreparedCommonKernel m Jalloc)}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ (EnlargedPreparedCommonSamplerBlock prep Jalloc) ⟨j,a.val⟩}
variable (eSpatial : Fin 2 × (Fin nX) ↪ (EnlargedPreparedCommonKernel m Jalloc))
variable {gainLog : ℝ}
variable {N : (Fin nX) → ℕ} {ξ cost : ℝ}
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : (Fin nX) → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc))) (Fin nX) stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  (Real.exp (-(gainLog + (nX : ℝ) + 8))) ξ stride cells center}

local instance instNonemptySiteEnlargedPreparedCommonKernelFinPreparedSamplerContinuousEnlargedPreparedCommonSamplerBlockCoord_rbe9aba_1 : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : ((Fin nX) → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {pRadius Qstride PF Pchart childLog Pdim : ℝ}

include ν hpPrep hRprep hchild hgain hReady hregularityBudget
  hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule in

theorem relativePatchSliceConclusion_of_prepared_source_geometry_s2_oai

    (hmPositive : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace ((prep j).space)) (b j) ≤ Real.exp Pchart)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (prep j)), ‖normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace ((prep j).space) × (Fin (preparedSamplerTransverse prep j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace ((prep j).space)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (hchildLog : 0 ≤ childLog)

    (centerLift : ∀ j, (prep j).space)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => (preparedSlicedForecastChildSize childLog) ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin (Real.exp (-(gainLog + (nX : ℝ) + 8))) N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ p)
    (hPrecision : actualForecastDataModelRequired localBudget (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)))) C (Real.exp (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog))))
    (hexcess : letI : DecidableEq (Fin nX) := Classical.decEq _
      letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3))
        (2 * u + 4 * p + max 0 (preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (2 * u + 4 * p + 12)) + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ((allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) + (preparedSlicedForecastSourceLog m M Jalloc Ptest) + 4) (cost + 1)
      (2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14) m))
    (hlarge : ∀ i, Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost) (2 * max Ptest (3 * (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)) + 3) + 1))
      ((preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
    (readFn : ((Fin nX) → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) × (Fin nX) → ℤ) →
      AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m Jalloc) (Fin nX) (PreparedSamplerContinuous prep) Eout (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc) → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      (EnlargedPreparedCommonSamplerBlock prep Jalloc) (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m (nX + m * M) : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card (Fin nX)) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : (Fin nX) => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card (Fin nX) : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card (Fin nX)) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hE : 0 ≤ Ecompare)
    (hSourceFloor : preparedSlicedForecastCommonFloor 0
      childLog cost (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j)) Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * (preparedSlicedForecastSourceLog m M Jalloc Ptest) + (Ecompare + 4) + 14)))
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, (PreparedSamplerContinuous prep) j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + nX + 8)) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : (preparedSlicedForecastBadLog m nX Qstride gainLog) ∈ Set.Icc 0 crtBudget)
    (hCRTpres : (cost + 1) ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : ((nX + m * M) : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : (preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog) ≤ budget) (hPnative : (preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog (2 * u + 4 * p + 12)) ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (originalRank + degree * (D + E))
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
  obtain ⟨qnum, hqδ, hqH, hqv, hqTail, hqE, hqPN, hqMass, hqCap, hqCtail,
      hqT, hqMass0, hqCap0, hqPN0⟩ :=
    exists_preparedSourceSlicedForecastNumerics_s2 (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      childLog (2 * u + 4 * p + 12) hchildLog (by linarith)
  obtain ⟨qLate, hlδ, hlH, hlv, hlTail, hlE, hlPN, hlMass, hlCap, hlCtail,
      hlT, hlMass0, hlCap0, hlPN0⟩ :=
    exists_preparedSourceSlicedForecastNumerics_s2 (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      childLog (Ecompare + 8) hchildLog (by linarith)
  obtain ⟨hsP, hsScale, hsBad, hsPres, hsPκ, hsκ, hsCap, hsPτ, hsPK, hsPF, hsD⟩ :=
    preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
  obtain ⟨hsPcap, hsPu, hsGrid, hsFloor, hsPerturb, hsCommon⟩ :=
    preparedActualSlicedForecastSetupOfSourceGeometry_comparison_data (nX := nX) prep Jalloc (fun j : Fin m => (prep j).space) b o S bW hb
    hmPositive hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound inverse hinverse hchart hInverseBound hgeometry
      ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
      Ptest (2 * Ptest) Ecompare (mul_nonneg (by norm_num) hCRTtest.1) hE
  change s.pcap = preparedSlicedForecastPrimitiveCap at hsPcap
  change s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost at hsP
  change s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog at hsBad
  change s.Ppres = cost + 1 at hsPres
  change s.Pτ = gainLog + nX + 8 at hsPτ
  change s.D = allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) at hsD
  change s.κ = forecastGeometricJacobian (X := Fin nX)
    (I := PreparedSamplerContinuous prep) (fun j : Fin m => (prep j).space) b R S.value
    (preparedForecastGridVolume prep Jalloc (fun j : Fin m => (prep j).space) b S)
    (Real.exp (-(gainLog + (nX : ℝ) + 8))) at hsκ
  change s.slicedComparisonSourceLog Ptest =
    preparedSlicedForecastSourceLog m M Jalloc Ptest at hsPu
  change ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
    (s.slicedComparisonSourceLog Ptest) =
    preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest at hsGrid
  let periodLog : ℝ := 0
  let comparisonLog := preparedSlicedForecastComparisonFloorLog m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare
  have hSourceFloor' : preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ S.value :=
    hSourceFloor
  have hfloorBounds := preparedSlicedForecastCommonFloor_bounds periodLog childLog cost comparisonLog
  have hcutoff : qnum.Hchild ≤ S.value := by
    rw [hqH]
    exact hfloorBounds.2.2.2.1.trans hSourceFloor'
  have h2S : 2 * Real.exp cost ≤ (S.value : ℝ) :=
    hfloorBounds.2.2.2.2.1.trans (Nat.cast_le.mpr hSourceFloor')
  have hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2S (Real.exp_nonneg (-cost))
    have heq : Real.exp (-cost) * (2 * Real.exp cost) = 2 := by
      rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact heq ▸ h
  have hdet' := hdet
  have hdecX : instDecidableEqFin nX =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdecX] at hdet'
  have hdirect' := @hdirect
  rw [hdecX] at hdirect'
  exact relativePatchSliceConclusion_of_normalized_ready_s2
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (eSpatial := eSpatial) (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (f := f) (lam := lam) (hchild := hchild) (hgain := hgain) (hReady := hReady)
    (hregularityBudget := hregularityBudget) (hpGlobal := hpGlobal)
    (hchartGlobal := hchartGlobal) (hscoreGlobal := hscoreGlobal) (hmassGlobal := hmassGlobal)
    (hfGlobal := hfGlobal) (hlam := hlam) (rule := rule)
    (hkernel := ⟨enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m) 0⟩)
    (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := by rw [hqδ]; exact le_rfl)
    (hlog := hqv.symm.le) (hprescribed := hsPres.symm.le)
    (hstride := by rw [hqTail]; exact preparedSlicedForecastTailCap_stride_le cost)
    centerLift (preparedSlicedForecastChildSize childLog) hqH.symm hinit
    (hqδ.trans hlδ.symm) (hqH.trans hlH.symm) (hqv.trans hlv.symm) (hqTail.trans hlTail.symm)
    hξone hmargin hu hp hbudget hSliceLog hC hCp
    (by simpa only [hqCap] using hCap) hqE.symm.le
    (by simpa only [hqPN, hqMass] using hPrecision)
    (by rw [hqCap]; exact @hdirect') hexcess hSlice hcostSlice hchartCost htest hσone e
    hU (by simpa only [hqPN, hqMass] using hEcompare)
    (by simpa only [hqPN] using hcommonTest)
    (by simpa only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap,
      preparedSlicedForecastSourceLog, pow_two] using hσbound)
    (by
      apply hsκ.trans
      unfold preparedForecastGridVolume preparedActualForecastGridVolume
      congr 1)
    (by linarith [hlMass0])
    (by simpa only [hsP, hlPN, hlMass] using hlarge)
    (by simpa only [hsP, hlPN, hlMass] using hRrank) hrank
    sampleFn readFn hglobal hrecovered hgood hdet'
    hPdim hX hvars hnX hGain hgainDim hstrideSource
    (by rw [hsP]; exact (le_max_left _ _).trans (le_max_right _ _))
    (by simp only [hsBad, preparedSlicedForecastBadLog, Fintype.card_fin]; exact le_rfl)
    hcost hE (Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α := ℝ) nX; linarith))
    ((hsCommon periodLog childLog).trans hSourceFloor')
    (by simpa only [ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap,
      preparedSlicedForecastSourceLog, pow_two] using hξsmall) hlE.symm.le
    (by simpa only [ActualFixedSpatialSlicedForecastPath.comparisonGridLog,
      ActualFixedSpatialForecastSetup.slicedComparisonSourceLog, hsD, hsPcap, hsP, hsBad, hsPres,
      hsPτ, preparedSlicedForecastSourceLog, preparedSlicedForecastGridLog, Fintype.card_fin, pow_two] using hNgrid) hcoord hbW
    hεpos hεone hCRTbudget hCRTinv hCRTtest
    (by simpa only [hsBad] using hCRTbad) (by simpa only [hsPres] using hCRTpres)
    hm hprepared hFinalBudget hRankBudget
    (by simpa only [Nat.cast_add, Nat.cast_mul] using hDmodBudget) hMatrixBudget hPatchCostBudget
    (by simpa only [hqCap] using hcapLog) (by simpa only [hqPN] using hPnative)
    hScoreBudget hFinalLarge

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry_s2_oai := @OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_prepared_source_geometry_s2_oai
