-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:16:39.150424+00:00
-- url     : https://prove2.me/submissions/e4ff765d-f246-454d-ac0e-7681619b07a1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B077
import Definitions.Def_OAIErdos3B1348

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem and_rec_projection_p2 {p q : Prop} {α : Sort*}
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

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal



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

theorem and_rec_projection_p1 {p q : Prop} {α : Sort*}
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

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal



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



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal



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

theorem preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values_oai {M nX : ℕ}
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

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values_oai := @OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values_oai
