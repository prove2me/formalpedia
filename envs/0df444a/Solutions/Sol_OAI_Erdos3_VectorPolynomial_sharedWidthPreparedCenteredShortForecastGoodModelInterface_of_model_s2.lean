-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:14:44.123276+00:00
-- url     : https://prove2.me/submissions/46cdd79f-2f85-48fa-9f26-94d0add449f0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B290
import Definitions.Def_OAIE3v2B291

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

theorem sharedWidthPreparedCenteredForecastModelExtension_of_model
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired : ℝ)
    (hModel : SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hExtra : SharedWidthPreparedCenteredForecastModelExtraDataInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (Good := Good)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired) :
    SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z
  have hsizeModel (i) : Real.exp modelRequired ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize i)
  have hRankModel : Real.exp modelRequired ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRank
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hnormalizerCenter, hweight, hrest⟩ :=
    hModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
      hξn hξle hξLate cells poly hpoly hmem hsizeModel hrank hRankModel hCells
  have hgood := hExtra hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
    hξn hξle hξLate cells poly hpoly hmem hsize hrank hRank hCells
    hN hbases hbox hmass hnormalizer hmargin hnormalizerCenter
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  exact ⟨hweight, hgood, hrest⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

theorem sharedWidthPreparedCenteredShortForecastGoodExtraData
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : SharedWidthPreparedCenteredShortForecastGoodBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D) :
    SharedWidthPreparedCenteredForecastModelExtraDataInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o)
      (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
        stride gainLog gain Qgood spatialEmbedding)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      (preparedCenteredShortForecastGoodRequired m B0 Pgood) := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff Eforecast hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z hN hbases hbox hmass hnormalizer hmargin
    Path Zcenter hnormalizerCenter centeredLaw
  have hsizeGood (i) : Real.exp (preparedCenteredShortForecastGoodRequired m B0 Pgood) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize i)
  have hRankGood : Real.exp (preparedCenteredShortForecastGoodRequired m B0 Pgood) ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRank
  exact (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose_spec.2.2.2 (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) prep U b S B0 Vlog gainLog gain Qgood H.hcert
    bW hb o Cforward Vtail hforward hVactual hR hσ H.hσ1 C hC hchart
    (H.hsmall C hC hCbound)
    (Pchart := Pchart) (Pmaster := Pmaster) (Plate := Plate) (D := D)
    (Pwidth := Pwidth) (P₀ := P₀) (P := Pgood)
    hprofile hForward hVtail H.hchartB H.hMaster H.hLate H.hd H.hD H.hnMaster H.hRi H.hσi H.hS
    H.hprojection H.hphysical H.hVlog H.hQexp H.hP₀ H.hnP₀ H.hgP₀ H.hcutoffP H.hBP H.hwidthP H.hg H.hgP H.hgain
    μ ν poly hpoly hmem stride hstride
    (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr H.hstrideWidth))
    hτSpatial (hτInv.trans (Real.exp_le_exp.mpr H.hτWidth)) hξn hξone (hξLate.trans (Real.exp_le_exp.mpr H.hξWidth))
    N hN hsizeGood hrank hRankGood cells hCells bases hbases hmass
    hnormalizerCenter H.hnX spatialEmbedding

theorem sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2_oai
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : SharedWidthPreparedCenteredShortForecastGoodBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D)
    (hModel : SharedWidthPreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    SharedWidthPreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding := by
  apply sharedWidthPreparedCenteredForecastModelExtension_of_model
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
      stride gainLog gain Qgood spatialEmbedding)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (preparedCenteredShortForecastGoodRequired m B0 Pgood) hModel
  exact sharedWidthPreparedCenteredShortForecastGoodExtraData (m := m) (nX := nX) (M := M)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood spatialEmbedding
    H

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2_oai := @OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2_oai
