-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:31:24.440671+00:00
-- url     : https://prove2.me/submissions/6ab98abc-2be9-42ff-a55a-9f60017ead2c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeDirectSource_of_geometry_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section General

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
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
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (sourceU pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν bW μ in

theorem preparedFiniteScheduleGeometryDirectSource_s2_oai
    (Cdetect : ℕ) (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G) :
    PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  let : CompactSpace (CoefficientTorus (K := Fin (s + 1)) U) :=
    coefficientTorus_compact_of_lattice U
  let : MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Fin (s + 1)) U) := ⟨rfl⟩
  let : MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U) := borel _
  let : BorelSpace (SiteTorus (Finset (Fin (s + 1))) U) := ⟨rfl⟩
  intro α hαlower hαone
  rw [hCdetect] at scalar geometryAt
  exact preparedUniformDegreeDirectSource_of_geometry_s2
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
    (μrows := probabilityAddHaar (CoefficientTorus (K := Fin (s + 1)) U))
    hsm Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate hBa hBi hcapacity hαlower hαone

end General

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource_s2_oai
