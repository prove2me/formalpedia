-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:31:51.26322+00:00
-- url     : https://prove2.me/submissions/5a7eb52a-d88f-42bb-ba1d-3ecc4aa0cfba

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B284
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedModularGeneralDetector_late_ambient_bounds_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem coefficientLatticeBasis_card_le {m : ℕ} {J Q : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) ≤ Fintype.card (J j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedProfile_dimensions
    {G : Type*} [Fintype G] (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α O D)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    (∀ j, (Fintype.card (J j) : ℝ) ≤ D) ∧ (∀ j, (Fintype.card (Q j) : ℝ) ≤ D) := by
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans hd.axes
  exact ⟨hJ, fun j => (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitializedEarlyCanonicalSliceScales
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem canonicalTransitionLip_spec :
    LipschitzWith canonicalTransitionLip Real.smoothTransition :=
  (Classical.choose_spec exists_smoothTransition_lipschitz).2

attribute [local instance 2000] fullBooleanRowSetFintype

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularGeneralDetector_block_card (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  let f : B a → LayerSamplerVariables G I n B := fun x =>
    Sum.inr ⟨a, x, ⟨0, by simp [layerSamplerDegree]⟩⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  have hpair := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  exact congrArg Prod.fst hpair

theorem preparedModularGeneralDetector_blocks {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (a : LayerSamplerAxis I n) :
    (Fintype.card (B a) : ℝ) ≤ 2 * D :=
  (Nat.cast_le.mpr (preparedModularGeneralDetector_block_card (G := G) B a)).trans
    (preparedModularGeneralDetector_variable_count B rowSets hdim)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_grid_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hdim.axes

theorem preparedModularGeneralDetector_grid_slot_cap {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P) :
    let Qgrid := Real.toNNReal (8 * (D + 1))
    (∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Qgrid : ℝ)) ∧ (Qgrid : ℝ) ≤ Real.exp (P + 8) := by
  have hnonneg : 0 ≤ 8 * (D + 1) := by linarith [hdim.nonneg]
  dsimp only
  rw [Real.coe_toNNReal _ hnonneg]
  constructor
  · intro a
    have hc := (Nat.cast_le.mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2))).trans
      (hdim.coefficients (allocatedGridIntegerAxis B U b S a).1)
    linarith
  · have hP := hdim.nonneg.trans hDP
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P :=
        mul_le_mul h8 (Real.add_one_le_exp P) (by linarith) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem preparedModularGeneralDetector_ambient_count {P : ℝ}
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hJ j)
    _ = _ := by simp

theorem preparedModularGeneralDetector_chart_sum (C : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) :
    ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, Real.exp P * P := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (hC j) (hJ j) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (m : ℝ) * (Real.exp P * P) := by simp
    _ ≤ Real.exp P * (Real.exp P * Real.exp P) := mul_le_mul hmexp
      (mul_le_mul_of_nonneg_left hPexp (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem preparedModularDetector_scalar_resource_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    0 ≤ r.v ∧ 0 ≤ r.w ∧ 0 ≤ r.Dg ∧ 0 ≤ r.Pbox ∧
      0 ≤ r.Vlog ∧ 0 ≤ r.Nlog ∧ 0 ≤ r.Banalytic ∧ 0 ≤ r.baseAmbient ∧
      P ≤ r.v ∧ P + 1 ≤ r.w ∧ 2 * P ≤ r.Dg ∧ K.m * P ≤ r.Dg ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) ≤ r.Dg ∧ 1 ≤ r.Dg ∧
      r.Dg ≤ r.Banalytic ∧ 4 * P ≤ r.Banalytic ∧ P + 8 ≤ r.Banalytic ∧
      P ≤ r.baseAmbient ∧ 3 * P ≤ r.baseAmbient ∧ 2 * P ≤ r.baseAmbient ∧
      r.Vlog ≤ r.baseAmbient ∧ r.Nlog ≤ r.baseAmbient ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P ≤ r.baseAmbient ∧ 2 ≤ r.baseAmbient := by
  intro r
  have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ K.m := Nat.cast_nonneg _
  have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hmP : (0 : ℝ) ≤ K.m * P := mul_nonneg hm hP
  have hdegP : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P := mul_nonneg hdeg hP
  have hv : r.v = P + 8 := rfl
  have hw : r.w = P + 1 := rfl
  have hbox : r.Pbox = 2 * P + 8 := rfl
  have hd : r.Dg = 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) +
      K.m + comparisonProfileBound + 8 := rfl
  have hba : r.Banalytic = r.Dg + 4 * P + 32 := rfl
  have ha : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32 := rfl
  have hproj : 0 ≤ r.Pproj := by change 0 ≤ 4 * (P + 8)^2; positivity
  have hcover : 0 ≤ r.coverLog := by
    change 0 ≤ (r.Pproj + 3 + K.Acover)^K.Acover
    positivity
  have hq : 0 ≤ r.Q := by change 0 ≤ (P + K.Cperiod)^K.Cperiod; positivity
  have hvl : 0 ≤ r.Vlog := by
    change 0 ≤ P^2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
    positivity
  have hnl : 0 ≤ r.Nlog := by
    change 0 ≤ (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
    positivity
  have hd0 : 0 ≤ r.Dg := by linarith only [hd, hP, hmP, hdeg, hm, hprof]
  have hba0 : 0 ≤ r.Banalytic := by linarith only [hba, hd0, hP]
  have ha0 : 0 ≤ r.baseAmbient := by
    linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]
  refine ⟨by linarith only [hv, hP], by linarith only [hw, hP], hd0,
    by linarith only [hbox, hP], hvl, hnl, hba0, ha0, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hv]
  · exact hw.ge
  · linarith only [hd, hmP, hdeg, hm, hprof]
  · linarith only [hd, hP, hdeg, hm, hprof]
  · linarith only [hd, hP, hmP, hm, hprof]
  · linarith only [hd, hP, hmP, hdeg, hm, hprof]
  · linarith only [hba, hP]
  · linarith only [hba, hd0]
  · linarith only [hba, hd0, hP]
  all_goals linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularGeneralDetector_early_analytic_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P D pDetect : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hRone : ∀ j, R j ≤ 1) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hvolumeRatio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) (hDetect : pDetect ≤ P) :
    PreparedModularGeneralEarlyAnalyticBounds B rowSets U b S Cforward Ksource
      (preparedModularCanonicalDetectorResources K P) P D pDetect := by
  let r := preparedModularCanonicalDetectorResources K P
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  obtain ⟨hv0, hw0, hdg0, hbox0, hvol0, hnorm0, hba0, hbase0,
    hPv, hPw, h2PDg, hmPDg, htailDg, h1Dg, hDgBa, h4PBa, h8PBa,
    hPBase, h3PBase, h2PBase, hVBase, hNBase, htailBase, h2Base⟩ :=
      preparedModularDetector_scalar_resource_bounds K hP
  have hPDg : P ≤ r.Dg := (by linarith only [hP] : P ≤ 2 * P).trans h2PDg
  have hDDg : D ≤ r.Dg := hDP.trans hPDg
  have hPexp : P ≤ Real.exp P := by linarith only [Real.add_one_le_exp P]
  have hExpv : Real.exp P ≤ Real.exp r.v := Real.exp_le_exp.mpr hPv
  have hExpBa : Real.exp P ≤ Real.exp r.Banalytic :=
    Real.exp_le_exp.mpr ((by linarith only [hP] : P ≤ 4 * P).trans h4PBa)
  obtain ⟨hSlots, hSlotsExp⟩ := preparedModularGeneralDetector_grid_slot_cap B rowSets U b S hdim hDP
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B rowSets hdim
  have hCoords := preparedModularGeneralDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward
  have hCoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp r.Banalytic := by
    rw [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) :=
        mul_le_mul hK hCoords (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (4 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h4PBa
  refine {
    hQgrid := hSlots
    hDg := hdg0
    hvg := hv0
    hwg := hw0
    hcube := hdim.cube.trans hDDg
    hdegree := fun j => (hdim.layer_degree B j).trans hDDg
    hrowsD := ?_
    htail := ?_
    hblocks := fun a => (preparedModularGeneralDetector_blocks B rowSets hdim a).trans (by linarith only [hDP, h2PDg])
    hRv := fun j => (hRone j).trans (Real.one_le_exp hv0)
    hRiGrid := fun j => (hRi j).trans hExpv
    hδw := by linarith only [hDetect, hPw]
    hcoeff := fun j => (hdim.coefficients j).trans (hDP.trans (hPexp.trans hExpv))
    haxesGrid := (preparedModularGeneralDetector_grid_axes B rowSets U b S hdim).trans hDDg
    hfullAxes := hdim.axes.trans hDDg
    hfullOutputs := hdim.outputs.trans hDDg
    hambientCount := ?_
    hprofileBudget := hdim.profile.trans hDDg
    hBanalytic := hba0
    hDanalytic := hDgBa
    hcutoffAnalytic := hcutoff.trans hExpBa
    hcoordAnalytic := hCoordAnalytic
    hgridAnalytic := hSlotsExp.trans (Real.exp_le_exp.mpr h8PBa)
    hI := fun j => (hI j).trans hDP
    hn := fun j => (hn j).trans hDP
    hcoeffEarly := fun j => (hdim.coefficients j).trans hDP
    hRiEarly := hRi
    hVEarly := fun j => (hvolumeRatio j).trans (hV j) }
  · intro j
    simpa only [Fintype.card_coe] using (hdim.rows j).trans hDDg
  · simpa only [hm] using htailDg
  · apply (preparedModularGeneralDetector_ambient_count hJ).trans
    simpa only [hm] using hmPDg

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U b o hb bW

theorem preparedModularGeneralDetector_period_prefactor {P D Pk Qstride pDetect Pnum : ℝ} {nX : ℕ}
    (hP : 0 ≤ P)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hDP : D ≤ P) (hnX : (nX : ℝ) ≤ P) (hPk : Pk ∈ Set.Icc 0 P)
    (hQstride : Qstride ∈ Set.Icc 0 P) (hp : pDetect ∈ Set.Icc 0 P)
    (hPnum : Pnum ∈ Set.Icc 0 P) :
    let r := preparedModularCanonicalDetectorResources (preparedModularGeneralDetectorConstants m s) P
    let O := fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let qlog := L + nX * Qstride
    let maskLog := (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) + maskLog
    P ≤ r.Q ∧ L ∈ Set.Icc 0 r.Q ∧ qlog ∈ Set.Icc 0 r.Q ∧
      maskLog ∈ Set.Icc 0 r.Q ∧ labelLog ∈ Set.Icc 0 r.Q ∧ Fmodel ∈ Set.Icc 0 r.Fpref := by
  intro r O L qlog maskLog labelLog Fmodel
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    ((allocatedProfile_dimensions U b o B hdim hb bW).2 j).trans hDP
  have hn := (preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hdim).2
  have haxes := hdim.axes.trans hDP
  let Cgrid := (preparedModularGeneralDetectorConstants m s).Cgrid
  obtain ⟨hPQ, hL, hq, _, hmask, hlabel, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_period_budget.{0,0} m (s + 1) Cgrid)).2
      (A := LayerSamplerAxis I n) (nX := nX) n Q hP hnX hPk hQstride hp haxes (fun j => (hn j).trans hDP) hQ
  have hF := (Classical.choose_spec (exists_canonicalSlicedModelPrefactor_budget.{0,0} m (s + 1))).2
    (I := I) (n := n) (Q := Q) hP hPnum hPk haxes hQ
  refine ⟨hPQ, hL, hq, hmask, hlabel, ?_⟩
  change 0 ≤ Fmodel ∧ Fmodel ≤ _
  have heq : Fmodel = (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L) := by
    dsimp only [Fmodel, maskLog]
    ring
  rw [heq]
  exact hF

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDirectDetectionLateFloor
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedModularGeneralDirectDetectionThreshold_parameters
    {u pModel α : ℝ} (count : ℕ)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α)
    (hαone : α ≤ 1) :
    let pDetect := allocatedModelTestLog u pModel
    0 ≤ pDetect ∧ 0 < α ∧ α ≤ 1 ∧
      count * Real.exp (-pDetect) ≤ α / 8 ∧ Real.exp (-pDetect) ≤ α / 4 := by
  have hα : 0 < α := (Real.exp_pos _).trans_le hαlower
  have h8 : (8 : ℝ) ≤ Real.exp 5 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have h3 := Real.add_one_le_exp (3 : ℝ)
    rw [show (5 : ℝ) = 2 + 3 by norm_num, Real.exp_add]
    nlinarith
  have hsmall : Real.exp (-(2 * u + 4 * pModel + 12)) ≤ α / 8 := by
    calc
      _ = Real.exp (-(2 * u + 4 * pModel + 7)) / Real.exp 5 := by
        rw [← Real.exp_sub]
        congr 1
        ring
      _ ≤ Real.exp (-(2 * u + 4 * pModel + 7)) / 8 :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h8
      _ ≤ α / 8 := div_le_div_of_nonneg_right hαlower (by norm_num)
  have htest : Real.exp (-allocatedModelTestLog u pModel) ≤
      Real.exp (-(2 * u + 4 * pModel + 12)) := by
    apply Real.exp_le_exp.mpr
    unfold allocatedModelTestLog
    linarith
  refine ⟨by unfold allocatedModelTestLog; positivity, hα, hαone, ?_, ?_⟩
  · calc
      _ ≤ Real.exp pModel * Real.exp (-allocatedModelTestLog u pModel) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
      _ = Real.exp (-(2 * u + 4 * pModel + 12)) := by
        rw [← Real.exp_add]
        congr 1
        unfold allocatedModelTestLog
        ring
      _ ≤ α / 8 := hsmall
  · linarith [htest.trans hsmall]

theorem preparedModularGeneralDirectDetectionThreshold_slice_le
    {u pModel pSlice : ℝ} (hu : 0 ≤ u) (hpModel : 0 ≤ pModel)
    (hslice : pSlice ≤ pModel) : pSlice ≤ allocatedModelTestLog u pModel := by
  unfold allocatedModelTestLog
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedModularGeneralDirectDetectionFreeTrim
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
variable (α : ℝ)
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

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ in

theorem preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2_oai (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K)
    {Pmaster Plate : ℝ} (hLate : Pmaster ≤ Plate) (hMaster : 0 ≤ Pmaster) (hDMaster : D ≤ Pmaster)
    (hPkMaster : Pk ∈ Set.Icc 0 Pmaster) (hQstrideMaster : Qstride ∈ Set.Icc 0 Pmaster)
    (hDetectMaster : pDetect ∈ Set.Icc 0 Pmaster) (hnXMaster : (nX : ℝ) ≤ Pmaster)
    (hRone : ∀ j, R j ≤ 1)
    (hRiMaster : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hKMaster : (K : ℝ) ≤ Real.exp Pmaster)
    (hcutoffMaster : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pmaster)
    (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForwardMaster : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pmaster)
    (hVtailMaster : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pmaster)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let Pbox := r.Pbox
    let Vlog := r.Vlog
    let Nlog := r.Nlog
    let Mlog := r.Q
    let baseAmbient := r.baseAmbient
    let _Qgrid := Real.toNNReal (8 * (D + 1))
    let Ag := canonicalTransitionLip
    let Dg := r.Dg
    let vg := r.v
    let wg := r.w
    let Banalytic := r.Banalytic
    let Pnum := Pmaster
    ∀ {Pproj coarseTarget Ecoarse pGain : ℝ},
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn),
    ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
,
    ∀ {lossTarget Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → (hτSpatial : 0 < τ) →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (_hPhysicalNonneg : 0 ≤ Pphysical) → (_hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (_hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (_hCoarseNonneg : 0 ≤ coarseTarget) →
    (_hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (_hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (_hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)
    let Qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let tg := ((s + 1 : ℕ) : ℝ) + Qlog + (pDetect + 1) + 1
    let pg := (Cgrid : ℝ) + (((s + 1) + 1 : ℕ) : ℝ) * Qlog + (pDetect + 1) + 4
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2 →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,max 0 0 0} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vtail j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    ∀ (hbases : bases.Nonempty),
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let Cbudget := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + Cbudget) ^ Cbudget
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    0 ≤ u → 0 ≤ pModel → pSlice ≤ pModel →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pModel →
    Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α → α ≤ 1 →
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖ := by
  intro r Pbox Vlog Nlog Mlog baseAmbient Qgrid Ag Dg vg wg Banalytic Pnum
  have hd := geometry.hdimensions
  have hJ := (allocatedProfile_dimensions U basis o B hd hb bW).1
  have late := preparedModularGeneralDetector_late_ambient_bounds_s2 B rowSets U basis S
    Cforward K (preparedModularGeneralDetectorConstants m s) rfl hLate hd hDMaster
    hR hRone hRiMaster hSLate (fun j => (hJ j).trans hDMaster)
    (fun j => (hVactual j).2.trans (hVtailMaster j)) hForwardMaster hKMaster hcutoffMaster
  have early := preparedModularGeneralDetector_early_analytic_bounds B rowSets U basis S
    Vtail Cforward K (preparedModularGeneralDetectorConstants m s) rfl hd hDMaster
    hRone hRiMaster (fun j => (hJ j).trans hDMaster) hVtailMaster
    (fun j => (hVactual j).2) hForwardMaster hKMaster hcutoffMaster hDetectMaster.2
  obtain ⟨_, hperiod, _, hmask, hlabel, _⟩ :=
    preparedModularGeneralDetector_period_prefactor B U basis o hb bW hMaster hd hDMaster
      hnXMaster hPkMaster hQstrideMaster hDetectMaster ⟨hMaster, le_rfl⟩
  have hQbase : r.Q ≤ r.baseAmbient := by
    have hr := ((Classical.choose_spec (exists_preparedModularGeneralDetector_resource_budget
      (preparedModularGeneralDetectorConstants m s) (s + 1))).2 hMaster hLate).1
    have hm : 0 ≤ ((layerTailDegree m + 1 : ℕ) : ℝ) * Plate :=
      mul_nonneg (Nat.cast_nonneg _) (hMaster.trans hLate)
    change r.Q ≤ r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree m + 1 : ℕ) * Plate + 3 * Pmaster + comparisonProfileBound + (2 ^ (s + 1) : ℕ) + 32
    linarith only [hr.Pproj.1, hr.coverLog.1, hr.Vlog.1, hr.Nlog.1, hm, hMaster,
      Nat.cast_nonneg («α» := ℝ) comparisonProfileBound, Nat.cast_nonneg («α» := ℝ) (2 ^ (s + 1))]
  have hNative := allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) («pDetect» := pDetect) («qDetect» := qDetect) («α» := α)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    hsm Pchart D target Pk Prho Qstride K geometry
  intro Pproj coarseTarget Ecoarse pGain ambientQ ambientBudget τ Pphysical W ξn hξn hξn_le hW
  have hnative := hNative (ξn := ξn) (τ := τ) (Pphysical := Pphysical)
    (Pproj := Pproj) (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
    hMkP hMkPk hQstrideMaster.1 hstride hstrideBound C hC hCbound hchart Cforward hforward
    late.hPbox late.hVlog late.hNlog (hmask.1.trans hmask.2) late.hbox late.hvolume
    late.hnormalizer hmask.2 late.hbaseAmbient late.hvbase late.hnbase hQbase
    late.hsites late.haxes (hlabel.2.trans hQbase) late.hKbase late.hcoords
    late.hcutoff (hperiod.2.trans hQbase) late.hrowsAmbient late.houtputs late.hheight
    Qgrid early.hQgrid Ag canonicalTransitionLip_spec hBa hBi
    early.hDg early.hvg early.hwg early.hcube early.hdegree early.hrowsD early.htail
    (fun j i => early.hblocks ⟨j, Sum.inr i⟩) early.hRv early.hRiGrid early.hδw early.hcoeff
    early.haxesGrid early.hfullAxes early.hfullOutputs early.hambientCount early.hprofileBudget
    early.hBanalytic early.hDanalytic early.hcutoffAnalytic early.hcoordAnalytic early.hgridAnalytic
    hMaster early.hI early.hn early.hcoeffEarly early.hRiEarly early.hVEarly

  intro cells poly hp hmem lossTarget Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel Cgrid Qlog tg pg p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj
    Pside hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hmass htotal Path pathLaw
    sides Sites e Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices hdenseSlice hdimensionDetect hcomplexity hcap hGdetect hkernel
    Cbudget Bbudget Anorm Anative Abudget budget hu hpModel hpSliceModel hcountModel
    hαlower hαone signal hsignal hzero hdetected
  obtain ⟨hpDetect, hα, _, hmeshDetect, hthreshold⟩ :=
    preparedModularGeneralDirectDetectionThreshold_parameters
      (Fintype.card (LayerSamplerVariables G I n B)) hu hpModel hcountModel hαlower hαone
  have hpSliceDetect := preparedModularGeneralDirectDetectionThreshold_slice_le hu hpModel hpSliceModel
  have hdenseDetect z j := (hdenseSlice z j).mono_parameter hpSliceDetect
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  have hnative := hnative (Pnative := Pnative) hξn hξn_le cells poly hp hmem signal
    (fun t _ => hsignal t) hzero
    (lossTarget := lossTarget) (Psample := Psample) (Rrank := Rrank)
    (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision
  have hnative := hnative (Pside := Pside)
    hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vtail hcoverAmbient hcoverSample hmassSample hCactual hVactual
    hXmass hframeMass hstrideMass hτMass hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj
    hProfileProj hCproj hVproj hXproj hFrameProj hStrideProj hτProj hξProj hSizeProj hRankProj
  exact hnative hProjSide hCapSide hpSide htargetSide hside hCells _ hbases
    hmass htotal e Subtype.val_injective Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstepdetect hslices hpDetect hpDetect hdenseDetect hdimensionDetect hcomplexity hcap
    hα hαone hmeshDetect hthreshold hdetected hGdetect hkernel

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDirectDetectionAmbient_sharedWidth_s2_oai
