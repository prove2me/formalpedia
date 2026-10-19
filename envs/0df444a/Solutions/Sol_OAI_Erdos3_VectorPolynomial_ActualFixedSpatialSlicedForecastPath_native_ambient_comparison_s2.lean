-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:11:46.750456+00:00
-- url     : https://prove2.me/submissions/5ad9d212-fcc3-4b6c-940a-988f1d1a44bd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_stepInputLaw_sample_characteristic_decay_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_native_ambient_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem modularForecastRankConstant_dimension (s D d : ℕ) (hd : d ≤ D) :
    ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) := by
  rw [modularForecastRankConstant_decay]
  exact_mod_cast Nat.add_le_add_right hd 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointFrameCoefficientCoverSample
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

theorem affineCoefficientCoverSample_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) (q : ℕ) :
    affineCoefficientCoverSample U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      q (fun k v => (z (k,v) : ℝ)) =
    affineCoefficientCoverSample U p hm q
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  unfold affineCoefficientCoverSample
  rw [affineSampleCoefficientArray_joint_frame]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

omit [∀ j, Fintype (I j)] in

theorem allocatedCongruenceForecastRankConstant_dimension
    (hm : 0 < m) (D : ℕ)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D) :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) := by
  apply modularForecastRankConstant_dimension
  rw [Fintype.card_sigma]
  exact (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans hD

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedRecoveredForecastDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable [∀ j, Fintype (J j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedRecoveredForecastPolynomial_eq
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise) (sample : Sample)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d) :
    allocatedForecastPolynomial short base noise (allocatedReadDeck read)
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) =
    allocatedForecastPolynomial short base (allocatedReadNoise read) (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j,a.val⟩) := by
  rw [hnoise]
  funext output
  rcases output with ⟨j, a | a | a⟩
  · rfl
  · rfl
  · have hi : (sample j).2 a.val = allocatedReadProjection read ⟨j, Sum.inr a.val⟩ :=
      (funext (hinteger j a.val)).symm
    simp only [allocatedForecastPolynomial, allocatedSeparatedCongruencePolynomial,
      allocatedUnconditionedCongruenceIntegerPolynomial, allocatedOriginalSampleCongruenceProjection,
      allocatedCongruenceIntegerEmbedding]
    change MvPolynomial.rename _ (modularBoundedCoefficientPolynomial (j.val + 1)
      ((sample j).2 a.val)) = MvPolynomial.rename _
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (allocatedReadProjection read ⟨j, Sum.inr a.val⟩))
    rw [hi]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_read
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReplaceReadNoise B z (allocatedJointFrameRead a (read z)) = read z := by
  funext i
  rcases i with i | i
  · exact (congrFun (h z).1 i).symm
  · rfl

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_cover
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0)
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop) :
    coefficientDeckChartEvent U bW b hb o q event
      (affineCoefficientCoverSample U (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) q
        (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues
        (fun i => (allocatedReplaceReadNoise B z
          (allocatedJointFrameRead a (read z)) i : ZMod q))) := by
  have hs := ((h z).2 hz).2.2.2.2.1 q (NeZero.pos q) event
  rw [h.centeredJointFrame_read B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z]
  change coefficientDeckChartEvent U bW b hb o q event
    (affineCoefficientCoverSample U
      (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ))
        (subtractConstant (c j).val (poly j))
        (coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))) q
      (fun k x => (z (k,x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q))) at hs
  rw [affineCoefficientCoverSample_joint_frame] at hs
  exact hs

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_recovery
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0) :
    allocatedReadNoise (allocatedReplaceReadNoise B z
      (allocatedJointFrameRead a (read z))) = z ∧
    canonicalCoefficientSample U b hb o (sample z) =
      affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
        (fun k x => (jointIntegerFrame (a,z) k x : ℝ)) ∧
    (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
      mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
        (sample z j)) ∧
    (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
    (∀ (j : Fin m) (i : Fin (n j))
      (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection (allocatedReplaceReadNoise B z
        (allocatedJointFrameRead a (read z))) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
    (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U (fun j => subtractConstant (c j).val (poly j))
            (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) q
            (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues
            (fun i => (allocatedReplaceReadNoise B z
              (allocatedJointFrameRead a (read z)) i : ZMod q)))) := by
  have hs := (h.jointFrame B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z).2.2.2 hz
  refine ⟨rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  exact h.centeredJointFrame_cover B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z hz q

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedAnalyticIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}

omit [Fintype Tsp] in
theorem activeLower_eq (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    slice.path.lower a p = (slice.principalStart ⟨a.val,p⟩ : ℝ) / S.value := by
  rw [slice.lower_eq a p, activeSide (B := B) (U := U) (b := b) (S := S) a p]

omit [Fintype Tsp] in
theorem activeWidth_eq (hδ : 0 < δslice)
    (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    slice.path.width a p = (slice.step : ℝ) * ((slice.principalLength ⟨a.val,p⟩ : ℝ) - 1) /
      S.value := by
  have hlen : 1 ≤ slice.principalLength ⟨a.val,p⟩ :=
    le_trans (by decide : 1 ≤ 2) (slice.activeLength_two hδ a p)
  rw [slice.width_eq a p, slice.principalStep_active a p, activeSide (B := B) (U := U) (b := b) (S := S) a p,
    Nat.cast_sub hlen, Nat.cast_one]

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedCRTIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.slicedReferenceModulusNeZero
omit [Fintype Tsp] in
theorem referenceInputLaw_eq_step : slice.path.referenceInputLaw = slice.stepInputLaw := by
  have hp : (fun p : slice.path.primes => slice.path.prescribed p.val) =
      (fun p : slice.path.primes => padicValNat p.val slice.step) :=
    funext fun p => slice.prescribed_eq p.val
  have ho : slice.path.origin = (fun (p : slice.path.primes)
      (v : LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B) => ((Sum.elim slice.kernelStart
      (fun a => slice.principalStart ⟨a.1.val,a.2⟩) v : ℤ) :
        ZMod (p.val ^ slice.path.exponent p.val))) :=
    funext fun p => funext fun v => slice.origin_eq p v
  simp only [ActualFixedSpatialForecastPath.referenceInputLaw, stepInputLaw, hp, ho]
  congr 1

omit [Fintype Tsp] in
theorem referencePolynomial_eq_sample : slice.path.referencePolynomial =
    allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
      (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample) := by
  have h := allocatedRecoveredForecastPolynomial_eq B U b S slice.path.base slice.path.noise
    slice.path.read slice.path.readNoise slice.path.sample slice.path.readProjection
  rw [slice.path.readNoise] at h
  exact h.symm

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityIdentification
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

theorem density_eq_allocatedSlicedPhysicalForecastDensity
    (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδ : 0 < δslice) (ξ : ℝ) :
    slice.density hB = allocatedSlicedPhysicalForecastDensity B U b S τ ξ physicalN
      slice.path.noise slice.kernelLength slice.kernelLength_two slice.kernelStart slice.step
      slice.step_pos spatialEquiv (slice.analyticKernelDetFalse ξ) (slice.analyticKernelDetTrue ξ)
      hB slice.path.sample
      (fun j => slice.principalLength ⟨j.1.val,j.2⟩)
      (fun j => slice.principalStart ⟨j.1.val,j.2⟩) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have hl : slice.path.lower = fun a p => (slice.principalStart ⟨a.val,p⟩ : ℝ) / S.value :=
    funext (fun a => funext (slice.activeLower_eq a))
  have hw : slice.path.width = fun a p =>
      (slice.step : ℝ) * ((slice.principalLength ⟨a.val,p⟩ : ℝ) - 1) / S.value :=
    funext (fun a => funext (slice.activeWidth_eq hδ a))
  unfold density allocatedSlicedPhysicalForecastDensity
  dsimp only
  simp only [hl, hw]
  congr 1
  exact slice.normalizedNoise_eq_kernelFrame ξ

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}

omit [Fintype Tsp] in

theorem centered_recovery
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem
      (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
      center path.center path.base sampleFn readFn)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0)
    (hsample : sampleFn path.noise = path.sample)
    (hread : readFn path.noise = path.read) :
    canonicalCoefficientSample U b hb o path.sample =
      affineSampleCoefficientTorus U (path.physicalPolynomial originalpoly)
        (path.physicalPolynomial_mem originalpoly hmem)
        (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ)) ∧
    (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (path.sample j) ∧
      mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
        (path.sample j)) ∧
    (∀ d, |coefficientSamplerAmbientPoint U b o path.sample d| < 1 / 2) ∧
    (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n Eout q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U (path.physicalPolynomial originalpoly)
            (path.physicalPolynomial_mem originalpoly hmem) q
            (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (path.read i : ZMod q)))) := by
  have hr := h.centeredJointFrame_recovery B U bW b hb o S hR hσ originalpoly hmem
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block C path.noise hz
  rw [h.centeredJointFrame_read B U bW b hb o S hR hσ originalpoly hmem
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block C path.noise,
    hsample, hread] at hr
  exact ⟨hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2⟩

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod τ δslice}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
include s in

theorem modular_decay_dimension :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) := by
  exact allocatedCongruenceForecastRankConstant_dimension
    (allocatedShortAxis (I := I) U b S.value) s.hm Dmod s.hDmod

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}
local notation "selected" => allocatedShortIntegerSelection U b S.value
local notation "Original" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.actualComparisonReferenceNeZero
variable (gridVolume : ℝ) (hVpos : 0 < gridVolume)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ)
local notation "referenceTarget" => forecastLawDensityPhysicalTarget B U b S slice.principalLaw
  (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple
  (fun _ : Original => slice.path.referenceInputLaw)
  (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
    (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
  slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hp : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ) *
    forecastLawDensityPhysicalTarget B U b S slice.principalLaw (slice.density s.hBactive)
      (allocatedShortIntegerSelection U b S.value) slice.path.sample slice.path.commonTuple
      (fun _ : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S) =>
        slice.path.referenceInputLaw)
      (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
        (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
      slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW poly hp u -
    ∑ i, nativeCoeff i * (F i).eval physicalN poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hPP : s.P ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)

variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail hVpos ν hlattice hcompact
  hmargin htrimbase happrox hPambient hEprec hPP hLip hcoverF hmodF hmass hlarge
  hRrank hrank hcutoff hδgrid hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt in

theorem native_ambient_comparison_s2_oai :
    ‖slice.nativeMean s W originalpoly -
      (𝔼 u ∈ integerBox physicalN,
        W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
          (κ * referenceTarget (slice.path.physicalPolynomial originalpoly)
            (slice.path.physicalPolynomial_mem originalpoly hmem) u))‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := δnative) (M := M) (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  let := slice.path.primeNeZero
  have hr := slice.path.centered_recovery bW hb o originalpoly hmem C
    hglobal hz hsampleAt hreadAt
  have hframeEq : (fun k x => (jointIntegerFrame (slice.path.base, slice.path.noise) k x : ℝ)) =
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B)
        slice.path.base + slice.path.noise) (k,x) : ℝ)) := by
    funext k x
    cases k <;> simp [jointIntegerFrame, integerBaseTranslation, baseArrayJoin]
  rw [hframeEq] at hr
  have hphysicalDegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1)
      (slice.path.physicalPolynomial originalpoly j) :=
    fun j => (hdegree j).subtractConstant _
  have hphysicalRank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (physicalN i : ℝ)) Rrank (U j)
      (slice.path.physicalPolynomial originalpoly j) := by
    intro j
    exact (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
      _ _ _ _ _).mpr (hrank j)
  have hnonempty : ∀ a : Active, Nonempty (B a.val) := fun a =>
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 4) (s.hBactive a))
  let bActive : ∀ a : Active, B a.val := fun a => Classical.choice (hnonempty a)
  have hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient := by
    simpa only [Fintype.card_sigma] using s.hdim.trans (s.hDP.trans hPP)
  have hPdecay := s.modular_decay_dimension
  have hdecay := slice.stepInputLaw_sample_characteristic_decay_s2 s.hm
  have happrox' := happrox
  rw [slice.density_eq_allocatedSlicedPhysicalForecastDensity s.hBactive s.hδslice ξ,
    slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample] at happrox'
  dsimp only [nativeMean, comparisonError]
  rw [slice.density_eq_allocatedSlicedPhysicalForecastDensity s.hBactive s.hδslice ξ,
    slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample]
  dsimp only [principalLaw, stepInputLaw] at happrox' hdecay ⊢
  exact allocatedFixedPath_sliced_native_ambient_comparison_s2
    (B := B) (U := U) (basis := b) (hR := hR) (hσ := hσ) (S := S)
    (primes := fun p : slice.path.primes => p.val)
    (exponent := fun p : slice.path.primes => slice.path.exponent p.val)
    (HP := slice.principalLength) (stepP := slice.principalStep)
    (cP := slice.principalStart) (hinsideP := slice.principalInside)
    (hHP := slice.principalLength_pos) (τ := τ) (ξ := ξ) (hτ := s.hτ) (hξ := hξ)
    (box := physicalN) (hbox := hbox) (integerFrame := slice.path.noise) (hframe := hframe)
    (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
    (stepG := slice.step) (hstepG := slice.step_pos) (hcontainedG := slice.kernelSupport)
    (e := spatialEquiv) (h0 := slice.analyticKernelDetFalse ξ)
    (h1 := slice.analyticKernelDetTrue ξ) (hB := s.hBactive)
    (sample := slice.path.sample) (hs := slice.path.hs) (ht := ht) (hσbound := hσbound)
    (H := fun j => slice.principalLength ⟨j.1.val,j.2⟩)
    (c := fun j => slice.principalStart ⟨j.1.val,j.2⟩)
    (hH := fun j => slice.activeLength_two s.hδslice j.1 j.2)
    (hδ := hδ) (hsubset := fun j => slice.activeSupport j.1 j.2)
    (hdense := fun j => hdense j.1 j.2) (q := q) (hsizeG := hsizeG) (hsmallG := hsmallG)
    (hsize := fun j => hsize j.1 j.2) (hsmall := fun j => hsmall j.1 j.2)
    (hε := hε) (hmesh := fun _ => hmesh) (hδone := hδone)
    (b := bActive) (hη := hη) (A := s.L) (hA := s.hL) (htail := htail)
    (hb := hb) (o := o) (bW := bW) (W := W) (hm := s.hm)
    (hperiod := hperiod) (hcover := hcover) (xref := slice.path.commonTuple)
    (base := slice.path.base) (read := slice.path.read)
    (hp := fun p => slice.path.prime p.val p.property)
    (hcoprime := primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective)
    (hqN := hqN) (hV := hVpos.ne')
    (nativePoly := slice.path.physicalPolynomial originalpoly)
    (hmem := slice.path.physicalPolynomial_mem originalpoly hmem)
    (hdegree := hphysicalDegree) (hbase := hr.1) (hsmallChart := hr.2.2.1)
    (hread := hr.2.2.2 W.cover W.cover_pos)
    (ν := ν) (hσ1 := s.hσ1) (radius := s.radius)
    (hradius0 := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) s.hr3)
    (hradius3 := s.hr3) (hradius := s.hradius)
    (chartCap := s.inverse) (hchartCap := s.hinverse) (hchart := s.hchart)
    (hchartBudget := s.hbudget) (hmargin := hmargin) (htrimbase := htrimbase)
    (hVpos := hVpos) (F := F) (nativeCoeff := nativeCoeff) (δnative := δnative)
    (happrox := happrox') (hPambient := hPambient) (hEprec := hEprec)
    (hX := s.hX.trans hPP) (hdim := hdim) (hLip := hLip) (hcoverF := hcoverF)
    (hmodF := hmodF) (hmass := hmass) (hlarge := hlarge) (hRrank := hRrank)
    (hrank := hphysicalRank) (cutoff := cutoff) (hcutoff := hcutoff)
    (D := slice.decayConstant) (hD := Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (hPdecay := hPdecay) (hdecay := hdecay) (hδgrid := hδgrid)
    (hδgrid1 := hδgrid1) (hgridmesh := hgridmesh)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison_s2_oai
