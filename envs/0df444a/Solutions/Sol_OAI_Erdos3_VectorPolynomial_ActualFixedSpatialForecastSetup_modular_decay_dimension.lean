-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.modular_decay_dimension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:10.892415+00:00
-- url     : https://prove2.me/submissions/3247f5ba-3fcd-4445-adb9-529093b783ea

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1330

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

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

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

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

end Erdos3.VectorPolynomial

end

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end VectorPolynomial
end Erdos3

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

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialSlicedForecastPath

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod τ δslice}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
include s in

theorem modular_decay_dimension_oai :
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

variable (gridVolume : ℝ) (hVpos : 0 < gridVolume)

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










variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hPP : s.P ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
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

end ActualFixedSpatialSlicedForecastPath
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

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Eprec Rrank : ℝ} (hEprec : 0 ≤ Eprec)
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

variable (hfinite : (integerBox physicalN).Nonempty)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.modular_decay_dimension_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.modular_decay_dimension_oai
